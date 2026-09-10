import { execFile } from "node:child_process";
import { existsSync } from "node:fs";
import { readFile, realpath } from "node:fs/promises";
import { promisify } from "node:util";
import { dirname, isAbsolute, join, relative, resolve, sep } from "node:path";
import { leanNameLeaf, maskLeanCommandQuotations } from "./lean_decl_name.js";
import { extractDeclSnippet, parseSourceDecls } from "./lean_extract.js";

export interface ResolvedLeanDeclaration {
  /** Canonical path relative to the common workspace root (never `..`). */
  file: string;
  decl: string;
  line: number;
  snippet: string;
  relocated: boolean;
  resolution: "crosswalk" | "library-index" | "export-import" | "run-name-search";
}

const leafOf = leanNameLeaf;
const within = (root: string, target: string) => target === root || !relative(root, target).startsWith(`..${sep}`) && relative(root, target) !== ".." && !isAbsolute(relative(root, target));

/** The pinned Mathlib checkout: the package's own `.lake` when it has been built, else the
 *  workspace root's (a fresh clone that has only run `lake exe cache get && lake build` at
 *  the root has no `CausalSmith/.lake` yet, and the presentation tests must not depend on it). */
function mathlibCheckout(packageRoot: string, workspaceRoot: string): string {
  const own = join(packageRoot, ".lake", "packages", "mathlib");
  return existsSync(join(own, "Mathlib")) ? own : join(workspaceRoot, ".lake", "packages", "mathlib");
}

async function rootsFor(repoRoot: string): Promise<{ packageRoot: string; workspaceRoot: string; runRoot: string }> {
  const packageRoot = await realpath(repoRoot);
  const parent = await realpath(dirname(packageRoot));
  // PRESENT runs from the CausalSmith package and Causalean is its sibling. Tests may
  // use a one-package fixture; only select the parent when the sibling topology exists.
  let workspaceRoot = packageRoot;
  try {
    await realpath(join(parent, "Causalean"));
    workspaceRoot = parent;
  } catch (e) {
    if ((e as NodeJS.ErrnoException).code !== "ENOENT") throw e;
    /* single-package fixture */
  }
  return { packageRoot, workspaceRoot, runRoot: packageRoot };
}

async function safeRealFile(workspaceRoot: string, candidate: string): Promise<string> {
  const abs = await realpath(candidate);
  if (!within(workspaceRoot, abs)) throw new Error(`P1 declaration path escapes workspace root: ${candidate}`);
  return abs;
}

function canonicalFile(workspaceRoot: string, abs: string): string {
  const rel = relative(workspaceRoot, abs);
  if (!rel || rel === ".." || rel.startsWith(`..${sep}`) || isAbsolute(rel)) {
    throw new Error(`P1 declaration path is not workspace-contained: ${abs}`);
  }
  return rel.split(sep).join("/");
}

const NAME = /^(?:«[^»]+»|[\p{L}_][\p{L}\p{N}\p{M}_']*)(?:\.(?:«[^»]+»|[\p{L}_][\p{L}\p{N}\p{M}_']*))*/u;
const SCOPE_WORDS = new Set(["namespace", "section", "mutual", "end"]);

function namespaceAtOffset(maskedSource: string, offset: number, declaredNamespaces?: Set<string>): string {
  const frames: string[] = [];
  for (const line of maskedSource.slice(0, offset).split(/\r?\n/)) {
    let rest = line.trim().replace(/^noncomputable\s+(?=section\b)/, "");
    for (;;) {
      const command = /^(namespace|section|mutual|end)\b/.exec(rest);
      if (!command) break;
      rest = rest.slice(command[0].length).trimStart();
      const name = NAME.exec(rest)?.[0];
      const named = command[1] !== "mutual" && name && !SCOPE_WORDS.has(name);
      if (named) rest = rest.slice(name.length).trimStart();
      if (command[1] === "end") frames.pop();
      else {
        frames.push(command[1] === "namespace" && named ? name : "");
        if (command[1] === "namespace") declaredNamespaces?.add(frames.filter(Boolean).join("."));
      }
    }
  }
  return frames.filter(Boolean).join(".");
}

const qualify = (namespace: string, name: string): string =>
  name.startsWith("_root_.") ? name.slice(7) : namespace ? `${namespace}.${name}` : name;

function explicitExports(source: string, leaf: string): { aliasFq: string; targetFq: string; enclosing: string; offset: number }[] {
  const masked = maskLeanCommandQuotations(source);
  const out = new Map<string, { aliasFq: string; targetFq: string; enclosing: string; offset: number }>();
  const exportCommand = new RegExp(`^[ \t]*export\\s+(${NAME.source.slice(1)})\\s*\\(([^)]*)\\)`, "gmu");
  const names = new RegExp(NAME.source.slice(1), "gu");
  for (const m of masked.matchAll(exportCommand)) {
    if ([...m[2].matchAll(names)].some(([name]) => name === leaf)) {
      const enclosing = namespaceAtOffset(masked, m.index ?? 0);
      const entry = {
        aliasFq: enclosing ? `${enclosing}.${leaf}` : leaf,
        targetFq: `${m[1]}.${leaf}`,
        enclosing,
        offset: m.index ?? 0,
      };
      out.set(`${entry.aliasFq}\0${entry.targetFq}`, entry);
    }
  }
  return [...out.values()];
}

export function fullyQualifiedSourceDecls(source: string): { name: string; line: number; kind: string }[] {
  const masked = maskLeanCommandQuotations(source);
  const offsets = [0];
  for (let i = 0; i < masked.length; i++) if (masked[i] === "\n") offsets.push(i + 1);
  return parseSourceDecls(source).map((d) => ({ ...d,
    name: qualify(namespaceAtOffset(masked, offsets[d.line - 1]), d.name),
  }));
}

type Candidate = { abs: string; file: string; decl: string; line: number; resolution: ResolvedLeanDeclaration["resolution"] };

const execFileAsync = promisify(execFile);

/** Files in the Mathlib package that declare a top-level `leaf` (by `git grep`, which the
 *  lake checkout supports; an absent package or a grep failure yields no candidates). */
async function mathlibDeclarationFiles(mathlibDir: string, leaf: string): Promise<string[]> {
  if (!existsSync(join(mathlibDir, "Mathlib"))) return [];
  const escaped = leaf.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const pattern = `^(@\\[[^\\]]*\\] *)?(private |protected |noncomputable |nonrec |unsafe )*(theorem|lemma|def|abbrev|structure|class|instance|inductive|irreducible_def|opaque) ${escaped}\\b`;
  try {
    const { stdout } = await execFileAsync("git", ["-C", mathlibDir, "grep", "-lE", pattern, "--", "Mathlib/*.lean"], { maxBuffer: 1 << 20 });
    return stdout.split("\n").filter((f) => f.length > 0).map((f) => join(mathlibDir, f));
  } catch (e) {
    // exit 1 = no match; anything else (no git, not a repo) also means no candidates
    void e;
    return [];
  }
}

async function validateUnique(
  workspaceRoot: string,
  requestedFq: string,
  candidates: Candidate[],
  label: string,
  visibleBefore?: { abs: string; line: number },
): Promise<ResolvedLeanDeclaration | null> {
  const valid: (Candidate & { snippet: string })[] = [];
  const seen = new Set<string>();
  for (const c of candidates) {
    let abs: string;
    try { abs = await safeRealFile(workspaceRoot, c.abs); } catch (e) {
      if ((e as NodeJS.ErrnoException).code === "ENOENT") continue;
      throw e;
    }
    const key = `${abs}\0${c.decl}`;
    if (seen.has(key)) continue;
    seen.add(key);
    const source = await readFile(abs, "utf8");
    const short = leafOf(c.decl);
    const matches = fullyQualifiedSourceDecls(source).filter((d) => leafOf(d.name) === short);
    for (const d of matches) {
      if (visibleBefore?.abs === abs && d.line >= visibleBefore.line) continue;
      const actualFq = d.name;
      if (actualFq !== c.decl) continue;
      valid.push({ ...c, abs, file: canonicalFile(workspaceRoot, abs), line: d.line, snippet: extractDeclSnippet(source, c.decl, d.line) });
    }
  }
  if (valid.length > 1) {
    throw new Error(`P1 Lean declaration resolution is ambiguous for ${requestedFq} via ${label}: ${valid.map((v) => `${v.file}:${v.decl}:${v.line}`).join(", ")}`);
  }
  const hit = valid[0];
  return hit ? { file: hit.file, decl: hit.decl, line: hit.line, snippet: hit.snippet, relocated: true, resolution: hit.resolution } : null;
}

export async function resolvedLeanAbsolutePath(repoRoot: string, canonicalFile: string): Promise<string> {
  if (isAbsolute(canonicalFile) || canonicalFile.split(/[\\/]/).includes(".."))
    throw new Error(`P1 rejects non-canonical resolved Lean pointer: ${canonicalFile}`);
  const { workspaceRoot } = await rootsFor(repoRoot);
  return safeRealFile(workspaceRoot, resolve(workspaceRoot, canonicalFile));
}

/** Resolve and validate the exact fully-qualified declaration behind a crosswalk pointer.
 * The recorded file may be a thin re-export; leaf-name uniqueness is never authority. */
/** A declaration the run does not own: the Causalean library (by `doc/library_index.json`) or
 *  the pinned Mathlib checkout. Unique, authenticated body or null. */
type LibraryIndexRow = { name?: string; file?: string; line?: number };
const libraryIndexCache = new Map<string, Promise<Map<string, LibraryIndexRow[]>>>();
/** The workspace `doc/library_index.json` rows by exact name, read once per workspace. */
export function loadLibraryIndex(workspaceRoot: string): Promise<Map<string, LibraryIndexRow[]>> {
  let p = libraryIndexCache.get(workspaceRoot);
  if (!p) {
    p = (async () => {
      const byName = new Map<string, LibraryIndexRow[]>();
      let rows: LibraryIndexRow[] = [];
      try {
        rows = (JSON.parse(await readFile(join(workspaceRoot, "doc", "library_index.json"), "utf8")) as { entries?: LibraryIndexRow[] }).entries ?? [];
      } catch (e) {
        if (!(e instanceof SyntaxError) && (e as NodeJS.ErrnoException).code !== "ENOENT") throw e;
      }
      for (const r of rows) {
        if (typeof r.name !== "string" || typeof r.file !== "string" || !Number.isFinite(r.line)) continue;
        byName.set(r.name, [...(byName.get(r.name) ?? []), r]);
      }
      return byName;
    })();
    libraryIndexCache.set(workspaceRoot, p);
  }
  return p;
}

export async function resolveLibraryDeclaration(
  repoRoot: string,
  decl: string,
  opts: { mathlib?: boolean } = {},
): Promise<ResolvedLeanDeclaration | null> {
  const { packageRoot, workspaceRoot } = await rootsFor(repoRoot);
  const rows = (await loadLibraryIndex(workspaceRoot)).get(decl) ?? [];
  const indexed = await validateUnique(workspaceRoot, decl, rows.map((e) => ({
    abs: resolve(workspaceRoot, e.file!), file: "", decl, line: e.line!, resolution: "library-index" as const,
  })), "library index");
  if (indexed || opts.mathlib === false) return indexed;
  // A Mathlib lookup is a `git grep` over the checkout — seconds per name; only callers that
  // must resolve every component ask for it.
  const mathlibFiles = await mathlibDeclarationFiles(mathlibCheckout(packageRoot, workspaceRoot), leafOf(decl));
  return validateUnique(workspaceRoot, decl, mathlibFiles.map((abs) => ({
    abs, file: "", decl, line: 1, resolution: "library-index" as const,
  })), "Mathlib package");
}

export async function resolveLeanDeclaration(
  repoRoot: string,
  leanSubdir: string,
  requested: { file: string; decl: string; line: number },
): Promise<ResolvedLeanDeclaration> {
  if (isAbsolute(requested.file) || requested.file.split(/[\\/]/).includes("..")) {
    throw new Error(`P1 rejects non-relative/traversing Lean pointer: ${requested.file}`);
  }
  const { packageRoot, workspaceRoot } = await rootsFor(repoRoot);
  const runDir = resolve(packageRoot, leanSubdir);
  if (!within(packageRoot, runDir)) throw new Error(`P1 lean_subdir escapes package root: ${leanSubdir}`);
  const realRunDir = await realpath(runDir);
  if (!within(packageRoot, realRunDir)) throw new Error(`P1 lean_subdir symlink escapes package root: ${leanSubdir}`);
  const recordedAbs = resolve(runDir, requested.file);
  if (!within(runDir, recordedAbs)) throw new Error(`P1 recorded Lean pointer escapes run root: ${requested.file}`);
  const leaf = leafOf(requested.decl);
  let recordedSource = "";
  try {
    const realRecorded = await safeRealFile(workspaceRoot, recordedAbs);
    if (!within(realRunDir, realRecorded)) {
      throw new Error(`P1 recorded Lean pointer symlink escapes run root: ${requested.file}`);
    }
    recordedSource = await readFile(realRecorded, "utf8");
  }
  catch (e) {
    if ((e as NodeJS.ErrnoException).code !== "ENOENT") throw e;
  }

  const exportsForLeaf = recordedSource ? explicitExports(recordedSource, leaf) : [];
  const authenticatedExports = exportsForLeaf.filter((e) => e.aliasFq === requested.decl);
  if (exportsForLeaf.length > 0 && authenticatedExports.length === 0) {
    throw new Error(
      `P1 re-export alias namespace mismatch for ${requested.decl}: recorded source authenticates ` +
      exportsForLeaf.map((e) => `${e.aliasFq} -> ${e.targetFq}`).join(", "),
    );
  }
  if (authenticatedExports.length > 1) {
    throw new Error(`P1 re-export target is ambiguous for ${requested.decl}: ${authenticatedExports.map((e) => e.targetFq).join(", ")}`);
  }
  if (recordedSource && authenticatedExports.length === 0) {
    const local = await validateUnique(workspaceRoot, requested.decl, [{
      abs: recordedAbs, file: "", decl: requested.decl, line: requested.line, resolution: "crosswalk",
    }], "recorded source");
    if (local) return { ...local, relocated: false, resolution: "crosswalk" };
  }

  const exported = authenticatedExports[0];
  const recordedVisibleSource = exported ? recordedSource.slice(0, exported.offset) : recordedSource;
  const visibleBefore = exported ? {
    abs: await realpath(recordedAbs), line: recordedVisibleSource.split("\n").length,
  } : undefined;
  const targetNames: string[] = [];
  if (exported && !exported.targetFq.startsWith("_root_.")) {
    let namespace = exported.enclosing;
    while (namespace) {
      targetNames.push(qualify(namespace, exported.targetFq));
      const leaf = leanNameLeaf(namespace);
      namespace = namespace.slice(0, Math.max(0, namespace.length - leaf.length - 1));
    }
  }
  targetNames.push((exported?.targetFq ?? requested.decl).replace(/^_root_\./, ""));
  const imports = [...maskLeanCommandQuotations(recordedSource).matchAll(/^\s*import\s+([A-Za-z0-9_.']+)/gm)].map((m) => m[1]);
  const importFiles = imports.flatMap((name) => [packageRoot, workspaceRoot].map((root) => join(root, ...name.split(".")) + ".lean"));
  // Read fallback metadata once per resolution, not once for every enclosing namespace.
  let indexRows: { name?: string; file?: string; line?: number }[] = [];
  try {
    indexRows = (JSON.parse(await readFile(join(workspaceRoot, "doc", "library_index.json"), "utf8")) as { entries?: typeof indexRows }).entries ?? [];
  } catch (e) {
    if (!(e instanceof SyntaxError) && (e as NodeJS.ErrnoException).code !== "ENOENT") throw e;
  }
  const importedAliases = explicitExports(recordedVisibleSource, leaf);
  const declaredNamespaces = new Set<string>();
  const rememberNamespaces = (source: string) => {
    const masked = maskLeanCommandQuotations(source);
    namespaceAtOffset(masked, masked.length, declaredNamespaces);
    for (const d of fullyQualifiedSourceDecls(source)) {
      const parent = d.name.slice(0, Math.max(0, d.name.length - leafOf(d.name).length - 1));
      if (parent) declaredNamespaces.add(parent);
    }
  };
  if (exported) {
    rememberNamespaces(recordedVisibleSource);
    for (const file of new Set(importFiles)) {
      try {
        const source = await readFile(await safeRealFile(workspaceRoot, file), "utf8");
        importedAliases.push(...explicitExports(source, leaf));
        rememberNamespaces(source);
      } catch (e) {
        if ((e as NodeJS.ErrnoException).code !== "ENOENT") throw e;
      }
    }
  }
  let mathlibFiles: string[] | undefined;
  for (const targetFq of [...new Set(targetNames)]) {
    const rows = indexRows.filter((e) => e.name === targetFq && typeof e.file === "string" && Number.isFinite(e.line));
    const indexed = await validateUnique(workspaceRoot, targetFq, rows.map((e) => ({
      abs: resolve(workspaceRoot, e.file!), file: "", decl: targetFq, line: e.line!, resolution: "library-index",
    })), "library index", visibleBefore);
    if (indexed) return indexed;

    if (exported) {
      const local = await validateUnique(workspaceRoot, targetFq, [recordedAbs, ...importFiles].map((abs) => ({
        abs, file: "", decl: targetFq, line: 0, resolution: "export-import" as const,
      })), "explicit export/import graph", visibleBefore);
      if (local) return local;

    }

    // Locate a reused declaration in the pinned Mathlib checkout, then authenticate its FQ name.
    mathlibFiles ??= await mathlibDeclarationFiles(mathlibCheckout(packageRoot, workspaceRoot), leaf);
    const library = await validateUnique(workspaceRoot, targetFq, mathlibFiles.map((abs) => ({
      abs, file: "", decl: targetFq, line: 1, resolution: "library-index" as const,
    })), "Mathlib package", visibleBefore);
    if (library) return library;
    if (exported) {
      // A nearer alias shadows an outer declaration of the same name. Unsupported alias
      // chains must halt, never silently authenticate the outer declaration as its body.
      if (importedAliases.some((alias) => alias.aliasFq === targetFq)) {
        throw new Error(`P1 cannot resolve nested export ${targetFq} behind ${requested.decl}; refusing outer-namespace fallback`);
      }
      const targetNamespace = targetFq.slice(0, Math.max(0, targetFq.length - leaf.length - 1));
      if (declaredNamespaces.has(targetNamespace)) {
        throw new Error(`P1 export namespace ${targetNamespace} contains no authenticated body for ${targetFq}; refusing outer-namespace fallback`);
      }
    }
  }
  throw new Error(`P1 cannot audit ${requested.decl}: ${requested.file}:${requested.line} contains no exact declaration body and no unique authoritative source was resolved`);
}

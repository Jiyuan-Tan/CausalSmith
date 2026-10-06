#!/usr/bin/env node
/**
 * Refresh a published bundle's cached view of its Lean code without re-emitting the paper.
 *
 * `doc/presentation/<bundle>/paper_library_index.json` (source, docstring and line of every
 * declaration of the paper's modules) and the statement texts in `lean_snippets.json` are
 * written by P4 and go stale when the Lean files are edited afterwards in a way that changes no
 * statement: an attribute line, a renamed library namespace, shifted line numbers. This re-reads
 * the index from the compiled modules, and re-extracts each top-level snippet statement that is
 * not in its file any more. Component statements, snippet and crosswalk line numbers, and
 * `nl_links.json` stay as P4 wrote them. The paper, its version, its date and its pinned commit
 * are untouched; the index's `commit` becomes the current HEAD, so the Formalization page says
 * the index is newer than the paper's pin. Use `causalsmith present … --from P4` when the paper
 * itself must be re-issued.
 *
 *   npx tsx bin/refresh_paper_index.ts <bundle> [<bundle> …]
 *
 * The index is re-read from the compiled modules the bundle already indexes (build them first).
 * A refresh that would drop a published declaration or blank a field is refused. Afterwards run
 * `npx tsx bin/check_paper_indexes.ts --strict --bundle <bundle>`.
 */
import { execFile } from "node:child_process";
import { existsSync } from "node:fs";
import { readFile, rename, rm, writeFile } from "node:fs/promises";
import path from "node:path";
import process from "node:process";
import { promisify } from "node:util";
import { tryExtractDeclSnippet } from "../src/presentation/lean_extract.js";
import { resolvedLeanAbsolutePath } from "../src/presentation/declaration_resolver.js";
import { SYNTHETIC_COMPANION_RE } from "../src/presentation/paper_index_orphans.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";

const execFileP = promisify(execFile);
const FIELDS = ["source", "doc", "module", "file", "statement", "kind", "line"] as const;
/** The marker the extractor appends to a capped snippet (as `check_paper_indexes.ts` reads it). */
const TRUNCATION = /\n[ \t]*-- … \(?truncated[\s\S]*$/;

type Entry = { name?: string; module?: string; file?: string; line?: number; source?: string | null } & Record<string, unknown>;
type Index = { modules?: Record<string, unknown>; entries: Entry[] };
type Snippet = { decl?: string; file?: string; line?: number; statement?: string };

async function readJson<T>(file: string): Promise<T> {
  return JSON.parse(await readFile(file, "utf8")) as T;
}

/** The declarations of `previous` that carry a source position must survive with every field. */
function refuseLoss(previous: Index, next: Index): void {
  const byName = new Map(next.entries.flatMap((e) => (typeof e.name === "string" ? [[e.name, e] as const] : [])));
  const lost: string[] = [];
  const blanked: string[] = [];
  for (const old of previous.entries) {
    if (typeof old.name !== "string" || typeof old.source !== "string" || !old.source || !old.line) continue;
    const now = byName.get(old.name);
    if (!now) {
      if (!SYNTHETIC_COMPANION_RE.test(old.name)) lost.push(old.name);
      continue;
    }
    for (const f of FIELDS) {
      const a = old[f];
      const b = now[f];
      if (a !== null && a !== undefined && (b === null || b === undefined || (f === "line" && b === 0))) blanked.push(`${old.name}.${f}`);
    }
  }
  if (lost.length) throw new Error(`the refreshed index would drop ${lost.length} published declaration(s): ${lost.slice(0, 8).join(", ")}`);
  if (blanked.length) throw new Error(`the refreshed index would blank ${blanked.length} published field(s): ${blanked.slice(0, 8).join(", ")}`);
}

async function refreshIndex(csRoot: string, bundleDir: string, subdir: string): Promise<Index> {
  const indexPath = path.join(bundleDir, "paper_library_index.json");
  const previous = await readJson<Index>(indexPath);
  const prefix = subdir.replace(/\//g, ".");
  const own = (m: unknown): m is string => typeof m === "string" && (m === prefix || m.startsWith(`${prefix}.`));
  const modules = [...new Set([...Object.keys(previous.modules ?? {}), ...previous.entries.map((e) => e.module)].filter(own))].sort();
  if (modules.length === 0) throw new Error(`${indexPath} names no module under ${prefix}`);
  const candidate = `${indexPath}.next-${process.pid}`;
  try {
    await execFileP(
      "lake",
      ["-d", csRoot, "exe", "paper_index", "--", "--prefix", prefix, "--src-root", csRoot, "--modules", modules.join(","), "--out", candidate],
      { cwd: csRoot, maxBuffer: 16 * 1024 * 1024, timeout: 1_800_000 },
    );
    const next = await readJson<Index>(candidate);
    if (!Array.isArray(next.entries) || next.entries.length === 0) throw new Error("paper_index produced an empty index");
    refuseLoss(previous, next);
    await rename(candidate, indexPath);
    return next;
  } finally {
    await rm(candidate, { force: true });
  }
}

/** The text a snippet's `file` names: run-relative first, else workspace-canonical. */
async function snippetText(csRoot: string, subdir: string, file: string): Promise<string | null> {
  const local = path.join(csRoot, subdir, file);
  if (existsSync(local)) return readFile(local, "utf8");
  try {
    return await readFile(await resolvedLeanAbsolutePath(csRoot, file), "utf8");
  } catch {
    return null;
  }
}

/** Where `decl` lives now: the paper's own index, else the library index. Run files are
 *  recorded run-relative, library files workspace-canonical, as P4 records them. */
function locate(decl: string, subdir: string, index: Index, library: Map<string, Entry>): { file: string; line: number } | null {
  const mine = index.entries.find((e) => e.name === decl);
  if (mine?.file && mine.line) {
    const rel = path.posix.relative(subdir, mine.file);
    return { file: rel.startsWith("..") ? mine.file : rel, line: mine.line };
  }
  const lib = library.get(decl);
  return lib?.file && lib.line ? { file: lib.file, line: lib.line } : null;
}

async function refreshSnippets(csRoot: string, bundleDir: string, subdir: string, index: Index, library: Map<string, Entry>): Promise<number> {
  const file = path.join(bundleDir, "lean_snippets.json");
  if (!existsSync(file)) return 0;
  const doc = await readJson<{ snippets: Record<string, Snippet> }>(file);
  let changed = 0;
  const refresh = async (s: Snippet, id: string): Promise<void> => {
    if (!s.statement || !s.file || !s.decl || s.decl === "(composite)") return;
    const text = await snippetText(csRoot, subdir, s.file);
    if (text !== null && text.includes(s.statement.replace(TRUNCATION, ""))) return; // still current
    let fresh = text === null ? null : tryExtractDeclSnippet(text, s.decl, Number(s.line ?? 0));
    if (fresh === null) {
      const at = locate(s.decl, subdir, index, library);
      const moved = at ? await snippetText(csRoot, subdir, at.file) : null;
      fresh = at && moved !== null ? tryExtractDeclSnippet(moved, s.decl, at.line) : null;
      if (fresh === null || !at) throw new Error(`${id}: \`${s.decl}\` is not in ${s.file} and was not found elsewhere`);
      s.file = at.file;
      s.line = at.line;
    }
    s.statement = fresh;
    changed++;
    console.log(`  snippet ${id} (${s.decl})`);
  };
  for (const [id, s] of Object.entries(doc.snippets ?? {})) {
    await refresh(s, id);
  }
  if (changed > 0) await writeFile(file, JSON.stringify(doc, null, 2) + "\n", "utf8");
  return changed;
}

async function main(): Promise<void> {
  const bundles = process.argv.slice(2);
  if (bundles.length === 0 || bundles.includes("--help")) {
    console.log("usage: refresh_paper_index.ts <bundle> [<bundle> …]   (names under doc/presentation/)");
    process.exit(bundles.length === 0 ? 2 : 0);
  }
  const csRoot = findCausalSmithRoot(process.cwd());
  const libraryIndex = path.join(csRoot, "..", "doc", "library_index.json");
  const library = new Map<string, Entry>(
    existsSync(libraryIndex)
      ? (await readJson<{ entries: Entry[] }>(libraryIndex)).entries.flatMap((e) => (typeof e.name === "string" ? [[e.name, e] as const] : []))
      : [],
  );
  for (const bundle of bundles) {
    const bundleDir = path.join(csRoot, "doc", "presentation", bundle);
    const crosswalk = await readJson<{ lean_subdir?: string }>(path.join(bundleDir, "presentation_crosswalk.json"));
    if (!crosswalk.lean_subdir) throw new Error(`${bundle}: presentation_crosswalk.json names no lean_subdir`);
    const index = await refreshIndex(csRoot, bundleDir, crosswalk.lean_subdir);
    const snippets = await refreshSnippets(csRoot, bundleDir, crosswalk.lean_subdir, index, library);
    console.log(`${bundle}: index refreshed (${index.entries.length} declarations), ${snippets} snippet(s) refreshed`);
  }
}

main().catch((err: unknown) => {
  console.error(`refresh_paper_index: ${err instanceof Error ? err.message : String(err)}`);
  process.exit(1);
});

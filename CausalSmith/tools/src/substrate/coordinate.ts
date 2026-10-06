// CausalSmith/tools/src/substrate/coordinate.ts
//
// The `coordinate` phase — intelligent successor of the mechanical `promote`.
//
// On reviewer PASS, a codex COORDINATOR agent decides how the proven substrate
// integrates into Causalean: which existing topical module it belongs in
// (merge-first, so repeated `--study` runs follow the library's subject
// hierarchy), what existing decls it should reuse
// instead of reinventing, and how it is documented per the docstring-canonical
// workflow (per-decl docstrings, module docstring, `headline_theorems` sidecar,
// `doc/API.md` GEN markers).
//
// The intelligence is codex's; SAFETY is deterministic TS. The coordinator emits
// a structured MANIFEST (never free-form edits); this module applies it under
// snapshot / verify / rollback. Crucially, edits to EXISTING Lean files are
// INSERT-ONLY (a merge cannot modify or delete a proven decl — asserted by
// byte-preservation), and codex never self-certifies the build: the integration
// gate runs deterministically and rolls back everything on any failure. The gate
// is `lake build` → `lake exe library_index`, then two concurrent branches that
// only read the fresh index and write disjoint files — embeddings (`embed:library`
// → `lint:embeddings`) and docs (structural lints → crosslink lint → `doc:gen` →
// `doc:check`) — joined before the verdict.
//
// Manifest content is carried inline (full bodies / insert patches as strings).
// For the typical substrate run (1–3 files) this stays well within codex output
// limits and keeps the apply layer deterministic and unit-testable; if large
// runs prove truncation-prone, switch to a codex-writes-staging-dir handoff.
import { mkdir, readFile, writeFile, unlink, rmdir, rm, readdir } from "node:fs/promises";
import { existsSync } from "node:fs";
import path from "node:path";
import { lintLibraryLayout, baselineKey, isBlockingFinding, type Finding as LayoutFinding } from "../../bin/lint_library_layout.js";
import { lintModuleHeaders, type Finding as HeaderFinding } from "../../bin/lint_module_headers.js";
import { LockAcquireError, withLakeBuildLock } from "../shared/build_mutex.js";
import { spawnWithInactivityTimeout } from "../workers/spawn.js";
import { bashBinary } from "../local_config.js";
import { runCodex as realRunCodex } from "../shared/codex.js";
import { expectStringJsonOutput, persistCodexRaw } from "../shared/codex_json.js";
import { maskLeanCommentsAndStrings } from "../shared/lean_mask.js";
import { isLeanModuleFile, LEAN_MODULE_LINE_RE, parseLeanImport } from "../shared/lean_syntax.js";
import { causaleanRoot } from "./paths.js";
import { logAgentCall } from "./log.js";
import { buildCoordinatorPrompt } from "./prompts.js";
import { parseCoordinationManifest, type CoordinationManifest } from "./types.js";

// --- The coordinator agent (codex → manifest) ---------------------------------

export interface CoordinatorArgs {
  repoRoot: string;
  runDir: string;
  round: number;
  slug: string;
  requirement: string;
  leanDir: string;
  modulePrefix: string;
  leanFiles: string[];
  /** Directory where the coordinator WRITES file bodies / insert patches; the
   *  manifest references them by `from`. Keeps large content out of the JSON. */
  stagingDir: string;
  /** Failing integration-gate log from the previous coordinate attempt, fed back
   *  so codex can fix placement / imports / a dedup that broke the build. */
  lastFailureLog: string | null;
}
export interface CoordinatorDeps {
  runCodex: typeof realRunCodex;
}

export async function runCoordinator(
  args: CoordinatorArgs,
  deps: CoordinatorDeps = { runCodex: realRunCodex },
): Promise<CoordinationManifest> {
  const prompt = buildCoordinatorPrompt(args);
  // why: retries must not see staged bodies from an earlier coordinate attempt.
  await rm(args.stagingDir, { recursive: true, force: true });
  await mkdir(args.stagingDir, { recursive: true });
  const t0 = Date.now();
  let stdout = "";
  let parsed: CoordinationManifest | undefined;
  let parseError: string | undefined;
  try {
    // cwd = the Causalean root so codex sees BOTH the staging substrate (under
    // CausalSmith/) and the Causalean tree it integrates into, and lean-lsp
    // targets the Causalean lake project.
    const res = await deps.runCodex({ prompt, cwd: causaleanRoot(args.repoRoot) });
    stdout = res.stdout;
    // Persist raw stdout BEFORE parsing, so a parse failure leaves a forensic
    // trail (the #1 historical breakdown cause) in the run dir.
    await persistCodexRaw(args.runDir, "coordinator", stdout);
    parsed = parseCoordinationManifest(expectStringJsonOutput(stdout));
    await assertManifestFromFilesExist(args.stagingDir, parsed);
    return parsed;
  } catch (err) {
    parseError = err instanceof Error ? err.message : String(err);
    throw err;
  } finally {
    await logAgentCall(args.runDir, {
      agent: "coordinator", round: args.round, callId: "main", model: "codex",
      prompt, promptBytes: Buffer.byteLength(prompt), rawOutput: stdout,
      parsed, parseError, ok: parseError === undefined, durationMs: Date.now() - t0,
    });
  }
}

// --- Deterministic manifest apply (snapshot / verify / rollback) ---------------

export interface CoordinateApplyDeps {
  /** `timedOut` is set when the command was watchdog-killed (inactivity/liveness)
   *  rather than exiting on its own. A kill is NOT proof the step failed, so the
   *  caller escalates instead of rolling back proven work. `lakeLock` marks a
   *  command that runs Lake in `cwd` and so must hold that project's build lock. */
  run: (
    cmd: string,
    cwd: string,
    opts?: { lakeLock?: boolean },
  ) => Promise<{ code: number; log: string; timedOut?: boolean }>;
  readFile: (p: string) => Promise<string>;
  writeFile: (p: string, text: string) => Promise<void>;
  removeFile: (p: string) => Promise<void>;
  removeDir?: (p: string) => Promise<void>;
  exists: (p: string) => Promise<boolean>;
  lintLibraryLayout?: (root: string) => LayoutFinding[] | Promise<LayoutFinding[]>;
  lintModuleHeaders?: (
    files: string[],
    allowLegacy: boolean,
  ) => ReturnType<typeof lintModuleHeaders> | Promise<ReturnType<typeof lintModuleHeaders>>;
}

const realApplyDeps: CoordinateApplyDeps = {
  run: async (cmd, cwd, opts) => {
    const spawnCommand = async () => {
      // Drop any inherited isolated TMPDIR: the nested `doc:gen` / `embed:library`
      // tsx subcommands open an IPC pipe under TMPDIR and would collide on a
      // per-run TMPDIR (see promote.ts for the same fix).
      const env = { ...process.env };
      delete env.TMPDIR;
      // Inactivity bounds a SILENT hang; the wall-clock backstop bounds a step
      // that spins forever while EMITTING output (which would keep `lastOutput`
      // fresh and never trip inactivity), so a runaway verify can never hold the
      // promotion lock indefinitely. Generous (> inactivity); `CAUSALSMITH_VERIFY_MAX_MS=0`
      // disables it. Both kinds surface as `timedOut` → escalate (preserve).
      const maxTotalMs = Number(process.env.CAUSALSMITH_VERIFY_MAX_MS ?? 60 * 60 * 1000);
      // Preserve the parent process's verified Node/npm PATH. A login shell can
      // re-run nvm initialization while npm_config_prefix is set by `npx
      // --prefix tools`, leaving npm unavailable for the post-build embedding
      // steps even though it launched this pipeline successfully.
      const r = await spawnWithInactivityTimeout(bashBinary(), ["-c", cmd], {
        cwd, env, inactivityTimeoutMs: 30 * 60 * 1000, maxTotalMs,
      });
      const log = [r.stdout, r.stderr].filter(Boolean).join("\n");
      const timedOut =
        r.killedDueToInactivity || r.killedDueToLiveness != null || r.killedDueToTotalTimeout === true;
      const code = (r.exitCode ?? 1) !== 0 ? 1 : 0;
      return { code, log, timedOut };
    };
    // Lake commands serialize on their project's build lock. The tools-dir gates
    // run no Lake, and the two verify branches run them side by side.
    return opts?.lakeLock ? withLakeBuildLock(cwd, spawnCommand) : spawnCommand();
  },
  readFile: (p) => readFile(p, "utf8"),
  writeFile: async (p, text) => { await mkdir(path.dirname(p), { recursive: true }); await writeFile(p, text, "utf8"); },
  removeFile: async (p) => { await unlink(p).catch(() => {}); },
  removeDir: async (p) => { await rmdir(p).catch(() => {}); },
  exists: async (p) => existsSync(p),
  lintLibraryLayout,
  lintModuleHeaders,
};

/** Resolve `rel` against the Causalean root, refusing any path that escapes it. */
function resolveInside(cRoot: string, rel: string): string {
  const abs = path.resolve(cRoot, rel);
  const back = path.relative(cRoot, abs);
  if (back === "" || back.startsWith("..") || path.isAbsolute(back)) {
    throw new Error(`manifest op path escapes the Causalean root: ${rel}`);
  }
  return abs;
}

async function listStagedFiles(root: string, dir = root): Promise<Set<string>> {
  const out = new Set<string>();
  const entries = await readdir(dir, { withFileTypes: true }).catch(() => []);
  for (const entry of entries) {
    const abs = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      for (const nested of await listStagedFiles(root, abs)) out.add(nested);
    } else if (entry.isFile()) {
      out.add(path.relative(root, abs));
    }
  }
  return out;
}

async function assertManifestFromFilesExist(stagingDir: string, manifest: CoordinationManifest): Promise<void> {
  const staged = await listStagedFiles(stagingDir);
  for (const op of manifest.ops) {
    const abs = resolveInside(stagingDir, op.from);
    const rel = path.relative(stagingDir, abs);
    // why: the staging dir was cleared for this attempt, so membership proves this round wrote it.
    if (!staged.has(rel)) throw new Error(`manifest references unstaged from file: ${op.from}`);
  }
}

function isLeanWriteTarget(target: string): boolean {
  const normalized = target.replace(/\\/g, "/");
  return normalized === "Causalean.lean" || normalized.endsWith(".lean");
}

/** Add one barrel import in deterministic module-name order. */
export function insertImportSorted(rootFileText: string, importLine: string): string {
  const lines = rootFileText.split(/\r?\n/);
  const maskedLines = maskLeanCommentsAndStrings(rootFileText).split(/\r?\n/);
  const incoming = parseLeanImport(importLine);
  if (!incoming) throw new Error(`invalid Lean import line: ${importLine}`);
  const existing = lines
    .map((line, index) => ({ line, index, parsed: parseLeanImport(maskedLines[index] ?? "") }))
    .filter((row): row is { line: string; index: number; parsed: NonNullable<ReturnType<typeof parseLeanImport>> } => row.parsed != null);
  if (existing.some((row) => row.line === importLine)) return rootFileText;

  const imports = [
    ...existing.filter((row) => row.parsed.module !== incoming.module).map((row) => row.line),
    importLine,
  ].sort((a, b) => {
    const am = parseLeanImport(a)!.module;
    const bm = parseLeanImport(b)!.module;
    return am < bm ? -1 : am > bm ? 1 : a < b ? -1 : a > b ? 1 : 0;
  });
  if (existing.length > 0) {
    const firstImport = existing[0].index;
    const importIndexes = new Set(existing.map((row) => row.index));
    const rest = lines.filter((_, index) => !importIndexes.has(index));
    rest.splice(firstImport, 0, ...imports);
    return rest.join("\n");
  }

  const moduleLine = isLeanModuleFile(rootFileText)
    ? lines.findIndex((line) => LEAN_MODULE_LINE_RE.test(line))
    : -1;
  lines.splice(moduleLine + 1, 0, importLine);
  return lines.join("\n");
}

function leanCodeOnly(content: string): string {
  let out = "";
  let blockDepth = 0;
  let inString = false;
  let escaped = false;
  for (let i = 0; i < content.length; i++) {
    const c = content[i];
    const next = content[i + 1] ?? "";
    if (blockDepth > 0) {
      if (c === "/" && next === "-") { blockDepth++; out += "  "; i++; }
      else if (c === "-" && next === "/") { blockDepth--; out += "  "; i++; }
      else out += c === "\n" ? "\n" : " ";
      continue;
    }
    if (inString) {
      out += c === "\n" ? "\n" : " ";
      if (escaped) escaped = false;
      else if (c === "\\") escaped = true;
      else if (c === '"') inString = false;
      continue;
    }
    if (c === "-" && next === "-") {
      while (i < content.length && content[i] !== "\n") { out += " "; i++; }
      if (i < content.length) out += "\n";
      continue;
    }
    if (c === "/" && next === "-") { blockDepth = 1; out += "  "; i++; continue; }
    if (c === '"') { inString = true; out += " "; continue; }
    out += c;
  }
  return out;
}

/** Blank the generated table inside every `<!-- GEN:<module> -->` … `<!-- /GEN -->` region of
 * doc/API.md (same region grammar as bin/library_doc_gen.ts), leaving hand-written text intact. */
function maskGenRegions(api: string): string {
  const moduleIdent = String.raw`[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*`;
  const re = new RegExp(
    String.raw`^(<!-- GEN:(${moduleIdent}) -->)[^\S\r\n]*\r?\n([\s\S]*?)^(<!-- /GEN -->)[^\S\r\n]*$`,
    "gm",
  );
  return api.replace(re, (_m, open: string, _mod: string, _inner: string, close: string) => `${open}\n${close}`);
}

function assertLibraryOnlyLeanContent(content: string, target: string): void {
  if (/\bCausalSmith\b/.test(leanCodeOnly(content))) {
    throw new Error(`final Lean content retains a CausalSmith dependency: ${target}`);
  }
}

/** Every Causalean import in a newly-created file must already exist or name
 * another module created by the same manifest.  Without this preflight, a
 * coordinator can accidentally shorten sibling imports after choosing a deep
 * placement (for example `Causalean.Stat.Basic` instead of
 * `Causalean.Stat.CLT.MartingaleArray.Basic`).  The mistake otherwise burns a
 * full build/index/embedding attempt before Lean reports the missing module.
 */
async function assertCreatedFileImportsResolve(
  content: string,
  target: string,
  createdModules: ReadonlySet<string>,
  cRoot: string,
  d: CoordinateApplyDeps,
): Promise<void> {
  const code = leanCodeOnly(content);
  for (const line of code.split(/\r?\n/)) {
    const imported = parseLeanImport(line)?.module;
    if (!imported || !/^Causalean(?:\.[A-Za-z0-9_']+)+$/.test(imported)) continue;
    if (createdModules.has(imported)) continue;
    const importedPath = path.join(cRoot, ...imported.split(".")) + ".lean";
    if (await d.exists(importedPath)) continue;

    const leaf = imported.slice(imported.lastIndexOf(".") + 1);
    const candidates = [...createdModules].filter((m) => m.endsWith(`.${leaf}`));
    const hint = candidates.length === 1 ? `; did you mean ${candidates[0]}?` : "";
    throw new Error(`unresolved Causalean import in ${target}: ${imported}${hint}`);
  }
}

function isCausaleanLeanPath(target: string): boolean {
  const parts = target.replace(/\\/g, "/").split("/");
  return parts[0] === "Causalean" && parts.length >= 3 && parts.at(-1)?.endsWith(".lean") === true;
}

function isAllowedRecordPath(target: string): boolean {
  const normalized = target.replace(/\\/g, "/");
  return normalized === "doc/API.md" || /^doc\/library_review\/[A-Za-z0-9_-]+\.json$/.test(normalized);
}

/**
 * `doc/library_review/` records declarations that live under `Causalean/`. A declaration that
 * stays under `CausalSmith/` has no index entry, so curating it makes `loadLibrary` throw and
 * blocks index regeneration repo-wide until the file is hand-edited. Reject that at the write,
 * so the coordinator is told which names to drop and retries.
 *
 * The test is the `CausalSmith.` root specifically, NOT "does the name start with `Causalean.`":
 * Causalean contributes many declarations into Mathlib root namespaces (`MeasureTheory.*`,
 * `ProbabilityTheory.*`, `Set.*`) and attribute decls (`Parser.Attr.*`), all of which are
 * legitimately curated in `Mathlib.json` / `Tactic.json`. A prefix test on `Causalean.` would
 * reject those on every rewrite of the complete sidecar, hard-blocking the `Causalean/Mathlib/`
 * promotion path the study workflow is built around.
 *
 * Shape validation mirrors `loadLibrary` exactly so this fast-fail is a faithful superset: a
 * sidecar that passes here must not then fail the gate on a shape this did not look at.
 */
function assertSidecarCuratesCausaleanOnly(target: string, content: string): void {
  const normalized = target.replace(/\\/g, "/");
  if (!/^doc\/library_review\/[A-Za-z0-9_-]+\.json$/.test(normalized)) return;
  let parsed: Record<string, unknown>;
  try {
    parsed = JSON.parse(content) as Record<string, unknown>;
  } catch {
    throw new Error(`sidecar write is not valid JSON: ${target}`);
  }
  for (const key of ["headline_theorems", "reviews", "flags"] as const) {
    if (!Array.isArray(parsed[key])) {
      throw new Error(`sidecar ${target}: missing array field ${key}`);
    }
  }
  const names: string[] = [];
  for (const t of parsed.headline_theorems as unknown[]) {
    if (typeof t !== "string") {
      throw new Error(`sidecar ${target}: headline_theorems entries must be strings`);
    }
    names.push(t);
  }
  for (const key of ["reviews", "flags"] as const) {
    for (const r of parsed[key] as unknown[]) {
      const decl = (r as { decl?: unknown } | null)?.decl;
      if (typeof decl !== "string") {
        throw new Error(`sidecar ${target}: every ${key} entry needs a string \`decl\``);
      }
      names.push(decl);
    }
  }
  const foreign = [...new Set(names.filter((n) => n.startsWith("CausalSmith.")))];
  if (foreign.length > 0) {
    throw new Error(
      `sidecar ${target} curates ${foreign.length} CausalSmith declaration(s), which have no ` +
        `index entry; remove only these (files that stay under CausalSmith/ get no sidecar ` +
        `entry, and every other existing entry must be preserved): ${foreign.slice(0, 5).join(", ")}` +
        (foreign.length > 5 ? ` (+${foreign.length - 5} more)` : ""),
    );
  }
}

async function assertOperationTarget(
  cRoot: string,
  op: CoordinationManifest["ops"][number],
  abs: string,
  d: CoordinateApplyDeps,
): Promise<void> {
  if (op.kind === "merge_lean") {
    if (!isCausaleanLeanPath(op.target) || !(await d.exists(abs))) {
      throw new Error(`merge_lean target must be an existing Causalean subject file: ${op.target}`);
    }
    return;
  }
  if (op.kind === "write_file") {
    if (!isAllowedRecordPath(op.target)) {
      throw new Error(`write_file target is outside the coordinator record allowlist: ${op.target}`);
    }
    return;
  }
  if (!isLeanWriteTarget(op.target) && !isAllowedRecordPath(op.target)) {
    throw new Error(`non-Lean create_file target is outside the coordinator record allowlist: ${op.target}`);
  }
  if (isLeanWriteTarget(op.target) && !isCausaleanLeanPath(op.target)) {
    throw new Error(`create_file Lean target must be inside a Causalean subject area: ${op.target}`);
  }
  void cRoot;
}

async function assertCreatePlacement(
  cRoot: string,
  target: string,
  newModule: string | undefined,
  d: CoordinateApplyDeps,
): Promise<void> {
  const normalized = target.replace(/\\/g, "/");
  if (!normalized.endsWith(".lean")) return;
  const parts = normalized.split("/");
  if (parts[0] !== "Causalean" || parts.length < 3) {
    throw new Error(`new Lean module must live inside an existing Causalean subject area: ${target}`);
  }
  const subjectRoot = path.join(cRoot, "Causalean", parts[1]);
  if (!(await d.exists(subjectRoot))) {
    throw new Error(`new Lean module names a non-existing Causalean subject area: ${parts[1]}`);
  }
  const expectedModule = normalized.slice(0, -".lean".length).replaceAll("/", ".");
  if (!newModule || newModule !== expectedModule) {
    throw new Error(`create_file newModule must match target (${expectedModule}): ${newModule ?? "(missing)"}`);
  }
}

function runNameKey(value: string): string {
  return value.replace(/\.lean$/i, "").replace(/[._-]/g, "").toLowerCase();
}

/** Reject run-derived destinations before the first mutation. Compare the slug, the complete
 * module prefix, and its terminal segment so dotted-prefix camel transforms cannot bypass the gate. */
async function assertNoRunNamedTargets(
  cRoot: string,
  manifest: CoordinationManifest,
  slug: string | undefined,
  modulePrefix: string | undefined,
  d: CoordinateApplyDeps,
): Promise<void> {
  const forbidden = new Set(
    [slug, modulePrefix, modulePrefix?.split(".").at(-1)]
      .filter((name): name is string => Boolean(name?.trim()))
      .map(runNameKey),
  );
  if (forbidden.size === 0) return;
  for (const op of manifest.ops) {
    if (!isLeanWriteTarget(op.target)) continue;
    const normalized = op.target.replace(/\\/g, "/");
    const parts = normalized.split("/");
    const basename = parts.at(-1) ?? "";
    if (forbidden.has(runNameKey(basename))) {
      throw new Error(`manifest target basename must not be named after the study/run: ${op.target}`);
    }
    if (op.kind !== "create_file" || parts[0] !== "Causalean") continue;
    for (let i = 1; i < parts.length - 1; i++) {
      const directory = path.join(cRoot, ...parts.slice(0, i + 1));
      if (!(await d.exists(directory)) && forbidden.has(runNameKey(parts[i]))) {
        throw new Error(`manifest must not create a directory named after the study/run: ${parts[i]}`);
      }
    }
  }
}

/** A directory barrel contains only its header/import surface. Comments and strings are masked
 * before classification; module files may also carry the house-style blanket section line. */
function isImportsOnlyDirectoryBarrel(source: string): boolean {
  const moduleFile = isLeanModuleFile(source);
  const code = maskLeanCommentsAndStrings(source);
  let sawImport = false;
  for (const line of code.split(/\r?\n/)) {
    if (line.trim() === "") continue;
    if (parseLeanImport(line)) {
      sawImport = true;
      continue;
    }
    if (moduleFile && LEAN_MODULE_LINE_RE.test(line)) continue;
    if (/^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:public[ \t]+)?(?:noncomputable[ \t]+)?section[ \t]*$/.test(line)) continue;
    return false;
  }
  return sawImport;
}

async function nearestDirectoryBarrel(
  cRoot: string,
  moduleName: string,
  d: CoordinateApplyDeps,
): Promise<string | null> {
  const parts = moduleName.split(".");
  for (let end = parts.length - 1; end >= 2; end--) {
    const candidate = path.join(cRoot, ...parts.slice(0, end)) + ".lean";
    const directory = candidate.slice(0, -".lean".length);
    if (!(await d.exists(candidate)) || !(await d.exists(directory))) continue;
    if (isImportsOnlyDirectoryBarrel(await d.readFile(candidate))) return candidate;
  }
  return null;
}

function normalizeLintPath(cRoot: string, findingPath: string): string {
  const absolute = path.isAbsolute(findingPath) ? findingPath : path.join(cRoot, findingPath);
  return path.relative(cRoot, absolute).replaceAll(path.sep, "/");
}

// The key and the blocking predicate are the lint's contract, shared with its CLI so the promotion
// gate and the CI/export gate can never disagree about what a finding means.
const layoutBaselineKey = baselineKey;

async function loadLayoutBaseline(repoRoot: string, d: CoordinateApplyDeps): Promise<Set<string>> {
  const baselinePath = path.join(repoRoot, "tools", "lint", "layout_baseline.json");
  if (!(await d.exists(baselinePath))) return new Set();
  const parsed = JSON.parse(await d.readFile(baselinePath)) as
    | LayoutFinding[]
    | { violations?: LayoutFinding[] };
  const findings = Array.isArray(parsed) ? parsed : parsed.violations ?? [];
  return new Set(findings.map(layoutBaselineKey));
}

function isSupersededMathlibHeadlineBan(finding: LayoutFinding): boolean {
  // Phase 5b deliberately replaces the older zero-headlines-in-Mathlib policy with the universal
  // 1–5-per-theorem-file contract. The lint source is owned by another migration task, so adapt
  // that single stale finding here while retaining its >5 cap and every other structural rule.
  return finding.rule === "HEADLINES" && finding.message === "Mathlib modules may not have headline entries";
}

function findingTouchesFiles(cRoot: string, findingPath: string, touched: ReadonlySet<string>): boolean {
  const finding = normalizeLintPath(cRoot, findingPath);
  for (const file of touched) {
    const rel = path.relative(cRoot, file).replaceAll(path.sep, "/");
    if (finding === rel || rel.startsWith(`${finding}/`)) return true;
  }
  return false;
}

function formatLayoutFinding(finding: LayoutFinding): string {
  return `${finding.rule}: ${finding.path}${finding.line ? `:${finding.line}` : ""}: ${finding.message}`;
}

function formatHeaderFinding(finding: HeaderFinding): string {
  return `${finding.path}:${finding.line}: ${finding.rule}: ${finding.message}`;
}

/**
 * Insert `insert` into `orig` after the first line containing `anchor` (empty
 * anchor → append at end of file). Returns the merged text plus the exact
 * inserted segment and its offset, so the caller can assert byte-preservation.
 */
export function applyInsertOnly(
  orig: string,
  anchor: string,
  insert: string,
): { merged: string; at: number; segment: string } {
  const block = insert.endsWith("\n") ? insert : `${insert}\n`;
  if (anchor.trim() === "") {
    const lead = orig.length === 0 || orig.endsWith("\n") ? "\n" : "\n\n";
    const segment = `${lead}${block}`;
    return { merged: orig + segment, at: orig.length, segment };
  }
  const lines = orig.split("\n");
  const idx = lines.findIndex((l) => l.includes(anchor));
  if (idx < 0) throw new Error(`merge_lean anchor not found: ${JSON.stringify(anchor)}`);
  // Char offset of the start of line idx+1 (i.e. just after line idx's newline).
  let at = 0;
  for (let i = 0; i <= idx; i++) at += lines[i].length + 1;
  if (at > orig.length) at = orig.length; // last line had no trailing newline
  const segment = `${block}\n`;
  const merged = orig.slice(0, at) + segment + orig.slice(at);
  return { merged, at, segment };
}

/** A merge must leave every pre-existing byte intact: removing the inserted
 *  segment at its offset must reproduce the original exactly. */
function assertInsertOnly(orig: string, merged: string, at: number, segment: string): void {
  const without = merged.slice(0, at) + merged.slice(at + segment.length);
  if (without !== orig) {
    throw new Error("insert-only invariant violated: a merge would change existing bytes");
  }
}

export interface ApplyManifestArgs {
  cRoot: string;
  repoRoot: string;
  /** Root the manifest's `from` paths resolve against (where codex staged the
   *  file bodies / insert patches). */
  stagingDir: string;
  leanFiles: string[];
  manifest: CoordinationManifest;
  slug?: string;
  modulePrefix?: string;
  /** Prefer an existing `Causalean/<TopDir>.lean` barrel for each new module. */
  barrelTarget?: "root" | "directory";
}

export interface ApplyResult {
  ok: boolean;
  log: string;
  /** A verify command was watchdog-killed: nothing was rolled back, a human decides. */
  timedOut?: boolean;
  /** A Lake build lock could not be acquired. Everything applied was rolled back and the
   *  manifest received no verdict, so the attempt says nothing about the coordination. */
  lockWait?: boolean;
}

interface VerifyStep { label: string; cmd: string; cwd: string; lakeLock?: boolean }
/** Log sections and per-step durations of one serial run of verify steps. */
interface VerifyLog { sections: string[]; timings: string[] }
/** The verify step that ended a run of steps without exiting 0. */
interface VerifyStop { end: "failed" | "timedOut"; cmd: string; output: string }

function seconds(ms: number): string {
  return `${(ms / 1000).toFixed(1)}s`;
}

export async function applyManifest(
  args: ApplyManifestArgs,
  d: CoordinateApplyDeps = realApplyDeps,
): Promise<ApplyResult> {
  const { cRoot, repoRoot, stagingDir, leanFiles, manifest } = args;
  const rootPath = path.join(cRoot, "Causalean.lean");
  // Every verify step logs one section stamped with its start time and its duration; the
  // closing timing line repeats the durations so they survive a tail-truncated log.
  const main: VerifyLog = { sections: [], timings: [] };
  let verifyStartedAt: Date | null = null;
  const finish = (status: string, notes: string[] = []): string => {
    const timing = verifyStartedAt === null ? [] : [
      `[coordinate] verify timing from ${verifyStartedAt.toISOString()}: ${main.timings.join("; ")}; `
        + `total ${seconds(Date.now() - verifyStartedAt.getTime())}`,
    ];
    return [...main.sections, ...timing, ...notes, status].join("\n\n");
  };
  const toolsDir = path.join(repoRoot, "tools");
  const embed: VerifyStep = { label: "embed", cmd: "npm run embed:library", cwd: toolsDir };
  let embedStarted = false;
  // abs path → original content (null = file did not exist, so rollback deletes).
  const snapshots = new Map<string, string | null>();
  // Record surfaces are full-file writes shared by every promotion. The
  // promotion mutex protects cooperating study runs, but an older/manual
  // process can still overwrite one while the long library-index gate runs.
  // Keep the exact staged bytes and fail at the first gate boundary where they
  // differ, instead of later misreporting the symptom as missing curation.
  const expectedRecordWrites = new Map<string, string>();
  const snap = async (abs: string) => {
    if (!snapshots.has(abs)) snapshots.set(abs, (await d.exists(abs)) ? await d.readFile(abs) : null);
  };
  const rollback = async () => {
    for (const [abs, orig] of snapshots) {
      if (orig === null) await d.removeFile(abs);
      else await d.writeFile(abs, orig);
    }
  };
  /** Roll back, then bring the embeddings back in line with the restored index when this
   *  attempt's embedding step may have written them. Returns the notes for the log; a resync
   *  that fails is reported and leaves the attempt's own verdict as it is. */
  const restore = async (): Promise<string[]> => {
    await rollback();
    if (!embedStarted) return [];
    const startedAt = Date.now();
    let problem: string;
    try {
      const r = await d.run(embed.cmd, embed.cwd);
      if (!r.timedOut && r.code === 0) {
        return [`[coordinate] embeddings resynced to the restored index (${seconds(Date.now() - startedAt)}).`];
      }
      problem = `${r.timedOut ? "watchdog-killed" : "exit nonzero"}: ${r.log.slice(-300)}`;
    } catch (err) {
      problem = err instanceof Error ? err.message : String(err);
    }
    return [
      `[coordinate] EMBEDDINGS NOT RESYNCED after rollback — doc/library_embeddings* may not match the `
        + `restored index; run \`${embed.cmd}\` in tools/ (${problem})`,
    ];
  };
  const manifestNewModules = new Set(
    manifest.ops
      .filter((op): op is Extract<CoordinationManifest["ops"][number], { kind: "create_file" }> =>
        op.kind === "create_file" && isLeanWriteTarget(op.target) && op.newModule != null)
      .map((op) => op.newModule as string),
  );
  const newModules: string[] = [];
  const touchedLeanFiles = new Set<string>();
  try {
    // This validation scans the whole manifest before any op can write, so a later run-named op
    // cannot transiently mutate an earlier target before rollback.
    await assertNoRunNamedTargets(cRoot, manifest, args.slug, args.modulePrefix, d);
    await snap(rootPath);
    for (const op of manifest.ops) {
      const abs = resolveInside(cRoot, op.target);
      await assertOperationTarget(cRoot, op, abs, d);
      if (op.kind === "create_file") {
        // The op body lives in a staged file; read it (never inline in the JSON).
        const content = await d.readFile(resolveInside(stagingDir, op.from));
        assertSidecarCuratesCausaleanOnly(op.target, content);
        await assertCreatePlacement(cRoot, op.target, op.newModule, d);
        if (isLeanWriteTarget(op.target)) {
          assertLibraryOnlyLeanContent(content, op.target);
          await assertCreatedFileImportsResolve(content, op.target, manifestNewModules, cRoot, d);
        }
        if (await d.exists(abs)) {
          // Recovery after an interrupted verification pass: the promotion may
          // already have written this new file even though study state did not
          // reach `done`. Accept only an exact byte match; any differing file
          // remains a hard placement conflict.
          const existing = await d.readFile(abs);
          if (existing !== content) {
            throw new Error(`create_file target already exists with different content (use merge_lean): ${op.target}`);
          }
        } else {
          await snap(abs);
          await d.writeFile(abs, content);
        }
        if (op.newModule) newModules.push(op.newModule);
        if (isLeanWriteTarget(op.target)) touchedLeanFiles.add(abs);
      } else if (op.kind === "merge_lean") {
        const content = await d.readFile(resolveInside(stagingDir, op.from));
        assertLibraryOnlyLeanContent(content, op.target);
        if (!(await d.exists(abs))) throw new Error(`merge_lean target does not exist: ${op.target}`);
        await snap(abs);
        const orig = await d.readFile(abs);
        const { merged, at, segment } = applyInsertOnly(orig, op.anchor, content);
        assertInsertOnly(orig, merged, at, segment);
        await d.writeFile(abs, merged);
        touchedLeanFiles.add(abs);
      } else {
        // write_file (non-Lean record surface)
        // why: Lean edits must go through create_file/merge_lean so existing bytes stay insert-only.
        if (isLeanWriteTarget(op.target)) throw new Error(`write_file cannot target Lean files: ${op.target}`);
        const content = await d.readFile(resolveInside(stagingDir, op.from));
        assertSidecarCuratesCausaleanOnly(op.target, content);
        await snap(abs);
        await d.writeFile(abs, content);
        expectedRecordWrites.set(abs, content);
      }
    }
    // Promotions default to the nearest imports-only directory barrel. The root remains available
    // only as an explicit override for callers with a deliberate exceptional wiring target.
    if (newModules.length > 0) {
      const byBarrel = new Map<string, string[]>();
      const useDirectoryBarrel = args.barrelTarget !== "root";
      for (const m of newModules) {
        const directoryBarrel = useDirectoryBarrel
          ? await nearestDirectoryBarrel(cRoot, m, d)
          : null;
        if (useDirectoryBarrel && !directoryBarrel) {
          throw new Error(`module-system promotion has no directory barrel for ${m}`);
        }
        const barrel = useDirectoryBarrel ? directoryBarrel : rootPath;
        if (!barrel) throw new Error(`directory-barrel promotion has no directory barrel for ${m}`);
        byBarrel.set(barrel, [...(byBarrel.get(barrel) ?? []), m]);
      }
      for (const [barrel, modules] of byBarrel) {
        await snap(barrel);
        let barrelText = await d.readFile(barrel);
        const importPrefix = isLeanModuleFile(barrelText) ? "public import" : "import";
        for (const m of modules) barrelText = insertImportSorted(barrelText, `${importPrefix} ${m}`);
        await d.writeFile(barrel, barrelText);
        touchedLeanFiles.add(barrel);
      }
    }
    // Integration gate — any failure rolls back.
    // `lake exe library_index` rewrites this tracked artifact, and doc gen rewrites `doc/API.md`.
    // Both must describe the same tree as the restored sources if a later step rejects the
    // integration.
    const apiMd = path.join(cRoot, "doc", "API.md");
    await snap(path.join(cRoot, "doc", "library_index.json"));
    await snap(apiMd);
    // The crosslink and documentation gates scan the WHOLE library, so a concurrent session's
    // in-flight docstring or uncurated file would fail a promotion that never touched it. Scope
    // their BLOCKING findings to this manifest's own Lean files (they still report the rest);
    // CI and the public export run the same tools without the flag and stay library-wide.
    const scopeFile = path.join(stagingDir, ".promotion-scope.txt");
    await d.writeFile(
      scopeFile,
      [...touchedLeanFiles].map((file) => path.relative(cRoot, file).replaceAll(path.sep, "/")).join("\n") + "\n",
    );
    const scopeArg = `--blocking-paths ${JSON.stringify(scopeFile)}`;
    const build: VerifyStep = { label: "build", cmd: "lake build", cwd: cRoot, lakeLock: true };
    const index: VerifyStep = { label: "index", cmd: "lake exe library_index", cwd: cRoot, lakeLock: true };
    const embedFresh: VerifyStep = { label: "lint:embeddings", cmd: "npm run lint:embeddings", cwd: toolsDir };
    // Crosslink gate: the /library page and the public export hard-fail on a
    // theorem whose docstring leaves a binder unlinked or a headline unannotated.
    const crosslinks: VerifyStep = { label: "crosslinks", cmd: `npx tsx bin/check_nl_crosslinks.ts ${scopeArg}`, cwd: toolsDir };
    const docGen: VerifyStep = { label: "doc:gen", cmd: `node --import tsx/esm bin/library_doc_gen.ts --write ${scopeArg}`, cwd: toolsDir };
    const docCheck: VerifyStep = { label: "doc:check", cmd: `npm run doc:check -- ${scopeArg}`, cwd: toolsDir };

    const everyRecord = (): boolean => true;
    const assertRecordsStable = async (step: string, guards: (record: string) => boolean) => {
      for (const [record, expected] of expectedRecordWrites) {
        if (!guards(record)) continue;
        const actual = await d.readFile(record);
        if (actual !== expected) {
          throw new Error(
            `promoted record changed before verify step '${step}': ${record}`,
          );
        }
      }
    };
    /** Run one command and log its section; `guards` selects the promoted records that must
     *  still hold their expected bytes when it starts (null: the caller has just checked). */
    const runStep = async (
      s: VerifyStep,
      sink: VerifyLog,
      guards: ((record: string) => boolean) | null,
    ): Promise<VerifyStop | null> => {
      if (guards) await assertRecordsStable(s.cmd, guards);
      const startedAt = new Date();
      verifyStartedAt ??= startedAt;
      if (s === embed) embedStarted = true;
      const r = await d.run(s.cmd, s.cwd, { lakeLock: s.lakeLock === true });
      const took = seconds(Date.now() - startedAt.getTime());
      const end = r.timedOut ? "timedOut" : r.code !== 0 ? "failed" : "ok";
      const outcome = end === "timedOut" ? "watchdog-killed" : end === "failed" ? "exit nonzero" : "exit 0";
      sink.sections.push(`[${startedAt.toISOString()}] $ (${s.cwd}) ${s.cmd}\n${r.log}\n[${outcome} after ${took}]`);
      sink.timings.push(`${s.label} ${took}`);
      return end === "ok" ? null : { end, cmd: s.cmd, output: r.log };
    };
    // A watchdog kill means the step went silent for the FULL timeout without
    // exiting — it may be genuinely stuck (deadlocked lake) OR was mid-flight
    // when killed. Either way a kill is NOT a compile error, and the files are
    // already promoted into Causalean, so rolling back destroys proven,
    // expensive work while a rollback of a mid-flight build is itself unsafe.
    // PRESERVE everything (no rollback, no source deletion) and escalate to a
    // human — who verifies the tree and keeps or reverts. The promotion is
    // UNVERIFIED until they do.
    const preserved = (cmd: string): ApplyResult => ({
      ok: false, timedOut: true,
      log: finish(`[coordinate] verify step '${cmd}' was watchdog-killed after going silent (unverified); files left in place for human verification (NOT rolled back).`),
    });
    // The status line names each failing step and repeats the end of its output, so the cause
    // survives however short a tail of the log is kept.
    const rejected = async (causes: string[]): Promise<ApplyResult> => {
      const notes = await restore();
      return { ok: false, log: finish(`${causes.join("\n")}\n[coordinate] every applied change was rolled back.`, notes) };
    };
    const stepFailure = (stop: VerifyStop): string =>
      `[coordinate] verify failed at '${stop.cmd}'; the end of its output:\n${stop.output.slice(-600)}`;

    for (const s of [build, index]) {
      const stop = await runStep(s, main, everyRecord);
      if (stop) return stop.end === "timedOut" ? preserved(stop.cmd) : await rejected([stepFailure(stop)]);
    }

    // Structural lints run after the index refresh so headline counts see the post-apply
    // declarations and sidecars.
    const structuralLints = async (sink: VerifyLog): Promise<void> => {
      const startedAt = new Date();
      const lines: string[] = [];
      try {
        const baseline = await loadLayoutBaseline(repoRoot, d);
        const relevantLayoutFindings = (await (d.lintLibraryLayout ?? lintLibraryLayout)(cRoot))
          .filter((finding) => !isSupersededMathlibHeadlineBan(finding))
          .filter((finding) => !baseline.has(layoutBaselineKey({
            ...finding,
            path: normalizeLintPath(cRoot, finding.path),
          })))
          // A sidecar rewrite can add a fourth headline to an otherwise untouched Lean file.
          .filter((finding) => finding.rule === "HEADLINES" || findingTouchesFiles(cRoot, finding.path, touchedLeanFiles));
        // Each lint's own CLI fails only on error severity; the gate follows that. Advisory findings
        // (the 600-line soft cap, whose >900 hard cap is a separate error) are reported and never block:
        // the rule they encode is "normally ≤600, split before ~900", and failing a promotion on one
        // sends the coordinator into split/merge churn. Partitioning AFTER the baseline and
        // touched-file filters keeps the advisory list scoped to this promotion, so the retry prompt
        // never sees the library's pre-existing backlog.
        const layoutFindings = relevantLayoutFindings.filter(isBlockingFinding);
        const layoutWarnings = relevantLayoutFindings.filter((finding) => !isBlockingFinding(finding));
        const headerLint = await (d.lintModuleHeaders ?? lintModuleHeaders)([...touchedLeanFiles], false);
        const headerFindings = headerLint.findings.filter(isBlockingFinding);
        const headerWarnings = headerLint.findings.filter((finding) => !isBlockingFinding(finding));
        lines.push(
          `[lint_library_layout] ${layoutFindings.length} unsuppressed finding(s) on ${touchedLeanFiles.size} touched Lean file(s)`
          + (layoutWarnings.length > 0
            ? `\n[lint_library_layout] ${layoutWarnings.length} advisory warning(s) (not blocking):\n  `
              + layoutWarnings.map(formatLayoutFinding).join("\n  ")
            : ""),
        );
        if (headerWarnings.length > 0) {
          lines.push(
            `[lint_module_headers] ${headerWarnings.length} advisory warning(s) (not blocking):\n  `
            + headerWarnings.map(formatHeaderFinding).join("\n  "),
          );
        }
        lines.push(
          `[lint_module_headers] ${headerFindings.length} finding(s) on ${touchedLeanFiles.size} touched Lean file(s)`,
        );
        if (layoutFindings.length > 0 || headerFindings.length > 0) {
          const headlineFiles = layoutFindings
            .filter((finding) => finding.rule === "HEADLINES")
            .map((finding) => normalizeLintPath(cRoot, finding.path));
          const details = [
            ...(headlineFiles.length > 0 ? [
              `OVER-CURATED THEOREM FILES (${headlineFiles.length}) — each file may have at most five matching headline_theorems entries:\n  ${headlineFiles.join("\n  ")}`,
            ] : []),
            ...layoutFindings.filter((finding) => finding.rule !== "HEADLINES").map(formatLayoutFinding),
            ...headerFindings.map(formatHeaderFinding),
          ];
          throw new Error(`post-apply structural lint failed:\n${details.join("\n")}`);
        }
      } finally {
        const took = seconds(Date.now() - startedAt.getTime());
        sink.sections.push([`[${startedAt.toISOString()}] structural lints (in-process)`, ...lines, `[done after ${took}]`].join("\n"));
        sink.timings.push(`structural-lints ${took}`);
      }
    };

    // The remaining steps only read the fresh index and write disjoint files — the embeddings
    // branch writes `doc/library_embeddings.*`, the docs branch writes `doc/API.md` — so the two
    // run side by side. A branch never throws: its error is carried to the join, so the verdict
    // (and any rollback, which rewrites files a live step may be reading) waits for both.
    const branch = async (
      body: (sink: VerifyLog) => Promise<VerifyStop | null>,
    ): Promise<{ log: VerifyLog; stop: VerifyStop | null; error?: unknown }> => {
      const log: VerifyLog = { sections: [], timings: [] };
      try {
        return { log, stop: await body(log) };
      } catch (error) {
        return { log, stop: null, error };
      }
    };
    // One check covers the first step of both branches, so the embedding command is already
    // running when the in-process lints start and occupy this process.
    await assertRecordsStable("post-index verify branches", everyRecord);
    const [embeddings, docs] = await Promise.all([
      // `doc/API.md` belongs to the docs branch, which rewrites it mid-flight; this branch
      // guards every other promoted record.
      branch(async (sink) =>
        (await runStep(embed, sink, null))
          ?? (await runStep(embedFresh, sink, (record) => record !== apiMd))),
      branch(async (sink) => {
        await structuralLints(sink);
        const stop = (await runStep(crosslinks, sink, everyRecord)) ?? (await runStep(docGen, sink, everyRecord));
        if (stop) return stop;
        // doc:gen legitimately rewrites the GEN regions of doc/API.md. Accept its output as the new
        // expectation only when everything outside those regions still equals the promoted bytes.
        const promotedApi = expectedRecordWrites.get(apiMd);
        if (promotedApi !== undefined) {
          const regenerated = await d.readFile(apiMd);
          if (maskGenRegions(regenerated) !== maskGenRegions(promotedApi)) {
            throw new Error(`promoted record changed before verify step 'npm run doc:check': ${apiMd}`);
          }
          expectedRecordWrites.set(apiMd, regenerated);
        }
        return runStep(docCheck, sink, everyRecord);
      }),
    ]);
    // Branch logs join embeddings-then-docs whichever finished first, except that a branch
    // which did not pass goes last, so the log ends on the output that explains the outcome.
    const passed = (b: typeof embeddings): boolean => b.stop === null && b.error === undefined;
    const branches = [embeddings, docs];
    for (const b of [...branches.filter(passed), ...branches.filter((x) => !passed(x))]) {
      main.sections.push(...b.log.sections);
      main.timings.push(`${b === embeddings ? "embeddings" : "docs"}[${b.log.timings.join("; ")}]`);
    }
    const errors = branches.flatMap((b) => (b.error === undefined ? [] : [b.error]));
    const stops = branches.flatMap((b) => (b.stop ? [b.stop] : []));
    const failed = stops.filter((stop) => stop.end === "failed");
    if (errors.length === 1 && failed.length === 0 && errors[0] instanceof LockAcquireError) throw errors[0];
    // A step that really failed settles the verdict, so it outranks a watchdog kill in the
    // other branch: both branches have exited, and the manifest is known to be wrong.
    if (errors.length > 0 || failed.length > 0) {
      return await rejected(branches.flatMap((b) => [
        ...(b.stop?.end === "failed" ? [stepFailure(b.stop)] : []),
        ...(b.error === undefined ? [] : [`[coordinate] apply error: ${b.error instanceof Error ? b.error.message : String(b.error)}`]),
      ]));
    }
    if (stops.length > 0) return preserved(stops[0].cmd);

    // Success — the substrate content now lives in Causalean; delete the staging
    // sources and clean up the now-empty Substrate dirs (best-effort).
    for (const f of leanFiles) await d.removeFile(f);
    if (d.removeDir) {
      const dirs = Array.from(new Set(leanFiles.map((f) => path.dirname(f))));
      for (const dir of dirs) {
        await d.removeDir(dir);
        await d.removeDir(path.dirname(dir));
      }
    }
    return { ok: true, log: finish(`[coordinate] applied ${manifest.ops.length} op(s).${manifest.notes ? `\nnotes: ${manifest.notes}` : ""}`) };
  } catch (err) {
    const notes = await restore();
    const msg = err instanceof Error ? err.message : String(err);
    if (err instanceof LockAcquireError) {
      return { ok: false, lockWait: true, log: finish(`[coordinate] lock wait, not a verdict: ${msg}; every applied change was rolled back.`, notes) };
    }
    return { ok: false, log: finish(`[coordinate] apply error: ${msg}`, notes) };
  }
}

// --- Orchestrator (one coordinate attempt: agent → apply) ----------------------

export interface CoordinateArgs {
  repoRoot: string;
  slug: string;
  leanDir: string;
  requirement: string;
  modulePrefix: string;
  runDir: string;
  leanFiles: string[];
  round: number;
  lastFailureLog: string | null;
  /** Prefer existing directory barrels when wiring newly created modules. */
  barrelTarget?: "root" | "directory";
}
export interface CoordinateDeps {
  runCoordinator: typeof runCoordinator;
  apply: typeof applyManifest;
  applyDeps?: CoordinateApplyDeps;
}

const realCoordinateDeps: CoordinateDeps = { runCoordinator, apply: applyManifest };

/**
 * One coordinate attempt: ask the coordinator for a manifest, then apply it
 * deterministically. Returns `{ ok, log }`; the pipeline owns the bounded retry
 * (feeding a failure log back on `ok === false`).
 */
export async function coordinate(
  args: CoordinateArgs,
  deps: CoordinateDeps = realCoordinateDeps,
): Promise<ApplyResult> {
  const stagingDir = path.join(args.runDir, "coordinate_staging", `round_${args.round}`);
  let manifest: CoordinationManifest;
  try {
    manifest = await deps.runCoordinator({
      repoRoot: args.repoRoot, runDir: args.runDir, round: args.round, slug: args.slug,
      requirement: args.requirement, leanDir: args.leanDir, modulePrefix: args.modulePrefix,
      leanFiles: args.leanFiles, stagingDir, lastFailureLog: args.lastFailureLog,
    });
  } catch (err) {
    const msg = err instanceof Error ? err.message : String(err);
    // A parse/agent failure is retryable: the pipeline feeds this back so codex
    // re-emits (the prompt already tells it to keep the JSON tiny + stage bodies).
    return { ok: false, log: `[coordinate] coordinator agent/parse failed: ${msg}` };
  }
  return deps.apply(
    {
      cRoot: causaleanRoot(args.repoRoot), repoRoot: args.repoRoot, stagingDir,
      leanFiles: args.leanFiles, manifest, slug: args.slug, modulePrefix: args.modulePrefix,
      barrelTarget: args.barrelTarget,
    },
    deps.applyDeps ?? realApplyDeps,
  );
}

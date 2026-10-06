// The promotion gate. Promotion only adds: it ADDS declarations to Causalean and leaves the
// banked run's Lean exactly as it was reviewed. Banking an accepted run records a snapshot in its
// entry (`recordSnapshot`); after a promotion `checkEntry` passes iff
//   (1) the run's Lean files are byte-identical to what was banked;
//   (2) every declaration of the run states what it stated (a new library instance or notation
//       can make unchanged text elaborate differently);
//   (3) every declaration outside the run that the run's statements USE states what it stated.
// "States" is a structural fingerprint of the compiled statement, and "uses" the closure of the
// dependency edges, both reported by the `statement_scan` exe (`CausalSmith/StatementScan.lean`): a
// definition, structure or instance is followed through its type and value, a theorem through its
// type only. Proofs are not followed — a changed lemma a run proof uses still proves it or breaks
// the build — and a declaration outside the closure is not compared at all, so a library edit
// elsewhere never fails the check.
import { execFile } from "node:child_process";
import { createHash } from "node:crypto";
import { existsSync } from "node:fs";
import { mkdir, mkdtemp, readdir, readFile, rename, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { promisify } from "node:util";
import { isPaperTmpPath } from "../paths.js";

const LIBRARY = "Causalean";

export interface ScanRow { name: string; kind: string; stmt_hash: string; module: string; deps: string[] }

/** The rows of a scan (one JSON object per line); a line that is not a row is dropped. Pure. */
export function parseScan(text: string): ScanRow[] {
  const rows: ScanRow[] = [];
  for (const line of text.split("\n")) {
    if (!line.trim()) continue;
    try {
      const d = JSON.parse(line) as Partial<ScanRow>;
      if (typeof d.name === "string" && typeof d.stmt_hash === "string") {
        rows.push({ name: d.name, kind: String(d.kind ?? ""), stmt_hash: d.stmt_hash, module: String(d.module ?? ""), deps: Array.isArray(d.deps) ? d.deps.map(String) : [] });
      }
    } catch { /* not a row */ }
  }
  return rows;
}

export interface TreeScan {
  /** Declaration → fingerprint. Private declarations of different modules may share a name:
   *  their fingerprints are joined, so a change to any of them changes the entry. */
  decls: Map<string, string>;
  /** Declaration → the scanned declarations its statement reads by name. */
  deps: Map<string, string[]>;
  /** The declarations of the run's own modules. */
  runDecls: string[];
}

/** A scan's rows as fingerprints and dependency edges; `ownModules` are the run's. Pure. */
export function readScan(text: string, ownModules: ReadonlySet<string>): TreeScan {
  const hashes = new Map<string, string[]>();
  const deps = new Map<string, Set<string>>();
  const run = new Set<string>();
  for (const r of parseScan(text)) {
    hashes.set(r.name, [...(hashes.get(r.name) ?? []), r.stmt_hash]);
    deps.set(r.name, new Set([...(deps.get(r.name) ?? []), ...r.deps]));
    if (ownModules.has(r.module)) run.add(r.name);
  }
  return {
    decls: new Map([...hashes].map(([name, hs]) => [name, hs.sort().join("+")])),
    deps: new Map([...deps].map(([name, ds]) => [name, [...ds].sort()])),
    runDecls: [...run],
  };
}

/**
 * The declarations outside the run that the run's statements use: everything reached from a run
 * declaration along the dependency edges. Each comes with up to three run declarations that reach
 * it, for the failure message. Pure.
 */
export function usedClosure(scan: Pick<TreeScan, "deps" | "runDecls">): Map<string, string[]> {
  const own = new Set(scan.runDecls);
  const users = new Map<string, string[]>();
  for (const root of [...scan.runDecls].sort()) {
    const seen = new Set<string>([root]);
    const stack = [root];
    while (stack.length > 0) {
      for (const d of scan.deps.get(stack.pop()!) ?? []) {
        if (seen.has(d)) continue;
        seen.add(d);
        if (!own.has(d)) {
          const u = users.get(d) ?? [];
          // three users already: every declaration below was reached by each of them too
          if (u.length >= 3) continue;
          users.set(d, [...u, root]);
        }
        stack.push(d);
      }
    }
  }
  return users;
}

// --- The run's files ------------------------------------------------------------------------

/** The Lake package directory a run's Lean dir belongs to (the nearest ancestor with a lakefile). */
export function packageRootOf(leanDir: string): string {
  let dir = path.resolve(leanDir);
  for (;;) {
    if (existsSync(path.join(dir, "lakefile.toml")) || existsSync(path.join(dir, "lakefile.lean"))) return dir;
    const up = path.dirname(dir);
    if (up === dir) throw new Error(`no lakefile above ${leanDir}`);
    dir = up;
  }
}

const posix = (p: string): string => p.split(path.sep).join("/");
const moduleOf = (relFile: string): string => relFile.slice(0, -".lean".length).split("/").join(".");

/** The run's Lean files, relative to its package root: every `.lean` file of its directory
 *  outside `tmp/` scratch folders, and the run's module file beside the directory. */
export async function runFiles(leanDir: string): Promise<string[]> {
  const pkg = packageRootOf(leanDir);
  const rel = posix(path.relative(pkg, path.resolve(leanDir)));
  const inside = (await readdir(leanDir, { recursive: true })).map(String).map(posix)
    .filter((f) => f.endsWith(".lean") && !isPaperTmpPath(f)).map((f) => `${rel}/${f}`);
  const barrel = `${rel}.lean`;
  return [...inside, ...(existsSync(path.join(pkg, barrel)) ? [barrel] : [])].sort();
}

/** sha256 of each of the run's Lean files, by path relative to the package root. */
export async function hashRunFiles(leanDir: string): Promise<Record<string, string>> {
  const pkg = packageRootOf(leanDir);
  const out: Record<string, string> = {};
  for (const f of await runFiles(leanDir)) out[f] = createHash("sha256").update(await readFile(path.join(pkg, f))).digest("hex");
  return out;
}

const RESTORE = "restore the run's Lean to its banked state and redo the promotion as a pure addition to Causalean";

/** (1): one line per run file that is not what was banked. Pure. */
export function fileFailures(before: Readonly<Record<string, string>>, after: Readonly<Record<string, string>>): string[] {
  const out: string[] = [];
  for (const f of Object.keys(before).sort()) {
    if (!(f in after)) out.push(`${f}: the file is gone — a promotion never edits the run; ${RESTORE}`);
    else if (after[f] !== before[f]) out.push(`${f}: the file changed — a promotion never edits the run; ${RESTORE}`);
  }
  for (const f of Object.keys(after).sort()) {
    if (!(f in before)) out.push(`${f}: the file was added to the run — a promotion never edits the run; remove it and redo the promotion as a pure addition to Causalean`);
  }
  return out;
}

/**
 * (2) and (3): one line per declaration that does not state what it stated at banking — the run's
 * own, and those outside it that its statements use (`used`: declaration → fingerprint and the run
 * declarations that reach it). Nothing else in `after` is looked at. Pure.
 */
/** Lean packages vendored in-tree (`third_party/`): path dependencies with no pinned revision, so
 *  their declarations are fingerprinted like the library's. */
const VENDORED = ["FoML", "Optlib"] as const;

export function statementFailures(
  before: { run: Readonly<Record<string, string>>; used: Readonly<Record<string, { hash: string; by: readonly string[] }>> },
  after: ReadonlyMap<string, string>,
): string[] {
  const out: string[] = [];
  for (const name of Object.keys(before.run).sort()) {
    const a = after.get(name);
    if (a === undefined) out.push(`${name}: this declaration of the run is no longer declared; ${RESTORE}`);
    else if (a !== before.run[name]) out.push(`${name}: this declaration of the run no longer states what it stated at banking, though its file may be unchanged (a new library instance, notation or simp lemma in a module the run imports can do that); move what this promotion added there to a module the run does not import, or remove it`);
  }
  for (const name of Object.keys(before.used).sort()) {
    const a = after.get(name);
    if (a !== undefined && a === before.used[name].hash) continue;
    out.push(
      `${name}: ${a === undefined ? "is no longer declared" : "no longer states what it stated at banking"}, and the run's statements use it (through ${before.used[name].by.join(", ")}). `
        + "If this promotion changed it, undo that change — a promotion only adds (an addition to a module it imports can also change it: then move the addition); if it did not, edit nothing, stop and report: something the paper relies on changed",
    );
  }
  return out;
}

// --- Scanning --------------------------------------------------------------------------------

/** The `lake` invocation that scans `modules` and everything they import, reporting the
 *  declarations of the modules under `prefixes`. Pure. */
export function scanCommand(args: { cwd: string; modules: readonly string[]; prefixes: readonly string[]; out: string }): { cmd: string; args: string[]; cwd: string } {
  return {
    cmd: "lake",
    cwd: args.cwd,
    args: ["exe", "statement_scan", "--modules", args.modules.join(","), "--prefixes", args.prefixes.join(","), "--out", posix(args.out)],
  };
}

const run = promisify(execFile);

/**
 * Scan the run's modules and what they import, as compiled now. Lake first confirms, without
 * building, that the run's modules — and so everything they import, and nothing else — are built
 * from their current sources; a library file the run does not import is never asked about.
 */
export async function scanTree(leanDir: string, out: string): Promise<TreeScan> {
  const pkg = packageRootOf(leanDir);
  const rel = posix(path.relative(pkg, path.resolve(leanDir)));
  // the run's module file beside the directory is hashed, not scanned: it only imports the others
  const modules = (await runFiles(leanDir)).filter((f) => f.startsWith(`${rel}/`)).map(moduleOf);
  if (modules.length === 0) throw new Error(`no Lean file under ${leanDir}`);
  const env = { ...process.env, PATH: `${process.env.PATH ?? ""}${path.delimiter}${path.join(process.env.HOME ?? "", ".elan", "bin")}` };
  try {
    await run("lake", ["build", "--no-build", ...modules], { cwd: pkg, maxBuffer: 256 * 1024 * 1024, env });
  } catch (err) {
    const e = err as { stdout?: string; stderr?: string; message?: string };
    const tail = `${e.stdout ?? ""}\n${e.stderr ?? ""}`.trim().split("\n").slice(-6).join("\n") || String(e.message ?? err);
    throw new Error(
      "the run, or a module it imports, is not built from its current sources. If the module named below is this run's or one this work edited, run the full build and retry. "
        + `If it is not, another session is editing it: wait and retry — do not build or revert it.\n${tail}`,
    );
  }
  await mkdir(path.dirname(out), { recursive: true });
  const c = scanCommand({ cwd: pkg, modules, prefixes: [LIBRARY, path.basename(pkg), ...VENDORED], out });
  if (!existsSync(path.join(pkg, ".lake", "build", "bin", "statement_scan"))) console.error("building statement_scan (first use)…");
  await run(c.cmd, c.args, { cwd: c.cwd, maxBuffer: 64 * 1024 * 1024, env });
  const scan = readScan(await readFile(out, "utf8"), new Set(modules));
  if (scan.runDecls.length === 0) throw new Error(`the scan reported no declaration of the run (${out})`);
  return scan;
}

/** The Lean toolchain and the Mathlib revision the run's package builds with (null when not
 *  recorded on disk): fingerprints are comparable only under the same pair. */
export async function buildBasis(pkg: string): Promise<{ toolchain: string | null; mathlib: string | null }> {
  const toolchain = await readFile(path.join(pkg, "lean-toolchain"), "utf8").then((t) => t.trim(), () => null);
  const mathlib = await readFile(path.join(pkg, "lake-manifest.json"), "utf8").then((t) => {
    const pkgs = (JSON.parse(t) as { packages?: { name?: string; rev?: string }[] }).packages ?? [];
    return pkgs.find((x) => x.name === "mathlib")?.rev ?? null;
  }, () => null);
  return { toolchain, mathlib };
}

/** Where the tree was when the snapshot was taken (information; nulls outside a git checkout). */
export async function gitState(leanDir: string): Promise<{ commit: string | null; lean_differs_from_commit: boolean | null }> {
  try {
    const git = async (...a: string[]) => (await run("git", a, { cwd: leanDir, maxBuffer: 64 * 1024 * 1024 })).stdout.trim();
    return { commit: await git("rev-parse", "HEAD"), lean_differs_from_commit: (await git("status", "--porcelain", "--", ".")) !== "" };
  } catch {
    return { commit: null, lean_differs_from_commit: null };
  }
}

/** The Lean directory of the run an entry records (`lean_subdir` of its state file), under
 *  `pkgRoot`. */
export async function entryLeanDir(entryDir: string, pkgRoot: string): Promise<string> {
  const files = (await readdir(entryDir)).filter((f) => f === "state.json" || f.endsWith("_state.json"));
  const file = files.includes("state.json") ? "state.json" : files.length === 1 ? files[0] : null;
  if (!file) throw new Error(`no state file in ${entryDir}`);
  const sub = (JSON.parse(await readFile(path.join(entryDir, file), "utf8")) as { lean_subdir?: unknown }).lean_subdir;
  if (typeof sub !== "string" || !sub) throw new Error(`${path.join(entryDir, file)} records no lean_subdir`);
  return path.join(pkgRoot, sub);
}

// --- Snapshot (taken at banking) and check ----------------------------------------------------

/** The snapshot's file in a bank entry. A raw run record: not committed. */
export const SNAPSHOT_FILE = "promotion_snapshot.json";

export interface Snapshot {
  schema: 2;
  /** The run's Lean directory, relative to its package root (`state.lean_subdir`). */
  lean_subdir: string;
  /** The commit the tree was at, and whether the run's Lean differed from it (null outside git). */
  commit: string | null;
  lean_differs_from_commit: boolean | null;
  /** The Lean toolchain and Mathlib revision the fingerprints were taken under. */
  toolchain: string | null;
  mathlib: string | null;
  /** sha256 of each of the run's Lean files, by path relative to the package root. */
  files: Record<string, string>;
  /** The run's declarations → fingerprint. */
  run: Record<string, string>;
  /** The declarations outside the run that its statements use → fingerprint, and up to three run
   *  declarations that reach each. */
  used: Record<string, { hash: string; by: string[] }>;
}

export interface ScanDeps { scan: typeof scanTree }

/** What the run's files hold, what its declarations state and what the declarations they use
 *  state — all on the Lean as it stands. */
export async function takeSnapshot(args: { leanDir: string }, deps: ScanDeps = { scan: scanTree }): Promise<Snapshot> {
  const tmp = await mkdtemp(path.join(tmpdir(), "statement-scan-"));
  try {
    const files = await hashRunFiles(args.leanDir);
    const scan = await deps.scan(args.leanDir, path.join(tmp, "scan.jsonl"));
    const pkg = packageRootOf(args.leanDir);
    return {
      schema: 2,
      lean_subdir: posix(path.relative(pkg, path.resolve(args.leanDir))),
      ...(await gitState(args.leanDir)),
      ...(await buildBasis(pkg)),
      files,
      run: Object.fromEntries([...scan.runDecls].sort().map((n) => [n, scan.decls.get(n)!])),
      used: Object.fromEntries([...usedClosure(scan)].sort(([a], [b]) => a.localeCompare(b)).map(([n, by]) => [n, { hash: scan.decls.get(n) ?? "", by }])),
    };
  } finally {
    await rm(tmp, { recursive: true, force: true });
  }
}

/**
 * Record the snapshot of a run in its entry directory. Banking calls this for an accepted research
 * run, on the Lean that was just reviewed and before anything is moved, so a failure (a module not
 * built from its sources, a scan error) fails the banking with nothing changed. The snapshot is
 * written once: an existing one is replaced only when `replace` is set — banking sets it for an
 * entry that was reopened and re-verified, never otherwise.
 */
export async function recordSnapshot(args: { entryDir: string; leanDir: string; replace?: boolean }, deps: ScanDeps = { scan: scanTree }): Promise<Snapshot> {
  const file = path.join(args.entryDir, SNAPSHOT_FILE);
  if (existsSync(file) && !args.replace) {
    throw new Error(`${file} already exists: the statement snapshot of a banked run is written once. It is replaced only when a reopened entry is banked again.`);
  }
  const snap = await takeSnapshot({ leanDir: args.leanDir }, deps);
  const tmp = `${file}.${process.pid}.tmp`; // temp file + rename: a killed banking never leaves half a snapshot
  await writeFile(tmp, `${JSON.stringify(snap)}\n`, "utf8");
  await rename(tmp, file);
  return snap;
}

/**
 * After a promotion and a full build, against the snapshot banking recorded in `entryDir`: one
 * line per run file or declaration that is not what it was (empty = the promotion changed nothing
 * the paper states). Changed files are reported without scanning. Writes nothing. `pkgRoot` is the
 * run's Lake package directory.
 */
export async function checkEntry(args: { entryDir: string; pkgRoot: string }, deps: ScanDeps = { scan: scanTree }): Promise<{ snapshot: Snapshot; failures: string[] }> {
  const file = path.join(args.entryDir, SNAPSHOT_FILE);
  if (!existsSync(file)) {
    throw new Error(
      `${args.entryDir} has no ${SNAPSHOT_FILE}. Banking at the accepted tier records it; an entry with no snapshot cannot have its promotion checked. `
        + "Do not promote it: the operator — never the promoting agent — records one on the committed, not yet promoted run "
        + "(`npm run promotion:invariance -- snapshot --entry <bank entry dir>`).",
    );
  }
  let snapshot: Snapshot;
  try {
    snapshot = JSON.parse(await readFile(file, "utf8")) as Snapshot;
    if (snapshot.schema !== 2 || typeof snapshot.lean_subdir !== "string" || !snapshot.files || !snapshot.run || !snapshot.used) throw new Error("not a schema-2 snapshot");
  } catch (err) {
    throw new Error(`${file} is not a readable statement snapshot (${err instanceof Error ? err.message : String(err)}). It is never edited by hand: the operator removes it and records a new one on the committed, not yet promoted run.`);
  }
  const now = await buildBasis(args.pkgRoot);
  if ((snapshot.toolchain ?? null) !== now.toolchain || (snapshot.mathlib ?? null) !== now.mathlib) {
    throw new Error(
      `the snapshot was taken under Lean ${snapshot.toolchain ?? "?"} and Mathlib ${snapshot.mathlib ?? "?"}; the tree is now at Lean ${now.toolchain ?? "?"} and Mathlib ${now.mathlib ?? "?"}. `
        + "Fingerprints are not comparable across a toolchain or Mathlib change: the entry needs a new snapshot, recorded by the operator on the unpromoted run.",
    );
  }
  const leanDir = path.join(args.pkgRoot, snapshot.lean_subdir);
  const changedFiles = fileFailures(snapshot.files, existsSync(leanDir) ? await hashRunFiles(leanDir) : {});
  if (changedFiles.length > 0) return { snapshot, failures: changedFiles };
  const tmp = await mkdtemp(path.join(tmpdir(), "statement-scan-"));
  try {
    const scan = await deps.scan(leanDir, path.join(tmp, "scan.jsonl"));
    return { snapshot, failures: statementFailures(snapshot, scan.decls) };
  } finally {
    await rm(tmp, { recursive: true, force: true });
  }
}

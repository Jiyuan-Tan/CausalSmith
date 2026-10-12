// What Lean elaborated, as the F4 receipt cache reads it. The `statement_scan` exe
// (`CausalSmith/StatementScan.lean`, run through `scanTree`) reports every declaration of
// Causalean, CausalSmith and the vendored packages with a structural fingerprint of what it states
// (a theorem by its type; a definition by its type and value; a structure by its constructor types
// and field names) and the scanned declarations that statement reads by name. The CLOSURE HASH of
// a declaration folds its fingerprint with those of everything it reaches along those edges. It
// moves exactly when one of those statements does: not with a proof, a comment, a docstring, an
// `open`, a `set_option`, a `variable` line, an import, a binder name, or a declaration the
// statement does not reach — and it does move with a named instance or a Causalean definition the
// statement elaborates through, which no reading of the run's text can see.
//
// The scan reads compiled modules, so it is taken once per graph refresh of the proof-review loop,
// F4 entry, F5 audit or banking, after the compile gate, and refused (null) on a tree whose oleans
// are not built from its sources.
import { createHash } from "node:crypto";
import { mkdtemp, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { withLakeBuildLock } from "../shared/build_mutex.js";
import { buildBasis, packageRootOf, scanTree, type TreeScan } from "../substrate/invariance.js";

export interface BuildBasis { toolchain: string | null; mathlib: string | null }

export interface StatementFingerprints {
  scan: TreeScan;
  /** The run's Lean dir as a module prefix (`CausalSmith.Stat.X_Research`): a graph anchor's
   *  `file` (relative to that dir) names the module `<prefix>.<file without .lean>`. */
  modulePrefix: string;
  /** The toolchain and Mathlib revision the scan was taken under: library constants are read by
   *  name, so a change of either is a change of what every statement may mean. */
  basis: BuildBasis;
  /** Last name segment → every scanned declaration carrying it. */
  byShort: Map<string, string[]>;
  /** Closure hashes computed so far. */
  closures: Map<string, string>;
}

const lastSegment = (name: string): string => name.split(".").filter(Boolean).pop() ?? "";

/** The fingerprints of a scan, ready to be read. Pure. */
export function statementFingerprints(scan: TreeScan, modulePrefix: string, basis: BuildBasis): StatementFingerprints {
  const byShort = new Map<string, string[]>();
  for (const name of scan.decls.keys()) {
    const s = lastSegment(name);
    if (!byShort.has(s)) byShort.set(s, []);
    byShort.get(s)!.push(name);
  }
  return { scan, modulePrefix, basis, byShort, closures: new Map() };
}

/** The module a file of the run's Lean dir compiles to. */
const moduleOfFile = (fp: StatementFingerprints, file: string): string =>
  `${fp.modulePrefix}.${file.replace(/\\/g, "/").replace(/\.lean$/, "").split("/").join(".")}`;

/** The scanned declarations an anchor names: the declared name, or either a namespace-qualified
 *  form of the other; in `file` (relative to the run's Lean dir) when the anchor has one. */
export function resolveDecls(fp: StatementFingerprints, declName: string, file: string | null): string[] {
  const module = file ? moduleOfFile(fp, file) : null;
  return (fp.byShort.get(lastSegment(declName)) ?? []).filter((c) =>
    (c === declName || declName.endsWith(`.${c}`) || c.endsWith(`.${declName}`)) &&
    (!module || (fp.scan.modules.get(c) ?? []).includes(module)));
}

/** Every scanned declaration of `file` (relative to the run's Lean dir). */
export function declsInFile(fp: StatementFingerprints, file: string): string[] {
  const module = moduleOfFile(fp, file);
  return [...fp.scan.modules].filter(([, ms]) => ms.includes(module)).map(([name]) => name).sort();
}

/** What `name` states together with everything its statement rests on, as one hash: the
 *  fingerprint of `name` and of every scanned declaration reachable from it, each under its name,
 *  in name order. */
export function closureHash(fp: StatementFingerprints, name: string): string {
  const known = fp.closures.get(name);
  if (known !== undefined) return known;
  const seen = new Set<string>([name]);
  const stack = [name];
  while (stack.length > 0) {
    for (const d of fp.scan.deps.get(stack.pop()!) ?? []) {
      if (!seen.has(d)) { seen.add(d); stack.push(d); }
    }
  }
  const h = createHash("sha1").update(JSON.stringify([...seen].sort().map((m) => [m, fp.scan.decls.get(m) ?? null]))).digest("hex");
  fp.closures.set(name, h);
  return h;
}

/**
 * The fingerprints of the run in `leanDir` as its package is built now: one `statement_scan` under
 * the lake lock, with Lake first confirming that the run's modules are built from their sources.
 * Null, with one `[fingerprints]` line saying why, when they cannot be had — a stale or red tree, a missing
 * exe, a lock that does not come free: every governed target is then reviewed, and no receipt is
 * written for it.
 */
export async function takeStatementFingerprints(leanDir: string): Promise<StatementFingerprints | null> {
  const none = (why: string): null => {
    console.warn(`[fingerprints] statement fingerprints unavailable — targets are compared by source text, every governed target is reviewed and none is receipted: ${why}`);
    return null;
  };
  let tmp: string | null = null;
  try {
    const pkg = packageRootOf(leanDir);
    const modulePrefix = path.relative(pkg, path.resolve(leanDir)).split(path.sep).join(".");
    tmp = await mkdtemp(path.join(tmpdir(), "statement-scan-"));
    const out = path.join(tmp, "scan.jsonl");
    // A busy lock (another run's build) is given the ordinary retry budget only: without the scan
    // the pass compares source text, which costs less than a long wait on every refresh.
    const scan = await withLakeBuildLock(pkg, () => scanTree(leanDir, out));
    return statementFingerprints(scan, modulePrefix, await buildBasis(pkg));
  } catch (err) {
    return none(err instanceof Error ? err.message : String(err));
  } finally {
    if (tmp) await rm(tmp, { recursive: true, force: true }).catch(() => {});
  }
}

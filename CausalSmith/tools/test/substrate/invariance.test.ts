import { afterEach, beforeEach, describe, expect, it } from "vitest";
import { execFileSync } from "node:child_process";
import { existsSync } from "node:fs";
import { chmod, mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import {
  checkEntry,
  entryLeanDir,
  fileFailures,
  hashRunFiles,
  readScan,
  recordSnapshot,
  scanCommand,
  scanTree,
  SNAPSHOT_FILE,
  statementFailures,
  usedClosure,
  type TreeScan,
} from "../../src/substrate/invariance.js";

type Row = [name: string, hash: string, deps?: string[], module?: string];
const scanText = (rows: Row[]) => rows.map(([name, stmt_hash, deps = [], module = name.startsWith("Run.") ? "Pkg.Run.Main" : "Causalean.X"]) => JSON.stringify({ name, kind: "def", stmt_hash, module, deps })).join("\n");
const scanOf = (rows: Row[]): TreeScan => readScan(scanText(rows), new Set(["Pkg.Run.Main"]));

/** A run whose theorem uses `Lib.a` directly and `Lib.c` through two definitions; `Lib.far` is in
 *  the library but not used; `Lib.lemma` would only be used by a run proof, so no edge leads to it. */
const BASE: Row[] = [
  ["Run.main", "1", ["Lib.a", "Run.helper"]],
  ["Run.helper", "2", ["Lib.b"]],
  ["Lib.a", "10"],
  ["Lib.b", "11", ["Lib.c"]],
  ["Lib.c", "12"],
  ["Lib.far", "13", ["Lib.c"]],
  ["Lib.lemma", "14"],
];
const change = (name: string, hash: string): Row[] => BASE.map((r) => (r[0] === name ? [name, hash, r[2]] : r));

describe("what a run's statements use", () => {
  it("is the closure of the dependency edges from the run's declarations, each with the run declarations that reach it", () => {
    const used = usedClosure(scanOf(BASE));
    expect(Object.fromEntries(used)).toEqual({ "Lib.a": ["Run.main"], "Lib.b": ["Run.helper", "Run.main"], "Lib.c": ["Run.helper", "Run.main"] });
  });

  it("reads a scan's rows, joining private declarations that share a name", () => {
    const s = readScan(scanText([["Run.a", "7", ["Lib.x"]], ["Run.a", "3", ["Lib.y"]], ["Lib.x", "1"]]), new Set(["Pkg.Run.Main"]));
    expect(s.decls.get("Run.a")).toBe("3+7");
    expect(s.deps.get("Run.a")).toEqual(["Lib.x", "Lib.y"]);
    expect(s.runDecls).toEqual(["Run.a"]);
    expect(readScan("not json", new Set()).decls.size).toBe(0);
  });

  it("scans the run's modules and reports both packages", () => {
    expect(scanCommand({ cwd: "/pkg", modules: ["Pkg.Run.A", "Pkg.Run.B"], prefixes: ["Causalean", "Pkg"], out: "/tmp/o.jsonl" }))
      .toEqual({ cmd: "lake", cwd: "/pkg", args: ["exe", "statement_scan", "--modules", "Pkg.Run.A,Pkg.Run.B", "--prefixes", "Causalean,Pkg", "--out", "/tmp/o.jsonl"] });
  });
});

describe("the promotion check", () => {
  let pkg = "";
  const entry = () => path.join(pkg, "entry");
  const leanDir = () => path.join(pkg, "Pkg", "Run");
  const at = (rows: Row[]) => ({ scan: async () => scanOf(rows) });
  const check = (rows: Row[]) => checkEntry({ entryDir: entry(), pkgRoot: pkg }, at(rows)).then((r) => r.failures);

  beforeEach(async () => {
    pkg = await mkdtemp(path.join(tmpdir(), "promo-check-"));
    await mkdir(path.join(leanDir(), "Helpers"), { recursive: true });
    await mkdir(path.join(leanDir(), "tmp"));
    await mkdir(entry());
    await writeFile(path.join(pkg, "lakefile.toml"), 'name = "Pkg"\n');
    await writeFile(path.join(pkg, "lean-toolchain"), "leanprover/lean4:v9\n");
    await writeFile(path.join(pkg, "lake-manifest.json"), JSON.stringify({ packages: [{ name: "mathlib", rev: "abc" }] }));
    await writeFile(path.join(pkg, "Pkg", "Run.lean"), "import Pkg.Run.Main\n");
    await writeFile(path.join(leanDir(), "Main.lean"), "theorem main : True := trivial\n");
    await writeFile(path.join(leanDir(), "Helpers", "H.lean"), "def helper : Nat := 1\n");
    await writeFile(path.join(leanDir(), "tmp", "probe.lean"), "-- scratch\n");
    await writeFile(path.join(entry(), "state.json"), JSON.stringify({ lean_subdir: "Pkg/Run" }));
  });
  afterEach(async () => {
    await rm(pkg, { recursive: true, force: true });
  });

  it("records, once, the run's file hashes, its declarations and only the declarations they use", async () => {
    const snap = await recordSnapshot({ entryDir: entry(), leanDir: leanDir() }, at(BASE));
    expect(JSON.parse(await readFile(path.join(entry(), SNAPSHOT_FILE), "utf8"))).toEqual(snap);
    expect(snap).toMatchObject({ schema: 2, lean_subdir: "Pkg/Run", toolchain: "leanprover/lean4:v9", mathlib: "abc", run: { "Run.helper": "2", "Run.main": "1" } });
    expect(Object.keys(snap.files)).toEqual(["Pkg/Run.lean", "Pkg/Run/Helpers/H.lean", "Pkg/Run/Main.lean"]); // `tmp/` scratch is not the run
    expect(Object.keys(snap.used)).toEqual(["Lib.a", "Lib.b", "Lib.c"]);
    expect(await entryLeanDir(entry(), pkg)).toBe(leanDir());
    // a second snapshot never replaces the first, unless the entry was reopened
    const bytes = await readFile(path.join(entry(), SNAPSHOT_FILE), "utf8");
    await expect(recordSnapshot({ entryDir: entry(), leanDir: leanDir() }, at(change("Run.main", "9")))).rejects.toThrow(/written once/);
    expect(await readFile(path.join(entry(), SNAPSHOT_FILE), "utf8")).toBe(bytes);
    expect((await recordSnapshot({ entryDir: entry(), leanDir: leanDir(), replace: true }, at(change("Run.main", "9")))).run["Run.main"]).toBe("9");
  });

  it("passes when nothing the paper states changed — whatever else the library gained or changed", async () => {
    await recordSnapshot({ entryDir: entry(), leanDir: leanDir() }, at(BASE));
    expect(await check(BASE)).toEqual([]);
    await writeFile(path.join(leanDir(), "tmp", "probe.lean"), "-- other scratch\n"); // scratch is not compared
    expect(await check([...BASE, ["Lib.promotedCopy", "99", ["Lib.c"]]])).toEqual([]); // a library declaration ADDED
    expect(await check(change("Lib.far", "CHANGED"))).toEqual([]); // changed, but outside what the run uses
    expect(await check(change("Lib.lemma", "CHANGED"))).toEqual([]); // a lemma only a run PROOF uses
    expect(await check(BASE.filter((r) => r[0] !== "Lib.far"))).toEqual([]); // removed, and not used
  });

  it("fails on a changed, missing or added run file, naming it, without scanning", async () => {
    await recordSnapshot({ entryDir: entry(), leanDir: leanDir() }, at(BASE));
    const noScan = { scan: async (): Promise<TreeScan> => { throw new Error("must not scan"); } };
    await writeFile(path.join(leanDir(), "Main.lean"), "theorem main : True := by trivial\n");
    await rm(path.join(leanDir(), "Helpers", "H.lean"));
    await writeFile(path.join(leanDir(), "New.lean"), "def extra : Nat := 0\n");
    const r = await checkEntry({ entryDir: entry(), pkgRoot: pkg }, noScan);
    expect(r.failures).toEqual([
      "Pkg/Run/Helpers/H.lean: the file is gone — a promotion never edits the run; restore the run's Lean to its banked state and redo the promotion as a pure addition to Causalean",
      "Pkg/Run/Main.lean: the file changed — a promotion never edits the run; restore the run's Lean to its banked state and redo the promotion as a pure addition to Causalean",
      "Pkg/Run/New.lean: the file was added to the run — a promotion never edits the run; remove it and redo the promotion as a pure addition to Causalean",
    ]);
    expect(fileFailures({ a: "1" }, { a: "1" })).toEqual([]);
  });

  it("fails when a run declaration states something else although its file is unchanged", async () => {
    await recordSnapshot({ entryDir: entry(), leanDir: leanDir() }, at(BASE));
    expect(await check(change("Run.main", "CHANGED"))).toEqual([
      "Run.main: this declaration of the run no longer states what it stated at banking, though its file may be unchanged (a new library instance, notation or simp lemma in a module the run imports can do that); move what this promotion added there to a module the run does not import, or remove it",
    ]);
  });

  it("fails when a library declaration the run's statements use changed — directly or two definitions down — and names who uses it", async () => {
    await recordSnapshot({ entryDir: entry(), leanDir: leanDir() }, at(BASE));
    const tail = "If this promotion changed it, undo that change — a promotion only adds (an addition to a module it imports can also change it: then move the addition); if it did not, edit nothing, stop and report: something the paper relies on changed";
    expect(await check(change("Lib.a", "CHANGED"))).toEqual([`Lib.a: no longer states what it stated at banking, and the run's statements use it (through Run.main). ${tail}`]);
    expect(await check(change("Lib.c", "CHANGED"))).toEqual([`Lib.c: no longer states what it stated at banking, and the run's statements use it (through Run.helper, Run.main). ${tail}`]);
    expect(await check(BASE.filter((r) => r[0] !== "Lib.b"))).toEqual([`Lib.b: is no longer declared, and the run's statements use it (through Run.helper, Run.main). ${tail}`]);
    expect(statementFailures({ run: {}, used: {} }, new Map())).toEqual([]);
  });

  it("refuses an entry with no snapshot, an unreadable one, and one taken under another toolchain", async () => {
    await expect(check(BASE)).rejects.toThrow(/has no promotion_snapshot\.json\. Banking at the accepted tier records it/);
    await writeFile(path.join(entry(), SNAPSHOT_FILE), '{"schema":2,"files":');
    await expect(check(BASE)).rejects.toThrow(/is not a readable statement snapshot/);
    await rm(path.join(entry(), SNAPSHOT_FILE));
    await recordSnapshot({ entryDir: entry(), leanDir: leanDir() }, at(BASE));
    await writeFile(path.join(pkg, "lean-toolchain"), "leanprover/lean4:v10\n");
    await expect(check(BASE)).rejects.toThrow(/taken under Lean leanprover\/lean4:v9 .* now at Lean leanprover\/lean4:v10 .*not comparable/);
  });

  it("asks Lake only about the run's modules, and says whose a stale module is", async () => {
    const PATH0 = process.env.PATH;
    const bin = path.join(pkg, "fakebin");
    await mkdir(bin);
    // a stand-in `lake`: records its arguments, and reports a stale build
    await writeFile(path.join(bin, "lake"), `#!/bin/sh\necho "$*" >> "${path.join(pkg, "lake.args")}"\necho "Causalean.Y is out-of-date" >&2\nexit 1\n`);
    await chmod(path.join(bin, "lake"), 0o755);
    process.env.PATH = `${bin}${path.delimiter}${PATH0 ?? ""}`;
    try {
      await expect(scanTree(leanDir(), path.join(pkg, "out.jsonl"))).rejects.toThrow(/is not built from its current sources\. If the module named below is this run's .* run the full build and retry\. If it is not, another session is editing it: wait and retry — do not build or revert it\.\nCausalean\.Y is out-of-date/);
      expect((await readFile(path.join(pkg, "lake.args"), "utf8")).trim()).toBe("build --no-build Pkg.Run.Helpers.H Pkg.Run.Main");
    } finally {
      process.env.PATH = PATH0;
    }
  });

  it("hashes exactly the run's Lean files", async () => {
    const h = await hashRunFiles(leanDir());
    expect(Object.keys(h)).toEqual(["Pkg/Run.lean", "Pkg/Run/Helpers/H.lean", "Pkg/Run/Main.lean"]);
    expect(h["Pkg/Run/Main.lean"]).toMatch(/^[0-9a-f]{64}$/);
  });
});

// --- The real scan (needs the built `statement_scan` exe and the project's Lean toolchain) -----

const PKG = path.resolve(import.meta.dirname, "..", "..", "..");
const BIN = path.join(PKG, ".lake", "build", "bin", "statement_scan");
const TOOLCHAIN = (() => {
  if (!existsSync(BIN)) return ""; // no built exe: do not ask elan for a toolchain either
  try {
    const env = { ...process.env, PATH: `${path.join(process.env.HOME ?? "", ".elan", "bin")}${path.delimiter}${process.env.PATH ?? ""}` };
    return execFileSync("lean", ["--print-prefix"], { cwd: PKG, env, encoding: "utf8", stdio: ["ignore", "pipe", "ignore"] }).trim();
  } catch {
    return "";
  }
})();

describe.skipIf(!TOOLCHAIN)("statement_scan on compiled modules (requires the built exe)", () => {
  let dir = "";
  const env = () => ({ ...process.env, PATH: `${path.join(TOOLCHAIN, "bin")}${path.delimiter}${process.env.PATH ?? ""}`, LD_LIBRARY_PATH: path.join(TOOLCHAIN, "lib", "lean") });
  /** Compile `files` (module name → source, in import order) into their own directory and scan
   *  the run module(s) `run`, reporting every module of `files`. */
  async function scan(version: string, files: Record<string, string>, run = "Pkg.Run"): Promise<TreeScan> {
    const root = path.join(dir, version);
    await mkdir(root);
    for (const [mod, text] of Object.entries(files)) {
      const rel = mod.split(".").join("/");
      await mkdir(path.dirname(path.join(root, rel)), { recursive: true });
      await writeFile(path.join(root, `${rel}.lean`), text);
      execFileSync("lean", ["-o", `${rel}.olean`, `${rel}.lean`], { cwd: root, env: { ...env(), LEAN_PATH: root }, stdio: "pipe" });
    }
    const out = path.join(root, "scan.jsonl");
    execFileSync(BIN, ["--modules", run, "--prefixes", "Causalean,Pkg", "--out", out], { env: { ...env(), LEAN_PATH: root }, stdio: "pipe" });
    return readScan(await readFile(out, "utf8"), new Set(run.split(",")));
  }
  /** The check's (2) and (3), between two scans. */
  const failures = (before: TreeScan, after: TreeScan): string[] => {
    const used = Object.fromEntries([...usedClosure(before)].map(([n, by]) => [n, { hash: before.decls.get(n)!, by }]));
    const run = Object.fromEntries(before.runDecls.map((n) => [n, before.decls.get(n)!]));
    return statementFailures({ run, used }, after.decls).map((l) => l.split(":")[0]);
  };

  beforeEach(async () => {
    dir = await mkdtemp(path.join(tmpdir(), "statement-scan-"));
  });
  afterEach(async () => {
    await rm(dir, { recursive: true, force: true });
  });

  const LIB = (v: { weight?: string; base?: string; far?: string; lemma?: string; extra?: string } = {}) => [
    "namespace Causalean",
    `def base (n : Nat) : Nat := ${v.base ?? "n + 1"}`,
    `def weight (n : Nat) : Nat := ${v.weight ?? "base n + base n"}`,
    `def far (n : Nat) : Nat := ${v.far ?? "n"}`,
    `theorem weight_pos (n : Nat) ${v.lemma ?? "(_h : 0 ≤ n)"} : 0 < weight n := by unfold weight base; omega`,
    v.extra ?? "",
    "end Causalean",
  ].join("\n");
  const RUN = (proof = "Causalean.weight_pos n (Nat.zero_le n)") => ["import Causalean.X", "namespace Pkg.Run", "def score (n : Nat) : Nat := Causalean.weight n", `theorem main (n : Nat) : 0 < score n := ${proof}`, "end Pkg.Run"].join("\n");

  const REPROOF = "by unfold score; exact Causalean.weight_pos n (Nat.zero_le _)";

  it("compares the run and what its statements use, and nothing else", async () => {
    const before = await scan("before", { "Causalean.X": LIB(), "Pkg.Run": RUN() });
    expect([...usedClosure(before).keys()].sort()).toEqual(["Causalean.base", "Causalean.weight"]);
    // a re-proof of the run theorem, an added library declaration, a change to an unused definition,
    // and a restated lemma only the run's proof uses: none is a failure
    expect(failures(before, await scan("reproved", { "Causalean.X": LIB(), "Pkg.Run": RUN(REPROOF) }))).toEqual([]);
    expect(failures(before, await scan("added", { "Causalean.X": LIB({ extra: "theorem weight_pos' (n : Nat) : 0 < weight n := by unfold weight base; omega" }), "Pkg.Run": RUN() }))).toEqual([]);
    expect(failures(before, await scan("far", { "Causalean.X": LIB({ far: "n + 7" }), "Pkg.Run": RUN() }))).toEqual([]);
    expect(failures(before, await scan("lemma", { "Causalean.X": LIB({ lemma: "(_h : 0 ≤ n + 0)" }), "Pkg.Run": RUN("Causalean.weight_pos n (Nat.zero_le _)") }))).toEqual([]);
    // the definition the run's statement uses changes — directly, and two definitions down
    expect(failures(before, await scan("weight", { "Causalean.X": LIB({ weight: "base n + base n + 0" }), "Pkg.Run": RUN(REPROOF) }))).toEqual(["Causalean.weight"]);
    expect(failures(before, await scan("base", { "Causalean.X": LIB({ base: "n + 2" }), "Pkg.Run": RUN(REPROOF) }))).toEqual(["Causalean.base"]);
  }, 180_000);

  it("reads the body of a definition a `module` file does not expose, in the closure", async () => {
    const lib = (body: string) => ["module", "", "/-! fixture -/", "", "public section", "", `@[no_expose] def Causalean.hid : Nat := ${body}`, "", "@[expose] def Causalean.shown : Nat := 7"].join("\n");
    const run = ["module", "", "public import Causalean.X", "", "/-! fixture -/", "", "public section", "", "theorem Pkg.Run.t : Causalean.hid = Causalean.hid := rfl"].join("\n");
    const before = await scan("before", { "Causalean.X": lib("1"), "Pkg.Run": run });
    expect([...usedClosure(before).keys()]).toEqual(["Causalean.hid"]);
    expect(failures(before, await scan("same", { "Causalean.X": lib("1"), "Pkg.Run": run }))).toEqual([]);
    expect(failures(before, await scan("after", { "Causalean.X": lib("2"), "Pkg.Run": run }))).toEqual(["Causalean.hid"]);
  }, 120_000);

  it("finds every change behind a name: read by content it changes the fingerprint, read by name it is a dependency with a row", async () => {
    // each run theorem mentions one library constant of an awkward kind; `v` changes what is behind each
    const lib = (v: number, swap: boolean, ax: boolean) => [
      "namespace Causalean",
      `def match_weight : Nat := ${v}`,              // named like an auxiliary
      `def Foo.mk : Nat := ${v}`,                    // named like a constructor
      `private def secret : Nat := ${v}`,            // private
      "def viaSecret : Nat := secret",
      `def pick : Nat → Nat | 0 => ${v} | n + 1 => n`, // behind a compiler-generated matcher
      "structure Bd where",
      swap ? "  lower : Nat\n  upper : Nat" : "  upper : Nat\n  lower : Nat",
      `inductive Col | red | green (n : ${v === 1 ? "Nat" : "Int"})`,
      ax ? "axiom fact : 1 = 1" : "theorem fact : 1 = 1 := rfl",
      "structure Thing where",
      "  claim : fact = fact",
      "end Causalean",
    ].join("\n");
    const run = [
      "import Causalean.X", "namespace Pkg.Run", "open Causalean",
      "theorem usesAuxNamed : match_weight = match_weight := rfl",
      "theorem usesMk : Foo.mk = Foo.mk := rfl",
      "theorem usesPrivate : viaSecret = viaSecret := rfl",
      "theorem usesMatcher : pick 0 = pick 0 := rfl",
      "theorem usesProjection (b : Bd) : b.upper = b.upper := rfl",
      "theorem usesConstructor : Col.red = Col.red := rfl",
      "def usesAxiom : Prop := Thing",
      "theorem untouched : True := trivial",
      "end Pkg.Run",
    ].join("\n");
    const before = await scan("before", { "Causalean.X": lib(1, false, false), "Pkg.Run": run });
    // names and dependencies coincide: every dependency edge leads to a row
    for (const ds of before.deps.values()) for (const d of ds) expect(before.decls.has(d), d).toBe(true);
    const after = await scan("after", { "Causalean.X": lib(2, true, true), "Pkg.Run": run });
    const changed = new Set(failures(before, after));
    // read by content: the run declaration's own fingerprint moves
    expect([...changed].filter((n) => n.startsWith("Pkg.Run.")).sort()).toEqual(["Pkg.Run.usesAuxNamed", "Pkg.Run.usesMk"]);
    // read by name: the row behind the name is in the closure and is reported
    expect([...changed].filter((n) => n.startsWith("Causalean.")).sort()).toEqual(["Causalean.Bd", "Causalean.Col", "Causalean.fact", "Causalean.pick", "Causalean.viaSecret"]);
  }, 120_000);
});

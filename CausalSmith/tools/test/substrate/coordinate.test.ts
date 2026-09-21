// CausalSmith/tools/test/substrate/coordinate.test.ts
import { access, mkdir, mkdtemp, readFile, rm, rmdir, unlink, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { describe, it, expect, vi } from "vitest";
import {
  applyInsertOnly, applyManifest, insertImportSorted, type CoordinateApplyDeps,
} from "../../src/substrate/coordinate.js";
import type { CoordinationManifest } from "../../src/substrate/types.js";

/** In-memory fs + fake integration runner. `failStep` (a substring) makes the
 *  matching gate command return a nonzero code, triggering rollback. */
function memFs(initial: Record<string, string>) {
  const files = new Map<string, string>(Object.entries(initial));
  const runLog: string[] = [];
  const writeLog: string[] = [];
  let failStep: string | null = null;
  let timeoutStep: string | null = null;
  // The fixture keys are written `/`-separated, but the code under test composes paths
  // with `path.join`, which emits `\` on Windows — so every lookup missed there and the
  // real assertions were masked by "apply error: ENOENT". Key on one spelling instead.
  const key = (p: string): string => p.split(path.sep).join("/");
  const deps: CoordinateApplyDeps = {
    run: async (cmd) => {
      runLog.push(cmd);
      // A watchdog-killed step reports timedOut (exitCode null upstream). It must
      // NOT be treated like a genuine build failure.
      if (timeoutStep && cmd.includes(timeoutStep)) return { code: 1, log: `timed out ${cmd}`, timedOut: true };
      return { code: failStep && cmd.includes(failStep) ? 1 : 0, log: `ran ${cmd}` };
    },
    readFile: async (p) => {
      const v = files.get(key(p));
      if (v === undefined) throw new Error(`ENOENT ${p}`);
      return v;
    },
    writeFile: async (p, t) => { writeLog.push(p); files.set(key(p), t); },
    removeFile: async (p) => { files.delete(key(p)); },
    removeDir: async () => {},
    exists: async (p) => files.has(key(p)) || [...files.keys()].some((f) => f.startsWith(`${key(p)}/`)),
    lintLibraryLayout: () => [],
    lintModuleHeaders: () => ({ findings: [], legacyCount: 0 }),
  };
  return {
    files, deps, runLog, writeLog,
    setFail: (s: string | null) => { failStep = s; },
    setTimeout: (s: string | null) => { timeoutStep = s; },
  };
}

const C_ROOT = "/c";
const ROOT_LEAN = "/c/Causalean.lean";
const STAGING = "/stage";

describe("applyInsertOnly", () => {
  it("inserts root imports in sorted order and idempotently", () => {
    const root = "import Causalean.A\nimport Causalean.C\n";
    const once = insertImportSorted(root, "import Causalean.B");
    expect(once).toBe("import Causalean.A\nimport Causalean.B\nimport Causalean.C\n");
    expect(insertImportSorted(once, "import Causalean.B")).toBe(once);
  });

  it("sorts module-style imports by module name without moving the module header", () => {
    const root = "module\npublic import Causalean.C\nmeta import Causalean.A\n\n/-! Barrel. -/\n";
    expect(insertImportSorted(root, "public import Causalean.B")).toBe(
      "module\nmeta import Causalean.A\npublic import Causalean.B\npublic import Causalean.C\n\n/-! Barrel. -/\n",
    );
    expect(insertImportSorted("module\nimport Causalean.B\n", "public import Causalean.B")).toBe(
      "module\npublic import Causalean.B\n",
    );
  });

  it("ignores import-shaped comment text and keeps the real import block outside it", () => {
    const root = [
      "module",
      "/-",
      "public import Causalean.Ghost",
      "-/",
      "public import Causalean.Z",
      "",
      "/-! Barrel. -/",
      "",
    ].join("\n");
    expect(insertImportSorted(root, "public import Causalean.A")).toBe([
      "module",
      "/-",
      "public import Causalean.Ghost",
      "-/",
      "public import Causalean.A",
      "public import Causalean.Z",
      "",
      "/-! Barrel. -/",
      "",
    ].join("\n"));
  });

  it("inserts after the anchor line, preserving existing bytes", () => {
    const orig = "import A\n\nnamespace N\n-- decls here\nend N\n";
    const { merged, at, segment } = applyInsertOnly(orig, "-- decls here", "theorem t : True := trivial");
    expect(merged).toContain("theorem t : True := trivial");
    // Byte-preservation: removing the inserted segment at its offset reproduces orig.
    expect(merged.slice(0, at) + merged.slice(at + segment.length)).toBe(orig);
    // The insertion lands after the anchor line, before `end N`.
    expect(merged.indexOf("theorem t")).toBeGreaterThan(merged.indexOf("-- decls here"));
    expect(merged.indexOf("theorem t")).toBeLessThan(merged.indexOf("end N"));
  });

  it("appends at end of file for an empty anchor", () => {
    const orig = "import A\n";
    const { merged, at, segment } = applyInsertOnly(orig, "", "def z := 0");
    expect(merged.startsWith(orig)).toBe(true);
    expect(merged).toContain("def z := 0");
    expect(merged.slice(0, at) + merged.slice(at + segment.length)).toBe(orig);
  });

  it("throws when the anchor is not present", () => {
    expect(() => applyInsertOnly("import A\n", "nope", "x")).toThrow(/anchor not found/);
  });
});

describe("applyManifest", () => {
  // Base tree + staged bodies (codex writes bodies under STAGING; manifest only
  // references them by `from`).
  const base = () => ({
    [ROOT_LEAN]: "module\npublic import Causalean.Mathlib\n",
    "/c/Causalean/Mathlib.lean": "module\npublic import Causalean.Mathlib.Foo\n",
    "/c/Causalean/Mathlib/Foo.lean": "namespace Foo\n-- add here\nend Foo\n",
    "/stage/bar.lean": "namespace Bar\nend Bar\n",
    "/stage/merge_foo.lean": "theorem t : True := trivial",
  });

  it("applies create_file + merge_lean, directory-wires the new module, cleans staging", async () => {
    const fs = memFs(base());
    const manifest: CoordinationManifest = {
      notes: "",
      ops: [
        { kind: "create_file", target: "Causalean/Mathlib/Bar.lean", from: "bar.lean", newModule: "Causalean.Mathlib.Bar" },
        { kind: "merge_lean", target: "Causalean/Mathlib/Foo.lean", anchor: "-- add here", from: "merge_foo.lean" },
      ],
    };
    const staging = "/c/CausalSmith/CausalSmith/Substrate/S/Basic.lean";
    fs.files.set(staging, "stub");
    const res = await applyManifest(
      { cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [staging], manifest },
      fs.deps,
    );
    expect(res.ok).toBe(true);
    // New file written, existing file merged (existing bytes intact), directory wired.
    expect(fs.files.get("/c/Causalean/Mathlib/Bar.lean")).toContain("namespace Bar");
    expect(fs.files.get("/c/Causalean/Mathlib/Foo.lean")).toContain("theorem t");
    expect(fs.files.get("/c/Causalean/Mathlib/Foo.lean")).toContain("namespace Foo");
    expect(fs.files.get("/c/Causalean/Mathlib.lean")).toContain("public import Causalean.Mathlib.Bar");
    // Staging source deleted on success.
    expect(fs.files.has(staging)).toBe(false);
    // The full gate ran.
    expect(fs.runLog.some((c) => c.includes("lake build"))).toBe(true);
    expect(fs.runLog.some((c) => c.includes("doc:check"))).toBe(true);
  });

  it("allows the root barrel as an explicit override", async () => {
    const fs = memFs(base());
    const manifest: CoordinationManifest = {
      notes: "",
      ops: [{ kind: "create_file", target: "Causalean/Mathlib/Bar.lean", from: "bar.lean", newModule: "Causalean.Mathlib.Bar" }],
    };
    const res = await applyManifest(
      {
        cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest,
        barrelTarget: "root",
      },
      fs.deps,
    );
    expect(res.ok).toBe(true);
    expect(fs.files.get(ROOT_LEAN)).toContain("public import Causalean.Mathlib.Bar");
  });

  it("can wire a new module into an existing directory barrel", async () => {
    const directoryBarrel = "/c/Causalean/Mathlib.lean";
    const fs = memFs({
      ...base(),
      [directoryBarrel]: "module\npublic import Causalean.Mathlib.Foo\n",
    });
    const originalRoot = fs.files.get(ROOT_LEAN);
    const manifest: CoordinationManifest = {
      notes: "",
      ops: [{ kind: "create_file", target: "Causalean/Mathlib/Bar.lean", from: "bar.lean", newModule: "Causalean.Mathlib.Bar" }],
    };
    const res = await applyManifest(
      {
        cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest,
        barrelTarget: "directory",
      },
      fs.deps,
    );
    expect(res.ok).toBe(true);
    expect(fs.files.get(directoryBarrel)).toContain("public import Causalean.Mathlib.Bar");
    expect(fs.files.get(ROOT_LEAN)).toBe(originalRoot);
  });

  it("defaults to the nearest directory barrel, never the root", async () => {
    const directoryBarrel = "/c/Causalean/Mathlib.lean";
    const fs = memFs({
      ...base(),
      [directoryBarrel]: "module\npublic import Causalean.Mathlib.Foo\n",
    });
    const originalRoot = fs.files.get(ROOT_LEAN);
    const manifest: CoordinationManifest = {
      notes: "",
      ops: [{ kind: "create_file", target: "Causalean/Mathlib/Bar.lean", from: "bar.lean", newModule: "Causalean.Mathlib.Bar" }],
    };
    const res = await applyManifest(
      {
        cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest,
      },
      fs.deps,
    );
    expect(res.ok).toBe(true);
    expect(fs.files.get(directoryBarrel)).toContain("public import Causalean.Mathlib.Bar");
    expect(fs.files.get(ROOT_LEAN)).toBe(originalRoot);
  });

  it("wires Causalean.Stat.Minimax.New into the imports-only Minimax barrel", async () => {
    const minimaxBarrel = "/c/Causalean/Stat/Minimax.lean";
    const fs = memFs({
      ...base(),
      "/c/Causalean/Stat.lean": "module\npublic import Causalean.Stat.Minimax\n",
      [minimaxBarrel]: [
        "module",
        "public import Causalean.Stat.Minimax.Existing",
        "",
        "/-! Minimax barrel. -/",
        "public section",
        "",
      ].join("\n"),
    });
    const originalRoot = fs.files.get(ROOT_LEAN);
    const manifest: CoordinationManifest = {
      notes: "",
      ops: [{
        kind: "create_file", target: "Causalean/Stat/Minimax/New.lean", from: "bar.lean",
        newModule: "Causalean.Stat.Minimax.New",
      }],
    };
    const res = await applyManifest(
      {
        cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest,
      },
      fs.deps,
    );
    expect(res.ok).toBe(true);
    expect(fs.files.get(minimaxBarrel)).toContain("public import Causalean.Stat.Minimax.New");
    expect(fs.files.get(ROOT_LEAN)).toBe(originalRoot);
  });

  it("skips a same-named content module and continues upward to an imports-only barrel", async () => {
    const operatorModule = "/c/Causalean/Estimation/NPIV/Operator.lean";
    const npivBarrel = "/c/Causalean/Estimation/NPIV.lean";
    const operatorText = [
      "module",
      "public import Causalean.Estimation.NPIV.Basic",
      "",
      "/-! NPIV operators. -/",
      "@[expose] public section",
      "namespace Causalean.Estimation.NPIV",
      "def operator := 1",
      "",
    ].join("\n");
    const fs = memFs({
      ...base(),
      "/c/Causalean/Estimation.lean": "module\npublic import Causalean.Estimation.NPIV\n",
      [npivBarrel]: "module\npublic import Causalean.Estimation.NPIV.Operator\n",
      [operatorModule]: operatorText,
    });
    const manifest: CoordinationManifest = {
      notes: "",
      ops: [{
        kind: "create_file", target: "Causalean/Estimation/NPIV/Operator/New.lean", from: "bar.lean",
        newModule: "Causalean.Estimation.NPIV.Operator.New",
      }],
    };
    const res = await applyManifest(
      {
        cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest,
      },
      fs.deps,
    );
    expect(res.ok).toBe(true);
    expect(fs.files.get(operatorModule)).toBe(operatorText);
    expect(fs.files.get(npivBarrel)).toContain("public import Causalean.Estimation.NPIV.Operator.New");
  });

  it("rejects run-named target basenames and new directories before any write", async () => {
    const cases: Array<{ manifest: CoordinationManifest; slug: string; modulePrefix: string }> = [
      {
        slug: "unrelated", modulePrefix: "CausalSmith.Substrate.MyStudy",
        manifest: {
          notes: "",
          ops: [{
            kind: "create_file", target: "Causalean/Stat/MyStudy.lean", from: "bar.lean",
            newModule: "Causalean.Stat.MyStudy",
          }],
        },
      },
      {
        slug: "my-study", modulePrefix: "CausalSmith.Substrate.Unrelated",
        manifest: {
          notes: "",
          ops: [{
            kind: "create_file", target: "Causalean/Stat/my_study/Basic.lean", from: "bar.lean",
            newModule: "Causalean.Stat.my_study.Basic",
          }],
        },
      },
      {
        slug: "safe", modulePrefix: "CausalSmith.Substrate.MyStudy",
        manifest: {
          notes: "",
          ops: [{
            kind: "create_file", target: "Causalean/Stat/CausalSmithSubstrateMyStudy.lean", from: "bar.lean",
            newModule: "Causalean.Stat.CausalSmithSubstrateMyStudy",
          }],
        },
      },
    ];
    for (const { manifest, slug, modulePrefix } of cases) {
      const fs = memFs({ ...base(), "/c/Causalean/Stat/Existing.lean": "namespace Stat\n" });
      const res = await applyManifest(
        {
          cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest,
          slug, modulePrefix,
        },
        fs.deps,
      );
      expect(res.ok).toBe(false);
      expect(res.log).toMatch(/named after the study\/run/);
      expect(fs.writeLog).toEqual([]);
      expect(fs.runLog).toEqual([]);
    }
  });

  it("uses real sidecar/index state to reject a sixth headline on an untouched Lean file", async () => {
    const fixtureRoot = await mkdtemp(path.join(tmpdir(), "p5b-headlines-"));
    try {
      const repoRoot = path.join(fixtureRoot, "CausalSmith");
      const stagingDir = path.join(fixtureRoot, "stage");
      const sidecarPath = path.join(fixtureRoot, "doc/library_review/Stat.json");
      const initialSidecar = JSON.stringify({
        headline_theorems: [
          "Causalean.Stat.Existing.one", "Causalean.Stat.Existing.two",
          "Causalean.Stat.Existing.three", "Causalean.Stat.Existing.four",
          "Causalean.Stat.Existing.five",
        ],
        reviews: [], flags: [],
      });
      const fourthSidecar = JSON.stringify({
        headline_theorems: [
          "Causalean.Stat.Existing.one", "Causalean.Stat.Existing.two",
          "Causalean.Stat.Existing.three", "Causalean.Stat.Existing.four",
          "Causalean.Stat.Existing.five", "Causalean.Stat.Existing.six",
        ],
        reviews: [], flags: [],
      });
      const index = {
        entries: ["one", "two", "three", "four", "five", "six"].map((name) => ({
          name: `Causalean.Stat.Existing.${name}`,
          module: "Causalean.Stat.Existing",
          file: "Causalean/Stat/Existing.lean",
        })),
      };
      const fixtureFiles: Record<string, string> = {
        "Causalean.lean": "import Causalean.Stat.Existing\n",
        "Causalean/Stat/Existing.lean": "namespace Causalean.Stat\ntheorem existing : True := trivial\n",
        "doc/library_index.json": JSON.stringify(index),
        "doc/library_review/Stat.json": initialSidecar,
        "stage/stat.json": fourthSidecar,
      };
      for (const [relative, content] of Object.entries(fixtureFiles)) {
        const target = path.join(fixtureRoot, relative);
        await mkdir(path.dirname(target), { recursive: true });
        await writeFile(target, content, "utf8");
      }
      const runLog: string[] = [];
      const deps: CoordinateApplyDeps = {
        run: async (cmd) => { runLog.push(cmd); return { code: 0, log: `ran ${cmd}` }; },
        readFile: (target) => readFile(target, "utf8"),
        writeFile: async (target, content) => {
          await mkdir(path.dirname(target), { recursive: true });
          await writeFile(target, content, "utf8");
        },
        removeFile: async (target) => { await unlink(target).catch(() => {}); },
        removeDir: async (target) => { await rmdir(target).catch(() => {}); },
        exists: async (target) => access(target).then(() => true, () => false),
        lintModuleHeaders: () => ({ findings: [], legacyCount: 0 }),
      };
      const manifest: CoordinationManifest = {
        notes: "",
        ops: [{ kind: "write_file", target: "doc/library_review/Stat.json", from: "stat.json" }],
      };
      const res = await applyManifest(
        { cRoot: fixtureRoot, repoRoot, stagingDir, leanFiles: [], manifest },
        deps,
      );
      expect(res.ok).toBe(false);
      expect(res.log).toContain("OVER-CURATED THEOREM FILES (1)");
      expect(res.log).toContain("Causalean/Stat/Existing.lean");
      expect(runLog).toEqual(["lake build", "lake exe library_index"]);
      expect(await readFile(sidecarPath, "utf8")).toBe(initialSidecar);
    } finally {
      await rm(fixtureRoot, { recursive: true, force: true });
    }
  });

  it("refuses a sidecar naming a non-Causalean declaration, before touching the tree", async () => {
    const fixtureRoot = await mkdtemp(path.join(tmpdir(), "p5b-foreign-sidecar-"));
    try {
      const repoRoot = path.join(fixtureRoot, "CausalSmith");
      const stagingDir = path.join(fixtureRoot, "stage");
      const sidecarPath = path.join(fixtureRoot, "doc/library_review/Stat.json");
      const initialSidecar = JSON.stringify({
        headline_theorems: ["Causalean.Stat.Existing.one"],
        reviews: [], flags: [],
      });
      // A declaration that stays under CausalSmith/ must never be curated here: the index
      // records Causalean only, so such an entry fails the downstream integrity check.
      const foreignSidecar = JSON.stringify({
        headline_theorems: [
          "Causalean.Stat.Existing.one",
          "CausalSmith.olsSampleEstimator_bootstrapSolves",
        ],
        reviews: [], flags: [],
      });
      const fixtureFiles: Record<string, string> = {
        "Causalean.lean": "import Causalean.Stat.Existing\n",
        "Causalean/Stat/Existing.lean": "namespace Causalean.Stat\ntheorem existing : True := trivial\n",
        "doc/library_index.json": JSON.stringify({
          entries: [{
            name: "Causalean.Stat.Existing.one",
            module: "Causalean.Stat.Existing",
            file: "Causalean/Stat/Existing.lean",
          }],
        }),
        "doc/library_review/Stat.json": initialSidecar,
        "stage/stat.json": foreignSidecar,
      };
      for (const [relative, content] of Object.entries(fixtureFiles)) {
        const target = path.join(fixtureRoot, relative);
        await mkdir(path.dirname(target), { recursive: true });
        await writeFile(target, content, "utf8");
      }
      const runLog: string[] = [];
      const deps: CoordinateApplyDeps = {
        run: async (cmd) => { runLog.push(cmd); return { code: 0, log: `ran ${cmd}` }; },
        readFile: (target) => readFile(target, "utf8"),
        writeFile: async (target, content) => {
          await mkdir(path.dirname(target), { recursive: true });
          await writeFile(target, content, "utf8");
        },
        removeFile: async (target) => { await unlink(target).catch(() => {}); },
        removeDir: async (target) => { await rmdir(target).catch(() => {}); },
        exists: async (target) => access(target).then(() => true, () => false),
        lintModuleHeaders: () => ({ findings: [], legacyCount: 0 }),
      };
      const manifest: CoordinationManifest = {
        notes: "",
        ops: [{ kind: "write_file", target: "doc/library_review/Stat.json", from: "stat.json" }],
      };
      const res = await applyManifest(
        { cRoot: fixtureRoot, repoRoot, stagingDir, leanFiles: [], manifest },
        deps,
      );
      expect(res.ok).toBe(false);
      expect(res.log).toContain("CausalSmith.olsSampleEstimator_bootstrapSolves");
      expect(res.log).toContain("have no index entry");
      // the existing sidecar is untouched and no gate ran
      expect(await readFile(sidecarPath, "utf8")).toBe(initialSidecar);
      expect(runLog).toEqual([]);
    } finally {
      await rm(fixtureRoot, { recursive: true, force: true });
    }
  });

  it("accepts Mathlib-root declarations that Causalean owns (negative control)", async () => {
    // Causalean contributes decls into Mathlib root namespaces; these are legitimately
    // curated in Mathlib.json, so a prefix test on "Causalean." would wrongly reject them.
    const fixtureRoot = await mkdtemp(path.join(tmpdir(), "p5b-mathlib-sidecar-"));
    try {
      const repoRoot = path.join(fixtureRoot, "CausalSmith");
      const stagingDir = path.join(fixtureRoot, "stage");
      const sidecarPath = path.join(fixtureRoot, "doc/library_review/Mathlib.json");
      const updated = JSON.stringify({
        headline_theorems: ["MeasureTheory.condExp_add'", "Causalean.Mathlib.Extra.thm"],
        reviews: [{ decl: "ProbabilityTheory.witnessKernel", note: "ok" }],
        flags: [],
      });
      const fixtureFiles: Record<string, string> = {
        "Causalean.lean": "import Causalean.Mathlib.Extra\n",
        "Causalean/Mathlib/Extra.lean": "namespace Causalean.Mathlib.Extra\ntheorem thm : True := trivial\n",
        "doc/library_index.json": JSON.stringify({
          entries: [
            { name: "MeasureTheory.condExp_add'", module: "Causalean.Mathlib.Extra", file: "Causalean/Mathlib/Extra.lean" },
            { name: "Causalean.Mathlib.Extra.thm", module: "Causalean.Mathlib.Extra", file: "Causalean/Mathlib/Extra.lean" },
            { name: "ProbabilityTheory.witnessKernel", module: "Causalean.Mathlib.Extra", file: "Causalean/Mathlib/Extra.lean" },
          ],
        }),
        "doc/library_review/Mathlib.json": JSON.stringify({ headline_theorems: [], reviews: [], flags: [] }),
        "stage/mathlib.json": updated,
      };
      for (const [relative, content] of Object.entries(fixtureFiles)) {
        const target = path.join(fixtureRoot, relative);
        await mkdir(path.dirname(target), { recursive: true });
        await writeFile(target, content, "utf8");
      }
      const deps: CoordinateApplyDeps = {
        run: async () => ({ code: 0, log: "ok" }),
        readFile: (target) => readFile(target, "utf8"),
        writeFile: async (target, content) => {
          await mkdir(path.dirname(target), { recursive: true });
          await writeFile(target, content, "utf8");
        },
        removeFile: async (target) => { await unlink(target).catch(() => {}); },
        removeDir: async (target) => { await rmdir(target).catch(() => {}); },
        exists: async (target) => access(target).then(() => true, () => false),
        lintModuleHeaders: () => ({ findings: [], legacyCount: 0 }),
      };
      const manifest: CoordinationManifest = {
        notes: "",
        ops: [{ kind: "write_file", target: "doc/library_review/Mathlib.json", from: "mathlib.json" }],
      };
      const res = await applyManifest(
        { cRoot: fixtureRoot, repoRoot, stagingDir, leanFiles: [], manifest },
        deps,
      );
      // the guard must not fire: no "no index entry" complaint, and the write landed
      expect(res.log).not.toContain("have no index entry");
      expect(await readFile(sidecarPath, "utf8")).toBe(updated);
    } finally {
      await rm(fixtureRoot, { recursive: true, force: true });
    }
  });

  it("runs both lints on the post-apply tree and rolls back a lint failure", async () => {
    const directoryBarrel = "/c/Causalean/Mathlib.lean";
    const indexPath = "/c/doc/library_index.json";
    const originalIndex = "{\"entries\":[{\"name\":\"before\"}]}\n";
    const fs = memFs({
      ...base(),
      [directoryBarrel]: "module\npublic import Causalean.Mathlib.Foo\n",
      [indexPath]: originalIndex,
    });
    const baseRun = fs.deps.run;
    fs.deps.run = async (cmd, cwd) => {
      const result = await baseRun(cmd, cwd);
      if (cmd === "lake exe library_index") {
        fs.files.set(indexPath, "{\"entries\":[{\"name\":\"after\"}]}\n");
      }
      return result;
    };
    const layoutLint = vi.fn(() => {
      expect(fs.files.get("/c/Causalean/Mathlib/Bar.lean")).toContain("namespace Bar");
      return [{
        rule: "LAYER", path: "Causalean/Mathlib/Bar.lean",
        message: "imports higher layer", severity: "error" as const,
      }];
    });
    const headerLint = vi.fn((files: string[], allowLegacy: boolean) => {
      expect(files).toContain("/c/Causalean/Mathlib/Bar.lean");
      expect(files).toContain(directoryBarrel);
      expect(allowLegacy).toBe(false);
      return { findings: [], legacyCount: 0 };
    });
    fs.deps.lintLibraryLayout = layoutLint;
    fs.deps.lintModuleHeaders = headerLint;
    const manifest: CoordinationManifest = {
      notes: "",
      ops: [{ kind: "create_file", target: "Causalean/Mathlib/Bar.lean", from: "bar.lean", newModule: "Causalean.Mathlib.Bar" }],
    };
    const res = await applyManifest(
      {
        cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest,
      },
      fs.deps,
    );
    expect(layoutLint).toHaveBeenCalledWith(C_ROOT);
    expect(headerLint).toHaveBeenCalledOnce();
    expect(res.ok).toBe(false);
    expect(res.log).toContain("post-apply structural lint failed");
    expect(fs.files.has("/c/Causalean/Mathlib/Bar.lean")).toBe(false);
    expect(fs.files.get(directoryBarrel)).toBe("module\npublic import Causalean.Mathlib.Foo\n");
    expect(fs.files.get(indexPath)).toBe(originalIndex);
  });

  it("rolls back ALL changes when a gate step fails", async () => {
    const fs = memFs(base());
    fs.setFail("lake build");
    const origFoo = fs.files.get("/c/Causalean/Mathlib/Foo.lean");
    const origRoot = fs.files.get(ROOT_LEAN);
    const manifest: CoordinationManifest = {
      notes: "",
      ops: [
        { kind: "create_file", target: "Causalean/Mathlib/Bar.lean", from: "bar.lean", newModule: "Causalean.Mathlib.Bar" },
        { kind: "merge_lean", target: "Causalean/Mathlib/Foo.lean", anchor: "-- add here", from: "merge_foo.lean" },
      ],
    };
    const res = await applyManifest(
      { cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest },
      fs.deps,
    );
    expect(res.ok).toBe(false);
    // Created file removed; merged file + barrels restored byte-for-byte.
    expect(fs.files.has("/c/Causalean/Mathlib/Bar.lean")).toBe(false);
    expect(fs.files.get("/c/Causalean/Mathlib/Foo.lean")).toBe(origFoo);
    expect(fs.files.get(ROOT_LEAN)).toBe(origRoot);
  });

  it("detects a concurrent overwrite of a promoted record before the next gate", async () => {
    const fs = memFs({
      ...base(),
      "/stage/stat.json": "{\"headline_theorems\":[],\"reviews\":[],\"flags\":[]}",
      "/c/doc/library_review/Stat.json": "old",
    });
    const baseRun = fs.deps.run;
    fs.deps.run = async (cmd, cwd) => {
      const result = await baseRun(cmd, cwd);
      if (cmd === "lake build") fs.files.set("/c/doc/library_review/Stat.json", "concurrent");
      return result;
    };
    const manifest: CoordinationManifest = {
      notes: "",
      ops: [{ kind: "write_file", target: "doc/library_review/Stat.json", from: "stat.json" }],
    };
    const res = await applyManifest(
      { cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest },
      fs.deps,
    );
    expect(res.ok).toBe(false);
    expect(res.log).toMatch(/promoted record changed before verify step/);
    expect(fs.files.get("/c/doc/library_review/Stat.json")).toBe("old");
    expect(fs.runLog).toEqual(["lake build"]);
  });

  it("accepts doc:gen's own rewrite of a promoted API.md but still guards other writers", async () => {
    const staged = "intro\n<!-- GEN:X -->\n<!-- /GEN -->\n";
    const regen = "intro\n<!-- GEN:X -->\n| table |\n<!-- /GEN -->\n";
    const manifest: CoordinationManifest = {
      notes: "",
      ops: [{ kind: "write_file", target: "doc/API.md", from: "api.md" }],
    };
    const run = async (hook: (cmd: string, files: Map<string, string>) => void) => {
      const fs = memFs({ ...base(), "/stage/api.md": staged, "/c/doc/API.md": "old" });
      const baseRun = fs.deps.run;
      fs.deps.run = async (cmd, cwd) => {
        const result = await baseRun(cmd, cwd);
        hook(cmd, fs.files);
        return result;
      };
      const res = await applyManifest(
        { cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest },
        fs.deps,
      );
      return { res, fs };
    };

    // doc:gen only refreshes GEN regions: the promotion passes the stability guard through doc:check.
    const ok = await run((cmd, files) => { if (cmd.includes("library_doc_gen.ts")) files.set("/c/doc/API.md", regen); });
    expect(ok.res.log).not.toMatch(/promoted record changed/);
    expect(ok.fs.runLog).toContain("npm run doc:check");

    // A concurrent hand edit absorbed by doc:gen (text outside GEN regions changed) is rejected.
    const absorbed = await run((cmd, files) => {
      if (cmd.includes("library_doc_gen.ts")) files.set("/c/doc/API.md", regen.replace("intro", "someone else's edit"));
    });
    expect(absorbed.res.ok).toBe(false);
    expect(absorbed.res.log).toMatch(/promoted record changed before verify step 'npm run doc:check'/);
    expect(absorbed.fs.runLog).not.toContain("npm run doc:check");
    expect(absorbed.fs.files.get("/c/doc/API.md")).toBe("old");

    // A write after doc:gen's refresh is still caught before doc:check runs.
    const fs = memFs({ ...base(), "/stage/api.md": staged, "/c/doc/API.md": "old" });
    const baseRun = fs.deps.run;
    let docGenDone = false;
    fs.deps.run = async (cmd, cwd) => {
      const result = await baseRun(cmd, cwd);
      if (cmd.includes("library_doc_gen.ts")) { fs.files.set("/c/doc/API.md", regen); docGenDone = true; }
      return result;
    };
    const baseRead = fs.deps.readFile;
    fs.deps.readFile = async (p) => {
      const content = await baseRead(p);
      // The first API.md read after doc:gen is the refresh; a concurrent writer lands right after it.
      if (docGenDone && p.split(path.sep).join("/") === "/c/doc/API.md") { docGenDone = false; fs.files.set("/c/doc/API.md", "concurrent"); }
      return content;
    };
    const res = await applyManifest(
      { cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest },
      fs.deps,
    );
    expect(res.ok).toBe(false);
    expect(res.log).toMatch(/promoted record changed before verify step 'npm run doc:check'/);
    expect(fs.runLog).not.toContain("npm run doc:check");
  });

  it("does not block on advisory layout warnings, but still blocks on errors", async () => {
    const manifest: CoordinationManifest = {
      notes: "",
      ops: [{ kind: "create_file", target: "Causalean/Mathlib/Bar.lean", from: "bar.lean", newModule: "Causalean.Mathlib.Bar" }],
    };
    const run = async (severity: "warning" | "error") => {
      const fs = memFs(base());
      fs.deps.lintLibraryLayout = () => [{
        rule: "SIZE", path: "Causalean/Mathlib/Bar.lean",
        message: "722 lines exceeds normal cap of 600", severity,
      }];
      const res = await applyManifest(
        { cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest },
        fs.deps,
      );
      return { res, fs };
    };

    // The soft 600-line cap is advisory: the promotion lands, and the warning is still reported.
    const warned = await run("warning");
    expect(warned.res.ok).toBe(true);
    expect(warned.res.log).toMatch(/advisory warning\(s\) \(not blocking\)/);
    expect(warned.res.log).toMatch(/722 lines exceeds normal cap of 600/);
    expect(warned.fs.files.get("/c/Causalean/Mathlib/Bar.lean")).toContain("namespace Bar");

    // An error-severity finding (e.g. the hard cap of 900) still fails and rolls back.
    const failed = await run("error");
    expect(failed.res.ok).toBe(false);
    expect(failed.res.log).toMatch(/post-apply structural lint failed/);
    expect(failed.fs.files.has("/c/Causalean/Mathlib/Bar.lean")).toBe(false);
  });

  it("scopes advisory warnings to this promotion and never blocks on them", async () => {
    const manifest: CoordinationManifest = {
      notes: "",
      ops: [{ kind: "create_file", target: "Causalean/Mathlib/Bar.lean", from: "bar.lean", newModule: "Causalean.Mathlib.Bar" }],
    };
    const fs = memFs({
      ...base(),
      "/c/CausalSmith/tools/lint/layout_baseline.json": JSON.stringify({ violations: [
        { rule: "NAMESPACE", path: "Causalean/Mathlib/Bar.lean", message: "namespace Bar is not Causalean.Mathlib", severity: "error" },
      ] }),
    });
    fs.deps.lintLibraryLayout = () => [
      // Advisory, on a file this manifest touched: reported, not blocking.
      { rule: "SIZE", path: "Causalean/Mathlib/Bar.lean", message: "722 lines exceeds normal cap of 600", severity: "warning" as const },
      // Advisory, on a file nobody touched: must not reach the log (and so not the retry prompt).
      { rule: "SIZE", path: "Causalean/Stat/Untouched.lean", message: "888 lines exceeds normal cap of 600", severity: "warning" as const },
      // Advisory and already baselined: likewise absent from the log.
      // Baselined AND on a touched file: suppressed by the baseline alone, not by the touched filter.
      { rule: "NAMESPACE", path: "Causalean/Mathlib/Bar.lean", message: "namespace Bar is not Causalean.Mathlib", severity: "error" as const },
    ];
    // A header-lint warning must not block either: an insert-only coordinator cannot repair a
    // pre-existing header defect in a merge target.
    fs.deps.lintModuleHeaders = () => ({ findings: [{
      path: "/c/Causalean/Mathlib/Bar.lean", line: 3, rule: "expose-section",
      message: "`@[expose]` is harmless but has no effect in a theorem-only file", severity: "warning" as const,
    }], legacyCount: 0 });
    const res = await applyManifest(
      { cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest },
      fs.deps,
    );
    expect(res.ok).toBe(true);
    expect(res.log).toMatch(/722 lines exceeds normal cap of 600/);
    expect(res.log).not.toMatch(/Untouched\.lean/);
    expect(res.log).not.toMatch(/namespace Bar is not/);
    expect(res.log).toMatch(/\[lint_module_headers\] 1 advisory warning/);
  });

  it("scopes the crosslink and doc gates to this manifest's own Lean files", async () => {
    const fs = memFs(base());
    const res = await applyManifest(
      { cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest: {
        notes: "",
        ops: [{ kind: "create_file", target: "Causalean/Mathlib/Bar.lean", from: "bar.lean", newModule: "Causalean.Mathlib.Bar" }],
      } },
      fs.deps,
    );
    expect(res.ok).toBe(true);
    // Both library-wide gates are invoked with an explicit scope file …
    const scoped = fs.runLog.filter((cmd) => cmd.includes("--blocking-paths"));
    expect(scoped.some((cmd) => cmd.includes("check_nl_crosslinks.ts"))).toBe(true);
    expect(scoped.some((cmd) => cmd.includes("library_doc_gen.ts"))).toBe(true);
    // … listing exactly the Lean files this manifest touched (the new file and the wired barrel).
    const scope = fs.files.get("/stage/.promotion-scope.txt") ?? "";
    expect(scope.split("\n").filter(Boolean).sort()).toEqual([
      "Causalean/Mathlib.lean", "Causalean/Mathlib/Bar.lean",
    ]);
    // doc:check stays library-wide: a promotion must leave the whole API.md consistent.
    expect(fs.runLog.some((cmd) => cmd === "npm run doc:check")).toBe(true);
  });

  it("still blocks on an error-severity header finding", async () => {
    const fs = memFs(base());
    fs.deps.lintModuleHeaders = () => ({ findings: [{
      path: "/c/Causalean/Mathlib/Bar.lean", line: 12, rule: "blanket-public-section",
      message: "expected exactly one blanket public section, found 2", severity: "error" as const,
    }], legacyCount: 0 });
    const res = await applyManifest(
      { cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest: {
        notes: "",
        ops: [{ kind: "create_file", target: "Causalean/Mathlib/Bar.lean", from: "bar.lean", newModule: "Causalean.Mathlib.Bar" }],
      } },
      fs.deps,
    );
    expect(res.ok).toBe(false);
    expect(res.log).toMatch(/blanket-public-section/);
    expect(fs.files.has("/c/Causalean/Mathlib/Bar.lean")).toBe(false);
  });

  it("does not let a baselined size warning suppress the hard-cap error", async () => {
    const manifest: CoordinationManifest = {
      notes: "",
      ops: [{ kind: "create_file", target: "Causalean/Mathlib/Bar.lean", from: "bar.lean", newModule: "Causalean.Mathlib.Bar" }],
    };
    const fs = memFs({
      ...base(),
      "/c/CausalSmith/tools/lint/layout_baseline.json": JSON.stringify({ violations: [
        { rule: "SIZE", path: "Causalean/Mathlib/Bar.lean", message: "898 lines exceeds normal cap of 600", severity: "warning" },
      ] }),
    });
    fs.deps.lintLibraryLayout = () => [{
      rule: "SIZE", path: "Causalean/Mathlib/Bar.lean",
      message: "903 lines exceeds hard cap of 900", severity: "error" as const,
    }];
    const res = await applyManifest(
      { cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest },
      fs.deps,
    );
    expect(res.ok).toBe(false);
    expect(res.log).toMatch(/903 lines exceeds hard cap of 900/);
    expect(fs.files.has("/c/Causalean/Mathlib/Bar.lean")).toBe(false);
  });

  it("does NOT roll back when a gate step times out — preserves files and flags timedOut", async () => {
    const fs = memFs(base());
    fs.setTimeout("lake build"); // watchdog-killed verify step, not a real failure
    const manifest: CoordinationManifest = {
      notes: "",
      ops: [
        { kind: "create_file", target: "Causalean/Mathlib/Bar.lean", from: "bar.lean", newModule: "Causalean.Mathlib.Bar" },
        { kind: "merge_lean", target: "Causalean/Mathlib/Foo.lean", anchor: "-- add here", from: "merge_foo.lean" },
      ],
    };
    const staging = "/c/CausalSmith/CausalSmith/Substrate/S/Basic.lean";
    fs.files.set(staging, "stub");
    const res = await applyManifest(
      { cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [staging], manifest },
      fs.deps,
    );
    expect(res.ok).toBe(false);
    expect(res.timedOut).toBe(true);
    // Promoted work is PRESERVED (a timeout is not proof of failure): the new
    // file, the merge, and the directory-barrel wire all remain — a human confirms and
    // finalizes or rolls back manually.
    expect(fs.files.get("/c/Causalean/Mathlib/Bar.lean")).toContain("namespace Bar");
    expect(fs.files.get("/c/Causalean/Mathlib/Foo.lean")).toContain("theorem t");
    expect(fs.files.get("/c/Causalean/Mathlib.lean")).toContain("public import Causalean.Mathlib.Bar");
    // Promotion NOT finalized: the staging source is left in place.
    expect(fs.files.has(staging)).toBe(true);
  });

  it("refuses a manifest target that escapes the Causalean root (rollback, no gate)", async () => {
    const fs = memFs({ ...base(), "/stage/x.txt": "x" });
    const manifest: CoordinationManifest = {
      notes: "",
      ops: [{ kind: "write_file", target: "../escape.txt", from: "x.txt" }],
    };
    const res = await applyManifest(
      { cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest },
      fs.deps,
    );
    expect(res.ok).toBe(false);
    expect(res.log).toMatch(/escapes the Causalean root/);
    expect(fs.runLog.length).toBe(0); // never reached the gate
  });

  it("rejects a new Lean file outside an existing Causalean subject area", async () => {
    const fs = memFs(base());
    const manifest: CoordinationManifest = {
      notes: "",
      ops: [{ kind: "create_file", target: "Causalean/NewArea/Bar.lean", from: "bar.lean", newModule: "Causalean.NewArea.Bar" }],
    };
    const res = await applyManifest(
      { cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest },
      fs.deps,
    );
    expect(res.ok).toBe(false);
    expect(res.log).toMatch(/non-existing Causalean subject area/);
    expect(fs.runLog).toEqual([]);
  });

  it("rejects final Lean content with a CausalSmith dependency", async () => {
    const fs = memFs({ ...base(), "/stage/bar.lean": "import CausalSmith.Paper\nnamespace Bar\nend Bar\n" });
    const manifest: CoordinationManifest = {
      notes: "",
      ops: [{ kind: "create_file", target: "Causalean/Mathlib/Bar.lean", from: "bar.lean", newModule: "Causalean.Mathlib.Bar" }],
    };
    const res = await applyManifest(
      { cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest },
      fs.deps,
    );
    expect(res.ok).toBe(false);
    expect(res.log).toMatch(/retains a CausalSmith dependency/);
    expect(fs.files.has("/c/Causalean/Mathlib/Bar.lean")).toBe(false);
    expect(fs.runLog).toEqual([]);
  });

  it("rejects a shortened unresolved import of a sibling created module before the gate", async () => {
    const fs = memFs({
      ...base(),
      "/c/Causalean/Stat/Existing.lean": "namespace Causalean.Stat\n",
      "/stage/basic.lean": "namespace Causalean.Stat\n",
      "/stage/uses.lean": "import Causalean.Stat.Basic\nnamespace Causalean.Stat\n",
    });
    const manifest: CoordinationManifest = {
      notes: "",
      ops: [
        {
          kind: "create_file", target: "Causalean/Stat/CLT/MartingaleArray/Basic.lean",
          from: "basic.lean", newModule: "Causalean.Stat.CLT.MartingaleArray.Basic",
        },
        {
          kind: "create_file", target: "Causalean/Stat/CLT/MartingaleArray/Uses.lean",
          from: "uses.lean", newModule: "Causalean.Stat.CLT.MartingaleArray.Uses",
        },
      ],
    };
    const res = await applyManifest(
      { cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest },
      fs.deps,
    );
    expect(res.ok).toBe(false);
    expect(res.log).toMatch(/unresolved Causalean import.*Causalean\.Stat\.Basic/);
    expect(res.log).toContain("did you mean Causalean.Stat.CLT.MartingaleArray.Basic?");
    expect(fs.files.has("/c/Causalean/Stat/CLT/MartingaleArray/Basic.lean")).toBe(false);
    expect(fs.runLog).toEqual([]);
  });

  it("allows an exact import of a sibling created later in the manifest", async () => {
    const fs = memFs({
      ...base(),
      "/c/Causalean/Stat/Existing.lean": "namespace Causalean.Stat\n",
      "/c/Causalean/Stat.lean": "module\npublic import Causalean.Stat.Existing\n",
      "/stage/uses.lean": "public import Causalean.Stat.CLT.MartingaleArray.Basic\nnamespace Causalean.Stat\n",
      "/stage/basic.lean": "namespace Causalean.Stat\n",
    });
    const manifest: CoordinationManifest = {
      notes: "",
      ops: [
        {
          kind: "create_file", target: "Causalean/Stat/CLT/MartingaleArray/Uses.lean",
          from: "uses.lean", newModule: "Causalean.Stat.CLT.MartingaleArray.Uses",
        },
        {
          kind: "create_file", target: "Causalean/Stat/CLT/MartingaleArray/Basic.lean",
          from: "basic.lean", newModule: "Causalean.Stat.CLT.MartingaleArray.Basic",
        },
      ],
    };
    const res = await applyManifest(
      { cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest },
      fs.deps,
    );
    expect(res.ok).toBe(true);
    expect(fs.runLog.some((c) => c.includes("lake build"))).toBe(true);
  });

  it("rejects namespace/open CausalSmith references even without an import", async () => {
    for (const body of ["namespace CausalSmith\nend CausalSmith\n", "open CausalSmith\n"]) {
      const fs = memFs({ ...base(), "/stage/bar.lean": body });
      const manifest: CoordinationManifest = {
        notes: "",
        ops: [{ kind: "create_file", target: "Causalean/Mathlib/Bar.lean", from: "bar.lean", newModule: "Causalean.Mathlib.Bar" }],
      };
      const res = await applyManifest(
        { cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest },
        fs.deps,
      );
      expect(res.ok).toBe(false);
      expect(res.log).toMatch(/retains a CausalSmith dependency/);
    }
  });

  it("does not reject a CausalSmith name mentioned only in a comment or string", async () => {
    const fs = memFs({
      ...base(),
      "/stage/bar.lean": "/- migrated from CausalSmith.Old -/\ndef label := \"CausalSmith.Old\"\n",
    });
    const manifest: CoordinationManifest = {
      notes: "",
      ops: [{ kind: "create_file", target: "Causalean/Mathlib/Bar.lean", from: "bar.lean", newModule: "Causalean.Mathlib.Bar" }],
    };
    const res = await applyManifest(
      { cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest },
      fs.deps,
    );
    expect(res.ok).toBe(true);
  });

  it("rejects merge and record writes outside their exact allowlists", async () => {
    const cases: CoordinationManifest[] = [
      { notes: "", ops: [{ kind: "merge_lean", target: "CausalSmith/Paper.lean", anchor: "", from: "merge_foo.lean" }] },
      { notes: "", ops: [{ kind: "write_file", target: "package.json", from: "bar.lean" }] },
      { notes: "", ops: [{ kind: "create_file", target: "docs/arbitrary.md", from: "bar.lean" }] },
    ];
    for (const manifest of cases) {
      const fs = memFs({ ...base(), "/c/CausalSmith/Paper.lean": "namespace Paper\n" });
      const res = await applyManifest(
        { cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest },
        fs.deps,
      );
      expect(res.ok).toBe(false);
      expect(fs.runLog).toEqual([]);
    }
  });
});

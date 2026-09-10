import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, mkdir, writeFile, readFile, rm, symlink } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import {
  resolveLeanDeclaration,
  requiresIndividualStatementAudit,
  runStatementAudit,
  judgeStatements,
} from "../src/presentation/audit.js";
import { fullyQualifiedSourceDecls } from "../src/presentation/declaration_resolver.js";
import { extractFullDeclSource } from "../src/presentation/lean_extract.js";
import { FormalLayerSource } from "../src/presentation/formal_layer.js";
import type { StageIO } from "../src/presentation/pipeline.js";

/**
 * Mechanical-layer test for the P1 statement equivalence judge (runStatementAudit → judgeStatements).
 * It sources the env body from formal_layer.json, resolves the Lean via the crosswalk decl (a tiny
 * real Lean file) and judges with a STUB codex. The judge is verdict-only: it never rewrites the
 * layer (P1's render loop repairs drift). Covers the faithful path (cached verdict, [] returned)
 * and the drift path (one `equivalence` problem, body untouched, verdict cached as drift).
 */

const BODY = "The claim holds.";
let mode: "faithful" | "drift" = "faithful";

const stubRunCodex = async ({ prompt }: { prompt: string }) => {
  const verdict = mode === "drift" ? "drift" : "faithful";
  return { stdout: JSON.stringify({ obj_id: "thm1", verdict, detail: verdict === "drift" ? "omits the hypothesis h" : "" }), stderr: "" };
};

let dir: string;

function makeIO(): StageIO {
  return {
    outDir: dir,
    ctx: {
      repoRoot: dir,
      qid: "q",
      spec: "v1",
      deps: { runCodex: stubRunCodex, runClaude: async () => "", dryRun: false },
    },
    bank: {
      leanSubdir: "Lean",
      noteMd: "",
      graph: { nodes: [], edges: [] },
      crosswalk: [
        { obj_id: "thm1", kind: "theorem", title: "T", tex: null, lean: { file: "X.lean", decl: "thm1", decl_kind: "theorem", line: 1 }, verdict: "ok" },
      ],
    },
    state: { notes: [] },
  } as unknown as StageIO;
}

beforeEach(async () => {
  dir = await mkdtemp(join(tmpdir(), "stmtaudit-"));
  await mkdir(join(dir, "Lean"), { recursive: true });
  await writeFile(join(dir, "Lean", "X.lean"), "theorem thm1 (h : True) : True := trivial\n", "utf8");
  await writeFile(join(dir, "outline.md"), "# Title\n**Test.**\n\n# Notation\n- \\(x\\): a thing\n\n# Sections\n## section: Body\n", "utf8");
  const block = {
    obj_id: "thm1",
    alias: "T-1",
    kind: "theorem" as const,
    env: "theoremv" as const,
    title: null,
    body: BODY,
    ref_set: [],
    lean: { decl: "thm1", file: "X.lean" },
    status: "ok",
    provenance: "from-note",
  };
  await writeFile(
    join(dir, "formal_layer.json"),
    JSON.stringify(FormalLayerSource.parse({ commit: null, blocks: [block] }), null, 2) + "\n",
    "utf8",
  );
});

afterEach(async () => {
  await rm(dir, { recursive: true, force: true });
});

describe("runStatementAudit / judgeStatements (P1 statement equivalence)", () => {
  it("extracts the declaration below multiline attributes and retains its authenticated line", async () => {
    const source = "namespace N\n@[simp]\n@[aesop safe]\ntheorem foo : True := by trivial\nend N\nnamespace Other\ntheorem foo : False := by sorry\nend Other\n";
    await writeFile(join(dir, "Lean", "Attrs.lean"), source);
    const resolved = await resolveLeanDeclaration(dir, "Lean", { file: "Attrs.lean", decl: "N.foo", line: 0 });
    expect(resolved.line).toBe(4);
    expect(resolved.snippet).toContain("theorem foo : True");
    expect(resolved.snippet).not.toContain("False");
    const full = extractFullDeclSource(source, resolved.decl, resolved.line);
    expect(full).toContain("by trivial");
    expect(full).not.toContain("sorry");
  });

  it("never resolves a nearer nested export to a different outer declaration", async () => {
    const roots = "namespace A\ntheorem foo : True := by trivial\nend A\nnamespace B\ntheorem foo : 1 = 1 := rfl\nend B\n";
    const nearer = "namespace N\nnamespace A\nexport B (foo)\nend A\nend N\n";
    const outer = "namespace N\nexport A (foo)\nend N\n";
    await writeFile(join(dir, "Lean", "Nested.lean"), roots + nearer + outer);
    await expect(resolveLeanDeclaration(dir, "Lean", { file: "Nested.lean", decl: "N.foo", line: 0 }))
      .rejects.toThrow(/nested export N.A.foo.*refusing outer/);
    await writeFile(join(dir, "Lean", "Nested.lean"), roots + "namespace N.A\nend N.A\n" + outer);
    await expect(resolveLeanDeclaration(dir, "Lean", { file: "Nested.lean", decl: "N.foo", line: 0 }))
      .rejects.toThrow(/namespace N.A.*refusing outer/);
    // The same shadowing rule applies when the nearer alias is in a directly imported file.
    await writeFile(join(dir, "Lean", "Imported.lean"), roots + nearer);
    await writeFile(join(dir, "Lean", "Nested.lean"), "import Lean.Imported\n" + outer);
    await expect(resolveLeanDeclaration(dir, "Lean", { file: "Nested.lean", decl: "N.foo", line: 0 }))
      .rejects.toThrow(/nested export N.A.foo.*refusing outer/);
  });

  it("resolves an export using only declarations and namespaces visible at that command", async () => {
    const source = "namespace A\ntheorem foo : True := by trivial\nend A\nnamespace N\nexport A (foo)\nnamespace A\ntheorem foo : 1 = 1 := rfl\nend A\nend N\n";
    await writeFile(join(dir, "Lean", "Later.lean"), source);
    // Even a library-index row pointing at the future declaration cannot make it visible.
    await mkdir(join(dir, "doc"), { recursive: true });
    await writeFile(join(dir, "doc", "library_index.json"), JSON.stringify({ entries: [
      { name: "N.A.foo", file: "Lean/Later.lean", line: 7 },
    ] }));
    const resolved = await resolveLeanDeclaration(dir, "Lean", { file: "Later.lean", decl: "N.foo", line: 0 });
    expect(resolved.decl).toBe("A.foo");
    expect(resolved.snippet).toContain("True");
    expect(resolved.snippet).not.toContain("1 = 1");
  });

  it("keeps quoted export components whole instead of inventing an alias for part of a name", async () => {
    const source = "namespace A\ntheorem foo : True := by trivial\ntheorem «foo.bar» : 1 = 1 := rfl\nend A\nnamespace N\nexport A («foo.bar»)\nend N\n";
    await writeFile(join(dir, "Lean", "Quoted.lean"), source);
    const quoted = await resolveLeanDeclaration(dir, "Lean", { file: "Quoted.lean", decl: "N.«foo.bar»", line: 0 });
    expect(quoted.decl).toBe("A.«foo.bar»");
    await expect(resolveLeanDeclaration(dir, "Lean", { file: "Quoted.lean", decl: "N.foo", line: 0 }))
      .rejects.toThrow(/cannot audit/);
  });

  it("qualifies dotted relative declarations inside their enclosing namespace", async () => {
    const source = `namespace Paper.Outer
lemma Inner.target_decl : True := trivial
end Paper.Outer
`;
    expect(fullyQualifiedSourceDecls(source)).toEqual([
      { name: "Paper.Outer.Inner.target_decl", line: 2, kind: "lemma" },
    ]);
    await writeFile(join(dir, "Lean", "X.lean"), source, "utf8");
    const resolved = await resolveLeanDeclaration(dir, "Lean", {
      file: "X.lean", decl: "Paper.Outer.Inner.target_decl", line: 0,
    });
    expect(resolved).toMatchObject({
      decl: "Paper.Outer.Inner.target_decl", line: 2, relocated: false, resolution: "crosswalk",
    });
  });

  it("keeps top-level dotted and explicit root declarations absolute", () => {
    expect(fullyQualifiedSourceDecls("lemma Top.target : True := trivial\n")).toEqual([
      { name: "Top.target", line: 1, kind: "lemma" },
    ]);
    expect(fullyQualifiedSourceDecls("namespace Local\nlemma _root_.Top.target : True := trivial\nend Local\n")).toEqual([
      { name: "Top.target", line: 2, kind: "lemma" },
    ]);
  });

  it("keeps the enclosing namespace across mutual blocks and ignores comment-shaped declarations", () => {
    const source = `namespace N
/- lemma fake : False := by contradiction -/
mutual
  def a : Nat := b
  def b : Nat := 0
end
lemma target : True := trivial
end N
`;
    expect(fullyQualifiedSourceDecls(source)).toEqual([
      { name: "N.a", line: 4, kind: "def" },
      { name: "N.b", line: 5, kind: "def" },
      { name: "N.target", line: 7, kind: "lemma" },
    ]);
  });

  it("processes multiple scope commands on one physical line", () => {
    const source = `namespace N section S
end S
lemma real : True := trivial
end N
`;
    expect(fullyQualifiedSourceDecls(source)).toEqual([
      { name: "N.real", line: 3, kind: "lemma" },
    ]);
  });

  it("does not consume an adjacent scope keyword as a section or end name", () => {
    const source = `section namespace N
lemma real : True := trivial
end N end
`;
    expect(fullyQualifiedSourceDecls(source)).toEqual([
      { name: "N.real", line: 2, kind: "lemma" },
    ]);
  });

  it("ignores scope keywords inside quoted identifiers", () => {
    const source = `namespace N
def «namespace Ghost» : Nat := 1
def «end N» : Nat := 2
lemma real : True := trivial
end N
`;
    expect(fullyQualifiedSourceDecls(source)).toEqual([
      { name: "N.«namespace Ghost»", line: 2, kind: "def" },
      { name: "N.«end N»", line: 3, kind: "def" },
      { name: "N.real", line: 4, kind: "lemma" },
    ]);
  });

  it("does not authenticate declaration-shaped syntax inside a command quotation", () => {
    const source = `namespace N
macro "noop" : command => \`(command|
  lemma fake : False := by contradiction)
lemma real : True := trivial
end N
`;
    expect(fullyQualifiedSourceDecls(source)).toEqual([
      { name: "N.real", line: 4, kind: "lemma" },
    ]);
  });

  it("does not let quoted namespace or export commands alter a real declaration's identity", async () => {
    const source = `namespace N
macro "scopeSpoof" : command => \`(command|
  namespace Ghost)
macro "exportSpoof" : command => \`(command|
  export Evil (real))
lemma real : True := trivial
end N
`;
    expect(fullyQualifiedSourceDecls(source)).toEqual([
      { name: "N.real", line: 6, kind: "lemma" },
    ]);
    await writeFile(join(dir, "Lean", "X.lean"), source, "utf8");
    const resolved = await resolveLeanDeclaration(dir, "Lean", {
      file: "X.lean", decl: "N.real", line: 6,
    });
    expect(resolved).toMatchObject({ decl: "N.real", resolution: "crosswalk", relocated: false });
  });

  it("relocates a re-exported declaration through the authoritative library index", async () => {
    await mkdir(join(dir, "doc"), { recursive: true });
    await mkdir(join(dir, "Causalean", "Stat"), { recursive: true });
    await writeFile(join(dir, "Lean", "X.lean"), "import Causalean.Stat.Real\nnamespace Paper.Namespace\nexport Causalean.Stat (target_decl)\nend Paper.Namespace\n", "utf8");
    await writeFile(join(dir, "Causalean", "Stat", "Real.lean"), "namespace Causalean.Stat\nlemma target_decl : True := trivial\nend Causalean.Stat\n", "utf8");
    await writeFile(join(dir, "doc", "library_index.json"), JSON.stringify({
      entries: [{ name: "Causalean.Stat.target_decl", file: "Causalean/Stat/Real.lean", line: 2 }],
    }), "utf8");
    const resolved = await resolveLeanDeclaration(dir, "Lean", {
      file: "X.lean", decl: "Paper.Namespace.target_decl", line: 2,
    });
    expect(resolved).toMatchObject({
      file: "Causalean/Stat/Real.lean", decl: "Causalean.Stat.target_decl",
      line: 2, relocated: true, resolution: "library-index",
    });
    expect(resolved.snippet).toContain("lemma target_decl : True");
  });

  it("does not mistake a same-leaf local helper for an explicitly re-exported declaration", async () => {
    await mkdir(join(dir, "doc"), { recursive: true });
    await mkdir(join(dir, "Causalean", "Stat"), { recursive: true });
    await writeFile(
      join(dir, "Lean", "X.lean"),
      "import Causalean.Stat.Real\nlemma target_decl : False := by contradiction\nnamespace Paper.Namespace\nexport Causalean.Stat (target_decl)\nend Paper.Namespace\n",
      "utf8",
    );
    await writeFile(join(dir, "Causalean", "Stat", "Real.lean"), "namespace Causalean.Stat\nlemma target_decl : True := trivial\nend Causalean.Stat\n", "utf8");
    await writeFile(join(dir, "doc", "library_index.json"), JSON.stringify({
      entries: [{ name: "Causalean.Stat.target_decl", file: "Causalean/Stat/Real.lean", line: 2 }],
    }), "utf8");
    const resolved = await resolveLeanDeclaration(dir, "Lean", {
      file: "X.lean", decl: "Paper.Namespace.target_decl", line: 2,
    });
    expect(resolved).toMatchObject({
      file: "Causalean/Stat/Real.lean", decl: "Causalean.Stat.target_decl", resolution: "library-index",
    });
    expect(resolved.snippet).toContain(": True");
    expect(resolved.snippet).not.toContain(": False");
  });

  it("fails closed when a re-export target is ambiguous or missing", async () => {
    await mkdir(join(dir, "doc"), { recursive: true });
    await mkdir(join(dir, "Causalean", "A"), { recursive: true });
    await mkdir(join(dir, "Causalean", "B"), { recursive: true });
    await writeFile(join(dir, "Lean", "X.lean"), "-- thin barrel\n", "utf8");
    await writeFile(join(dir, "Lean", "X.lean"), "import A.One\nnamespace Paper\nexport Exact.Ns (target_decl)\nend Paper\n", "utf8");
    await writeFile(join(dir, "Causalean", "A", "One.lean"), "namespace Exact.Ns\nlemma target_decl : True := trivial\nend Exact.Ns\n", "utf8");
    await writeFile(join(dir, "Causalean", "B", "Two.lean"), "namespace Exact.Ns\nlemma target_decl : True := trivial\nend Exact.Ns\n", "utf8");
    await writeFile(join(dir, "doc", "library_index.json"), JSON.stringify({ entries: [
      { name: "Exact.Ns.target_decl", file: "Causalean/A/One.lean", line: 2 },
      { name: "Exact.Ns.target_decl", file: "Causalean/B/Two.lean", line: 2 },
    ] }), "utf8");
    await expect(resolveLeanDeclaration(dir, "Lean", {
      file: "X.lean", decl: "Paper.target_decl", line: 1,
    })).rejects.toThrow(/ambiguous/);
    await writeFile(join(dir, "doc", "library_index.json"), JSON.stringify({ entries: [] }), "utf8");
    await expect(resolveLeanDeclaration(dir, "Lean", {
      file: "X.lean", decl: "Paper.missing_decl", line: 1,
    })).rejects.toThrow(/no unique authoritative source/);
  });

  it("resolves the real PRESENT sibling topology and canonicalizes workspace-relative paths", async () => {
    const workspace = await mkdtemp(join(tmpdir(), "present-siblings-"));
    try {
      const packageRoot = join(workspace, "CausalSmith");
      await mkdir(join(packageRoot, "Run", "Helpers"), { recursive: true });
      await mkdir(join(workspace, "Causalean", "Stat"), { recursive: true });
      await mkdir(join(workspace, "doc"), { recursive: true });
      await writeFile(join(packageRoot, "Run", "Helpers", "Barrel.lean"), String.raw`
import Causalean.Stat.Real
/- export Wrong.Ns (target_decl) -/
namespace Paper.Ns
export
  Causalean.Stat
  ( target_decl )
end Paper.Ns
`, "utf8");
      await writeFile(join(workspace, "Causalean", "Stat", "Real.lean"), "namespace Causalean.Stat\nlemma target_decl : True := trivial\nend Causalean.Stat\n", "utf8");
      await writeFile(join(workspace, "doc", "library_index.json"), JSON.stringify({ entries: [
        { name: "Causalean.Stat.target_decl", file: "Causalean/Stat/Real.lean", line: 2 },
      ] }), "utf8");
      const hit = await resolveLeanDeclaration(packageRoot, "Run", {
        file: "Helpers/Barrel.lean", decl: "Paper.Ns.target_decl", line: 1,
      });
      expect(hit).toMatchObject({
        file: "Causalean/Stat/Real.lean", decl: "Causalean.Stat.target_decl", resolution: "library-index",
      });
    } finally { await rm(workspace, { recursive: true, force: true }); }
  });

  it("authenticates the alias namespace in a DirectProduct-style barrel", async () => {
    const workspace = await mkdtemp(join(tmpdir(), "present-alias-auth-"));
    try {
      const packageRoot = join(workspace, "CausalSmith");
      await mkdir(join(packageRoot, "Run", "Helpers"), { recursive: true });
      await mkdir(join(workspace, "Causalean", "Stat"), { recursive: true });
      await mkdir(join(workspace, "doc"), { recursive: true });
      await writeFile(join(packageRoot, "Run", "Helpers", "DirectProduct.lean"), `import Causalean.Stat.Real
namespace CausalSmith.Stat.BddUniformLogPenalty
export Causalean.Stat (coordinatewise_overlap_direct_product)
end CausalSmith.Stat.BddUniformLogPenalty
`, "utf8");
      await writeFile(join(workspace, "Causalean", "Stat", "Real.lean"), `namespace Causalean.Stat
lemma coordinatewise_overlap_direct_product : True := trivial
end Causalean.Stat
`, "utf8");
      await writeFile(join(workspace, "doc", "library_index.json"), JSON.stringify({ entries: [{
        name: "Causalean.Stat.coordinatewise_overlap_direct_product",
        file: "Causalean/Stat/Real.lean", line: 2,
      }] }), "utf8");
      await expect(resolveLeanDeclaration(packageRoot, "Run", {
        file: "Helpers/DirectProduct.lean", decl: "Totally.Wrong.coordinatewise_overlap_direct_product", line: 3,
      })).rejects.toThrow(/alias namespace mismatch/);
      const hit = await resolveLeanDeclaration(packageRoot, "Run", {
        file: "Helpers/DirectProduct.lean",
        decl: "CausalSmith.Stat.BddUniformLogPenalty.coordinatewise_overlap_direct_product", line: 3,
      });
      expect(hit.decl).toBe("Causalean.Stat.coordinatewise_overlap_direct_product");
    } finally { await rm(workspace, { recursive: true, force: true }); }
  });

  it("resolves an export namespace relative to the nearest enclosing namespace", async () => {
    const source = `namespace A
def foo : Nat := 1
end A
namespace N
namespace A
def foo : Bool := true
end A
export A (foo)
end N
`;
    await writeFile(join(dir, "Lean", "X.lean"), source, "utf8");
    const hit = await resolveLeanDeclaration(dir, "Lean", {
      file: "X.lean", decl: "N.foo", line: 8,
    });
    expect(hit).toMatchObject({ decl: "N.A.foo", resolution: "export-import" });
    expect(hit.snippet).toContain("def foo : Bool");
    expect(hit.snippet).not.toContain("def foo : Nat");
  });

  it("rejects wrong namespaces, traversal, and symlink escapes", async () => {
    await writeFile(join(dir, "Lean", "X.lean"), "namespace Wrong.Ns\nlemma target_decl : True := trivial\nend Wrong.Ns\n", "utf8");
    await expect(resolveLeanDeclaration(dir, "Lean", {
      file: "X.lean", decl: "Right.Ns.target_decl", line: 2,
    })).rejects.toThrow(/no exact declaration body/);
    await expect(resolveLeanDeclaration(dir, "Lean", {
      file: "../outside.lean", decl: "X.y", line: 1,
    })).rejects.toThrow(/traversing/);
    const outside = await mkdtemp(join(tmpdir(), "present-outside-"));
    try {
      await writeFile(join(outside, "Escape.lean"), "lemma escaped : True := trivial\n", "utf8");
      await symlink(join(outside, "Escape.lean"), join(dir, "Lean", "Escape.lean"));
      await expect(resolveLeanDeclaration(dir, "Lean", {
        file: "Escape.lean", decl: "escaped", line: 1,
      })).rejects.toThrow(/escapes workspace/);
    } finally { await rm(outside, { recursive: true, force: true }); }
  });

  it("rejects a recorded run-file symlink into the allowed sibling Causalean tree", async () => {
    const workspace = await mkdtemp(join(tmpdir(), "present-run-symlink-"));
    try {
      const packageRoot = join(workspace, "CausalSmith");
      await mkdir(join(packageRoot, "Run"), { recursive: true });
      await mkdir(join(workspace, "Causalean", "Stat"), { recursive: true });
      await writeFile(join(workspace, "Causalean", "Stat", "Escape.lean"),
        "namespace Causalean.Stat\nlemma escaped : True := trivial\nend Causalean.Stat\n", "utf8");
      await symlink(join(workspace, "Causalean", "Stat", "Escape.lean"), join(packageRoot, "Run", "Escape.lean"));
      await expect(resolveLeanDeclaration(packageRoot, "Run", {
        file: "Escape.lean", decl: "Causalean.Stat.escaped", line: 2,
      })).rejects.toThrow(/symlink escapes run root/);
    } finally { await rm(workspace, { recursive: true, force: true }); }
  });

  it("routes algorithmic and operation-count claims to individual audits", () => {
    expect(requiresIndividualStatementAudit("The estimator is computable in O(dM^4) operations.")).toBe(true);
    expect(requiresIndividualStatementAudit("The estimator equals the displayed clamped sum.")).toBe(false);
  });

  it("returns no problems and caches a faithful verdict when the body matches Lean", async () => {
    mode = "faithful";
    const problems = await runStatementAudit(makeIO());
    expect(problems).toEqual([]);
    const cache = JSON.parse(await readFile(join(dir, "equivalence_cache.json"), "utf8"));
    expect(cache.thm1.verdict).toBe("faithful");
    const warm = makeIO();
    warm.ctx.deps.runCodex = async () => { throw new Error("Existing faithful receipt must remain reusable"); };
    expect(await runStatementAudit(warm)).toEqual([]);
    // formal_layer.json body is unchanged (no refinement).
    const layer = FormalLayerSource.parse(JSON.parse(await readFile(join(dir, "formal_layer.json"), "utf8")));
    expect(layer.blocks[0].body).toBe(BODY);
  });

  it("supplies the referenced definitions and section context so the judge need not read the file", async () => {
    mode = "faithful";
    await writeFile(join(dir, "Lean", "X.lean"), "def foo : Nat := 1\nsection S\nvariable (n : Nat)\ntheorem thm1 (h : foo = n) : True := trivial\nend S\n", "utf8");
    const io = makeIO();
    let prompt = "";
    io.ctx.deps.runCodex = async (args) => { prompt = args.prompt; return stubRunCodex(args); };
    await runStatementAudit(io);
    expect(prompt).toContain("Referenced definitions and section context");
    expect(prompt).toContain("variable (n : Nat)");
    expect(prompt).toContain("def foo : Nat := 1");
    expect(prompt).toContain("read the file only for what they lack");
    expect(prompt).not.toContain("Read the Lean file around the declaration with your tools before judging");
  });

  it("honours a faithful row stamped under the line-carrying legacy key and re-stamps it", async () => {
    mode = "faithful";
    const io = makeIO();
    let prompt = "";
    io.ctx.deps.runCodex = async (args) => { prompt = args.prompt; return stubRunCodex(args); };
    await runStatementAudit(io);
    const cachePath = join(dir, "equivalence_cache.json");
    const cache = JSON.parse(await readFile(cachePath, "utf8"));
    const current = cache.thm1.key;
    // Rebuild the pre-2026-09-09 key from the judge's actual inputs, with the resolved line in the mapping.
    const leanStatement = /Lean statement \(extracted snippet[^\n]*\n([\s\S]*?)\n\nLean source location:/.exec(prompt)![1];
    const citedDependencies = /erased from the printed hypothesis list:\n([\s\S]*?)\n\nNotation table/.exec(prompt)![1];
    const { equivalenceAuditKey } = await import("../src/presentation/audit.js");
    const resolved = await resolveLeanDeclaration(dir, "Lean", { file: "X.lean", decl: "thm1", line: 0 });
    const inputs = { envBody: BODY, leanStatement, refDefs: "", citedDependencies };
    expect(equivalenceAuditKey({ ...inputs, mapping: `${resolved.file}:${resolved.decl}` })).toBe(current);
    const legacy = equivalenceAuditKey({ ...inputs, mapping: `${resolved.file}:${resolved.decl}:${resolved.line}` });
    cache.thm1.key = legacy;
    await writeFile(cachePath, JSON.stringify(cache));
    const warm = makeIO();
    warm.ctx.deps.runCodex = async () => { throw new Error("a legacy-keyed faithful receipt must be reused"); };
    expect(await runStatementAudit(warm)).toEqual([]);
    expect(JSON.parse(await readFile(cachePath, "utf8")).thm1.key).toBe(current);
  });

  it("fails instead of silently treating a formal bank object as note-only", async () => {
    const io = makeIO();
    io.bank.crosswalk[0].lean = null;
    io.bank.crosswalk[0].kind = "assumption";
    (io.ctx.deps as any).runCodex = async ({ prompt }: { prompt: string }) => {
      if (prompt.includes("components")) return { stdout: JSON.stringify({ components: [] }), stderr: "" };
      return { stdout: JSON.stringify({ obj_id: "thm1", verdict: "faithful" }), stderr: "" };
    };
    await expect(runStatementAudit(io)).rejects.toThrow(/neither a resolved Lean declaration nor nonempty resolved components/);
  });

  it("returns one problem on drift, leaves the layer untouched, and caches the drift verdict", async () => {
    mode = "drift";
    const problems = await runStatementAudit(makeIO());
    expect(problems).toHaveLength(1);
    expect(problems[0]).toMatchObject({ gate: "equivalence", objId: "thm1" });
    expect(problems[0].detail).toContain("omits the hypothesis h");
    const layer = FormalLayerSource.parse(JSON.parse(await readFile(join(dir, "formal_layer.json"), "utf8")));
    expect(layer.blocks[0].body).toBe(BODY);
    // A drift verdict is cached (and re-asked on a rerun, never short-circuited like faithful).
    const cache = JSON.parse(await readFile(join(dir, "equivalence_cache.json"), "utf8"));
    expect(cache.thm1.verdict).toBe("drift");
  });

  it("judgeStatements skips undelivered blocks and reuses an in-run memo for an unchanged body", async () => {
    mode = "faithful";
    let calls = 0;
    const io = makeIO();
    (io.ctx.deps as { runCodex: unknown }).runCodex = async (args: { prompt: string }) => { calls += 1; return stubRunCodex(args); };
    const layer = FormalLayerSource.parse(JSON.parse(await readFile(join(dir, "formal_layer.json"), "utf8")));
    const memo = new Map();
    const first = await judgeStatements(io, layer.blocks, memo);
    expect(first.verdicts.get("thm1")).toMatchObject({ verdict: "faithful" });
    expect(first.contexts.get("thm1")?.leanStatement).toContain("theorem thm1");
    const again = await judgeStatements(io, layer.blocks, memo);
    expect(again.verdicts.get("thm1")).toMatchObject({ verdict: "faithful" });
    expect(calls).toBe(1);
    const undelivered = await judgeStatements(io, [{ ...layer.blocks[0], status: "undelivered" }], new Map());
    expect(undelivered.verdicts.size).toBe(0);
  });
  it("reuses a coverage halt across restarts until explicit mapping correction, preserving the statement", async () => {
    const io = makeIO();
    await writeFile(join(dir, "Lean", "X.lean"), "def estimator : Nat := 1\nlemma estimator_spec : estimator = 1 := rfl\n");
    const layer = FormalLayerSource.parse(JSON.parse(await readFile(join(dir, "formal_layer.json"), "utf8")));
    layer.blocks[0] = { ...layer.blocks[0], env: "definitionv", kind: "definition",
      body: "The estimator equals one.", lean: { decl: "estimator", file: "X.lean" } };
    await writeFile(join(dir, "formal_layer.json"), JSON.stringify(layer));
    io.bank.crosswalk[0] = { ...io.bank.crosswalk[0], kind: "definition",
      lean: { ...io.bank.crosswalk[0].lean!, decl: "estimator", decl_kind: "def" } };
    io.bank.graph.nodes = [{ id: "thm1", kind: "definition", provenance: "from-note",
      nl: { statement: layer.blocks[0].body, tex_anchor: "", frozen: true },
      lean: { decl_name: "estimator", file: "X.lean" },
      review: { status: "matched", passed_hash: null }, proof: { state: "complete", sorry_count: 0 } }];
    const detail = "estimator_spec in X.lean supports the equals-one clause but is not mapped.";
    let calls = 0;
    io.ctx.deps.runCodex = async ({ prompt }) => {
      calls++;
      expect(prompt).toContain('"missing-coverage"');
      return { stdout: JSON.stringify({ verdict: prompt.includes("lemma estimator_spec") ? "faithful" : "missing-coverage", detail }), stderr: "" };
    };
    const before = await readFile(join(dir, "formal_layer.json"), "utf8");
    const memo = new Map();
    expect((await judgeStatements(io, layer.blocks, memo)).verdicts.get("thm1"))
      .toEqual({ verdict: "missing-coverage", detail });
    await judgeStatements(io, layer.blocks, memo);
    expect(await runStatementAudit(io)).toEqual([{ gate: "lean-coverage", objId: "thm1", detail: `thm1: ${detail}` }]);
    expect(calls).toBe(1); // A fresh memo/process still stops without another paid judgment.
    expect(await readFile(join(dir, "formal_layer.json"), "utf8")).toBe(before);
    const cache = JSON.parse(await readFile(join(dir, "equivalence_cache.json"), "utf8"));
    expect(cache.thm1.verdict).toBe("missing-coverage");
    io.bank.graph.nodes[0].lean.supporting_decls = ["estimator_spec"];
    expect((await judgeStatements(io, layer.blocks, new Map())).verdicts.get("thm1")?.verdict).toBe("faithful");
    expect(calls).toBe(2);
    const corrected = JSON.parse(await readFile(join(dir, "equivalence_cache.json"), "utf8"));
    expect(corrected.thm1.key).not.toBe(cache.thm1.key);
    await judgeStatements(io, layer.blocks, new Map());
    expect(calls).toBe(2);
    expect(await readFile(join(dir, "formal_layer.json"), "utf8")).toBe(before);
  });

  it("adopts batch coverage verdicts without an individual retry or weakening other statements", async () => {
    const io = makeIO();
    await writeFile(join(dir, "Lean", "X.lean"), "lemma thm1 : True := trivial\nlemma thm2 : True := trivial\n");
    const layer = FormalLayerSource.parse(JSON.parse(await readFile(join(dir, "formal_layer.json"), "utf8")));
    const blocks = ["thm1", "thm2"].map((id) => ({ ...layer.blocks[0], obj_id: id,
      env: "lemmav" as const, kind: "lemma" as const, lean: { decl: id, file: "X.lean" } }));
    io.bank.crosswalk = blocks.map((b) => ({ ...io.bank.crosswalk[0], obj_id: b.obj_id,
      kind: "lemma", lean: { ...io.bank.crosswalk[0].lean!, decl: b.obj_id } }));
    let calls = 0;
    io.ctx.deps.runCodex = async ({ prompt }) => {
      calls++;
      expect(prompt).toContain("=== PROMPT: statement_equivalence_batch ===");
      expect(prompt).toContain('"missing-coverage"');
      return { stdout: JSON.stringify({ results: [
        { obj_id: "thm1", verdict: "missing-coverage", detail: "Estimator.measurable supports the Borel clause." },
        { obj_id: "thm2", verdict: "faithful" },
      ] }), stderr: "" };
    };
    const outcome = await judgeStatements(io, blocks);
    expect(calls).toBe(1);
    expect(outcome.verdicts.get("thm1")?.verdict).toBe("missing-coverage");
    expect(outcome.verdicts.get("thm2")?.verdict).toBe("faithful");
    expect(blocks.map((b) => b.body)).toEqual([BODY, BODY]);
  });

});

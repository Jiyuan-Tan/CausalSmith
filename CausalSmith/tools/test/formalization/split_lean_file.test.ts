import { describe, it, expect } from "vitest";
import { splitFlatNamespaceFile } from "../../src/formalization/splitLeanFile.js";

const opts = { modulePrefix: "CausalSmith.Demo", baseName: "Helpers", lineBudget: 12 };

/** A flat-namespace legacy or house-style module file, plus optional injected preamble text. */
function file(decls: string[], preamble = "import Mathlib.Tactic\n", moduleStyle = false): string {
  const header = moduleStyle
    ? "module\npublic import Mathlib.Tactic\n\n/-! Demo module. -/\n\n@[expose] public section\n"
    : preamble;
  return `${header}\nnamespace Demo\n\n${decls.join("\n\n")}\n\nend Demo\n`;
}

const decl = (name: string, pad = 6) =>
  [`theorem ${name} : True := by`, ...Array.from({ length: pad }, () => "  -- filler"), "  trivial"].join("\n");

describe("splitFlatNamespaceFile — scope safety", () => {
  it("splits a genuinely flat file", () => {
    const r = splitFlatNamespaceFile(file([decl("a"), decl("b"), decl("c")]), opts);
    expect(r.ok).toBe(true);
    expect(r.parts.length).toBeGreaterThanOrEqual(2);
  });

  it("accepts the house-style blanket public section in a module preamble", () => {
    const r = splitFlatNamespaceFile(file([decl("a"), decl("b"), decl("c")], undefined, true), opts);
    expect(r.ok).toBe(true);
    expect(r.parts.length).toBeGreaterThanOrEqual(2);
  });

  it("refuses a file with a bare `section`", () => {
    const src = file([decl("a"), decl("b"), decl("c")]).replace("namespace Demo\n", "namespace Demo\nsection\n");
    const r = splitFlatNamespaceFile(src, opts);
    expect(r.ok).toBe(false);
    expect(r.reason).toMatch(/non-flat/);
  });

  // `noncomputable section` opens a scope exactly like `section`, but a `/^section\b/` test does
  // not match it. Compounding it, the anonymous `end` that closes such a scope is excluded from
  // the namespace-`end` count, so the file passes the "exactly one namespace…end" check and gets
  // split into parts that do not reproduce or close the scope.
  it("refuses a file with a `noncomputable section`", () => {
    const src = file([decl("a"), decl("b"), decl("c")])
      .replace("namespace Demo\n", "namespace Demo\nnoncomputable section\n")
      .replace("\nend Demo\n", "\nend\n\nend Demo\n");
    const r = splitFlatNamespaceFile(src, opts);
    expect(r.ok).toBe(false);
    expect(r.reason).toMatch(/non-flat/);
  });
});

describe("splitFlatNamespaceFile — legacy and module emission", () => {
  const privateLemma = [
    "private lemma hidden : True := by",
    ...Array.from({ length: 10 }, () => "  -- filler"),
    "  trivial",
  ].join("\n");
  const consumer = "theorem usesHidden : True := hidden";

  it("keeps legacy headers/imports and strips a cross-part private lemma", () => {
    const r = splitFlatNamespaceFile(file([privateLemma, consumer, decl("tail")]), opts);
    expect(r.ok).toBe(true);
    expect(r.deprivatized).toContain("hidden");
    expect(r.parts.some((p) => /\nlemma hidden\b/.test(p.content))).toBe(true);
    expect(r.parts.every((p) => !/^module\s*$/m.test(p.content))).toBe(true);
    expect(r.aggregator).not.toMatch(/^module\s*$/m);
    expect(r.aggregator).toContain("import CausalSmith.Demo.Helpers_Part1");
    expect(r.aggregator).not.toContain("public import CausalSmith.Demo.Helpers_Part1");
  });

  it("preserves module headers, public imports, and strips a cross-part private lemma", () => {
    const r = splitFlatNamespaceFile(file([privateLemma, consumer, decl("tail")], undefined, true), opts);
    expect(r.ok).toBe(true);
    expect(r.deprivatized).toContain("hidden");
    for (const part of r.parts) {
      expect(part.content).toMatch(/^module\s*$/m);
      expect(part.content).toContain("public import Mathlib.Tactic");
      expect(part.content).toContain("@[expose] public section");
    }
    expect(r.parts.some((p) => /\nlemma hidden\b/.test(p.content))).toBe(true);
    expect(r.aggregator).toMatch(/^module\s*$/m);
    expect(r.aggregator).toContain("public import Mathlib.Tactic");
    expect(r.aggregator).toContain("public import CausalSmith.Demo.Helpers_Part1");
    expect(r.aggregator).not.toMatch(/^import CausalSmith\.Demo\.Helpers_Part1$/m);
  });

  it("publishes a cross-part referent explicitly when there is no blanket public section", () => {
    const src = file([privateLemma, consumer, decl("tail")], undefined, true)
      .replace("\n@[expose] public section\n", "\n");
    const r = splitFlatNamespaceFile(src, opts);
    expect(r.ok).toBe(true);
    expect(r.parts.some((p) => /\npublic lemma hidden\b/.test(p.content))).toBe(true);
  });

  it("leaves a cross-part referent bare when a blanket public section publishes it", () => {
    const r = splitFlatNamespaceFile(file([privateLemma, consumer, decl("tail")], undefined, true), opts);
    expect(r.ok).toBe(true);
    const owner = r.parts.find((p) => /\nlemma hidden\b/.test(p.content));
    expect(owner?.content).toMatch(/\nlemma hidden\b/);
    expect(owner?.content).not.toMatch(/\npublic lemma hidden\b/);
  });

  it("upgrades a blanket public section when a later part unfolds a private definition", () => {
    const definition = [
      "def hiddenValue : Nat :=",
      ...Array.from({ length: 10 }, () => "  -- filler"),
      "  1",
    ].join("\n");
    const moduleWithUnexposedBlanket = file(
      [definition, "theorem hiddenValue_eq : hiddenValue = 1 := by simp [hiddenValue]", decl("tail")],
      undefined,
      true,
    ).replace("@[expose] public section", "public section");
    const r = splitFlatNamespaceFile(moduleWithUnexposedBlanket, opts);
    expect(r.ok).toBe(true);
    const owner = r.parts.find((p) => p.content.includes("def hiddenValue"));
    expect(owner?.content).toContain("@[expose] public section");
    expect(owner?.content).toMatch(/\ndef hiddenValue\b/);
  });

  it("finds meta imports when choosing where to insert part imports", () => {
    const src = file([decl("a"), decl("b"), decl("c")], undefined, true)
      .replace("public import Mathlib.Tactic", "public meta import Lean");
    const r = splitFlatNamespaceFile(src, opts);
    expect(r.ok).toBe(true);
    expect(r.parts[1].content).toMatch(
      /public meta import Lean\npublic import CausalSmith\.Demo\.Helpers_Part1/,
    );
  });

  it("keeps module syntax in a pinned-suffix retainer", () => {
    const r = splitFlatNamespaceFile(
      file([decl("helper", 10), "theorem pinned : True := helper", decl("tail")], undefined, true),
      { ...opts, pinnedDecls: new Set(["pinned"]) },
    );
    expect(r.ok).toBe(true);
    expect(r.parts).toHaveLength(1);
    expect(r.parts[0].content).toMatch(/^module\s*$/m);
    expect(r.aggregator).toMatch(/^module\s*$/m);
    expect(r.aggregator).toContain("public import CausalSmith.Demo.Helpers_Part1");
    expect(r.aggregator).toContain("theorem pinned");
  });
});

describe("splitFlatNamespaceFile — command prefixes", () => {
  // `set_option … in` applies to the NEXT command. If a chunk boundary lands between the two,
  // the prefix is applied to whatever command follows it in the old file while the decl it was
  // meant for moves to another part without its budget — a build that fails or hangs.
  it("keeps a `set_option … in` attached to the decl it modifies", () => {
    const decls = [decl("a"), `set_option maxHeartbeats 1000000 in\n${decl("b")}`, decl("c")];
    const r = splitFlatNamespaceFile(file(decls), opts);
    expect(r.ok).toBe(true);
    const withPrefix = [...r.parts.map((p) => p.content), r.aggregator].filter((t) =>
      t.includes("set_option maxHeartbeats 1000000 in"),
    );
    expect(withPrefix).toHaveLength(1);
    // the prefix and its theorem must live in the SAME emitted text, adjacent
    expect(withPrefix[0]).toMatch(/set_option maxHeartbeats 1000000 in\s*\ntheorem b\b/);
  });

  it("keeps stacked command prefixes with their decl", () => {
    const decls = [decl("a"), `open Classical in\nset_option maxHeartbeats 400000 in\n${decl("b")}`, decl("c")];
    const r = splitFlatNamespaceFile(file(decls), opts);
    expect(r.ok).toBe(true);
    const owner = [...r.parts.map((p) => p.content), r.aggregator].find((t) => t.includes("open Classical in"))!;
    expect(owner).toMatch(/open Classical in\s*\nset_option maxHeartbeats 400000 in\s*\ntheorem b\b/);
  });

  it("keeps a docstring, an attribute and a command prefix together with the decl", () => {
    const decls = [
      decl("a"),
      `/-- doc for b -/\n@[simp]\nset_option maxHeartbeats 400000 in\n${decl("b")}`,
      decl("c"),
    ];
    const r = splitFlatNamespaceFile(file(decls), opts);
    expect(r.ok).toBe(true);
    const owner = [...r.parts.map((p) => p.content), r.aggregator].find((t) => t.includes("doc for b"))!;
    expect(owner).toMatch(/\/-- doc for b -\/\s*\n@\[simp\]\s*\nset_option maxHeartbeats 400000 in\s*\ntheorem b\b/);
  });

  // Refuse rather than guess: a prefix that binds across a blank line cannot be attributed to a
  // decl header by the upward walk, so splitting could silently detach it.
  it("refuses when a command prefix cannot be attached to a following decl", () => {
    const decls = [decl("a"), `set_option maxHeartbeats 400000 in\n\n${decl("b")}`, decl("c")];
    const r = splitFlatNamespaceFile(file(decls), opts);
    expect(r.ok).toBe(false);
    expect(r.reason).toMatch(/command prefix/i);
  });
});

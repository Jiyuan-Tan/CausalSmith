import { describe, expect, it } from "vitest";
import type { Core } from "../../../src/discovery/core/schema.js";
import { checkGraph } from "../../../src/discovery/vcs/checks.js";
import { diffGraphs } from "../../../src/discovery/vcs/graph.js";
import { graphFromCore, renderCore } from "../../../src/discovery/vcs/render.js";
import { blobId } from "../../../src/discovery/vcs/node.js";
import { contentClosure, deriveStatus, proofVerdict, staleProofs } from "../../../src/discovery/vcs/validity.js";
import { fixtureCore } from "./fixture.js";

// The one validity rule, exercised on every edge class the old snapshots handled
// with separate code: claim edits, definition edits, assumption edits, symbol
// edits (declared and undeclared), pure rewires, TeX re-flow, deletion.

const edited = (mutate: (core: Core) => void): Core => {
  const core = fixtureCore();
  mutate(core);
  return core;
};

describe("vcs validity", () => {
  const base = graphFromCore(fixtureCore());

  it("the fixture converts with every proof valid and the closure it declares", () => {
    expect(checkGraph(base).ok).toBe(true);
    expect(deriveStatus(base, "thm:main")).toBe("proved");
    expect(deriveStatus(base, "lem:helper")).toBe("proved");
    expect(deriveStatus(base, "lem:cited")).toBe("cited");
    const closure = contentClosure(base, "thm:main");
    expect([...closure].sort()).toEqual(["ass:overlap", "def:class", "lem:cited", "lem:helper", "sym:\\bar d", "sym:n", "thm:main"]);
    // lem:helper declares only \bar d: n is outside its closure.
    expect(contentClosure(base, "lem:helper").has("sym:n")).toBe(false);
  });

  it("a claim edit on a node invalidates its own proof and every proof resting on it", () => {
    const g = graphFromCore(edited((c) => { c.statements[1].statement = "Under ass:overlap, the margin is bounded ABOVE."; }), base);
    expect(proofVerdict(g, "lem:helper")).toMatchObject({ valid: false, stale: ["lem:helper"] });
    expect(proofVerdict(g, "thm:main")).toMatchObject({ valid: false, stale: ["lem:helper"] });
    expect(renderCore(g).statements.map((s) => s.status)).toEqual(["cited", "to-prove", "to-prove"]);
    expect(staleProofs(g).map((s) => s.id)).toEqual(["lem:helper", "thm:main"]);
  });

  it("a definition or assumption edit reopens exactly the closure that uses it", () => {
    const g = graphFromCore(edited((c) => { c.assumptions[0].condition = "$\\bar d \\ge 2\\epsilon$"; }), base);
    expect(deriveStatus(g, "lem:helper")).toBe("to-prove");
    expect(deriveStatus(g, "thm:main")).toBe("to-prove");
    expect(deriveStatus(g, "lem:cited")).toBe("cited");
  });

  it("a symbol edit reopens only nodes whose declared closure uses it", () => {
    const g = graphFromCore(edited((c) => { c.symbols[1].def = "the number of clusters"; }), base);
    expect(deriveStatus(g, "lem:helper")).toBe("proved"); // declares only \bar d
    expect(deriveStatus(g, "thm:main")).toBe("to-prove"); // declares n
  });

  it("a declared symbol written with math delimiters still scopes the closure", () => {
    const g0 = graphFromCore(edited((c) => { c.statements[1].free_symbols = ["$\\bar d$"]; }));
    expect(contentClosure(g0, "lem:helper").has("sym:\\bar d")).toBe(true);
    const g = graphFromCore(edited((c) => { c.statements[1].free_symbols = ["$\\bar d$"]; c.symbols[0].def = "changed meaning"; }), g0);
    expect(deriveStatus(g, "lem:helper")).toBe("to-prove");
  });

  it("a hand-written proof on a to-prove node counts as a proof against the current tree", () => {
    const open = graphFromCore(edited((c) => { c.statements[1].status = "to-prove"; delete c.statements[1].proof_tex; }));
    expect(deriveStatus(open, "lem:helper")).toBe("to-prove");
    const repaired = graphFromCore(edited((c) => { c.statements[1].status = "to-prove"; c.statements[1].proof_tex = "the orchestrator's proof"; }), open);
    expect(deriveStatus(repaired, "lem:helper")).toBe("proved");
  });

  it("an undeclared free_symbols means any symbol edit reopens the node", () => {
    const g0 = graphFromCore(edited((c) => { delete c.statements[1].free_symbols; }));
    const g = graphFromCore(edited((c) => { delete c.statements[1].free_symbols; c.symbols[1].def = "changed"; }), g0);
    expect(deriveStatus(g, "lem:helper")).toBe("to-prove");
  });

  it("TeX re-flow, prose, provenance and pure rewires keep every proof", () => {
    const g = graphFromCore(edited((c) => {
      c.statements[2].statement = "The estimand is identified over def:class at rate $n^{ -1/2 }$.";
      c.statements[2].justification = "new motivation";
      c.assumptions[0].standard = { name: "positivity", cite: "R1983" };
      c.statements[1].depends_on = ["ass:overlap", "def:class", "lem:cited"]; // rewire only
      c.bibliography.push({ key: "X2020", citation: "Extra (2020)" });
    }), base);
    expect(deriveStatus(g, "lem:helper")).toBe("proved");
    expect(deriveStatus(g, "thm:main")).toBe("proved");
    const diff = diffGraphs(base, g);
    expect(diff.changed.every((c) => !c.content)).toBe(true);
    expect(diff.added).toEqual(["bib:X2020"]);
  });

  it("deleting a basis node or its proof reopens the dependents", () => {
    const g = graphFromCore(edited((c) => { delete c.statements[1].proof_tex; c.statements[1].status = "to-prove"; }), base);
    expect(proofVerdict(g, "lem:helper")).toMatchObject({ valid: false, reason: "no-proof" });
    expect(deriveStatus(g, "thm:main")).toBe("proved"); // thm:main's proof rests on the CLAIM of lem:helper, which stands
    const g2 = graphFromCore(edited((c) => {
      c.statements.splice(1, 1);
      c.statements[1].depends_on = ["ass:overlap", "def:class", "lem:cited"]; // proof bytes unchanged: basis carried
      c.assumptions[0].used_by = ["def:class", "thm:main"];
    }), base);
    expect(proofVerdict(g2, "thm:main")).toMatchObject({ valid: false, stale: ["lem:helper"] });
  });

  it("a status flip in the working copy cannot mint a basis for unchanged proof bytes", () => {
    const partial = graphFromCore(edited((c) => { c.statements[1].status = "to-prove"; }));
    expect(deriveStatus(partial, "lem:helper")).toBe("to-prove");
    const flipped = graphFromCore(edited(() => {}), partial); // same bytes, status "proved" in the file
    expect(deriveStatus(flipped, "lem:helper")).toBe("to-prove");
  });

  it("a hand-edited proof is re-based on the tree it was committed against", () => {
    const g = graphFromCore(edited((c) => {
      c.statements[1].statement = "Under ass:overlap, the margin is bounded ABOVE.";
      c.statements[1].proof_tex = "New proof of the new claim.";
    }), base);
    expect(deriveStatus(g, "lem:helper")).toBe("proved");
    expect(deriveStatus(g, "thm:main")).toBe("to-prove");
  });

  it("checks refuse a dangling edge, an unnormalized tree and a malformed basis", () => {
    const dangling = edited((c) => { c.statements[2].depends_on.push("lem:ghost"); });
    expect(() => graphFromCore(dangling, base)).not.toThrow();
    const check = checkGraph(graphFromCore(dangling, base));
    expect(check.ok).toBe(false);
    expect(check.violations.some((v) => v.code === "V6" || v.code === "G4")).toBe(true);
    const broken = structuredClone(base);
    const stmt = broken.nodes.get("thm:main")!;
    if (stmt.node_type === "statement") stmt.body.proof_basis = { "thm:main": "not-a-key" };
    expect(checkGraph(broken).violations.some((v) => v.code === "V4")).toBe(true);
  });

  it("checks refuse hidden structural references to a resolved question", () => {
    const core = fixtureCore();
    core.statements.push({
      id: "oeq:sharp", kind: "openendedquestion", statement: "Is the rate sharp?",
      depends_on: [], free_symbols: [], status: "to-prove", justification: "j", gap: "g", consumer: "c",
    });
    const graph = graphFromCore(core);
    const question = graph.nodes.get("oeq:sharp")!;
    if (question.node_type !== "statement") throw new Error("fixture question is not a statement");
    const resolved = { ...question, body: { ...question.body, resolved_by: "lem:helper" } };
    graph.nodes.set("oeq:sharp", resolved);
    graph.tree["oeq:sharp"] = { ...graph.tree["oeq:sharp"], blob: blobId(resolved) };
    const definition = graph.nodes.get("def:class")!;
    if (definition.node_type !== "definition") throw new Error("fixture definition is not a definition");
    const referencing = { ...definition, body: { ...definition.body, construction: "$\\{P : \\text{oeq:sharp holds}\\}$" } };
    graph.nodes.set("def:class", referencing);
    graph.tree["def:class"] = { ...graph.tree["def:class"], blob: blobId(referencing) };

    expect(checkGraph(graph).violations).toContainEqual(expect.objectContaining({ code: "V2", where: "def:class" }));
  });
});

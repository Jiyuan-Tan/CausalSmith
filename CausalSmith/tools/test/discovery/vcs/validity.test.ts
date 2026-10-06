import { describe, expect, it } from "vitest";
import type { Core } from "../../../src/discovery/core/schema.js";
import { checkGraph } from "../../../src/discovery/vcs/checks.js";
import { diffGraphs, statementBlob } from "../../../src/discovery/vcs/graph.js";
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
    expect(proofVerdict(g, "lem:helper")).toMatchObject({ valid: false, reason: "no-basis" });
    expect(proofVerdict(g, "thm:main")).toMatchObject({ valid: false, stale: ["lem:helper"] });
    expect(renderCore(g).statements.map((s) => s.status)).toEqual(["cited", "to-prove", "to-prove"]);
    expect(staleProofs(g).map((s) => s.id)).toEqual(["thm:main"]);
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

  it("keeps exact symbol identities when normalized aliases collide", () => {
    const original = edited((c) => {
      c.symbols.push({ name: "$n$", type: "integer", def: "an aliased count" });
      c.statements[1].free_symbols = ["n", "$n$"];
    });
    const g0 = graphFromCore(original);
    expect(contentClosure(g0, "lem:helper").has("sym:n")).toBe(true);
    expect(contentClosure(g0, "lem:helper").has("sym:$n$")).toBe(true);
    const g = graphFromCore(edited((c) => {
      c.symbols.push({ name: "$n$", type: "integer", def: "an aliased count" });
      c.statements[1].free_symbols = ["n", "$n$"];
      c.symbols.find((symbol) => symbol.name === "n")!.def = "changed sample size";
    }), g0);
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

  it("byte-different TeX re-flow defers its proof while prose and rewires stay content-neutral", () => {
    const g = graphFromCore(edited((c) => {
      c.statements[2].statement = "The estimand is identified over def:class at rate $n^{ -1/2 }$.";
      c.statements[2].justification = "new motivation";
      c.assumptions[0].standard = { name: "positivity", cite: "R1983" };
      c.statements[1].depends_on = ["ass:overlap", "def:class", "lem:cited"]; // rewire only
      c.bibliography.push({ key: "X2020", citation: "Extra (2020)" });
    }), base);
    expect(deriveStatus(g, "lem:helper")).toBe("proved");
    expect(deriveStatus(g, "thm:main")).toBe("to-prove");
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

  it("a hand-edited claim and proof require a later proof-only authentication", () => {
    const g = graphFromCore(edited((c) => {
      c.statements[1].statement = "Under ass:overlap, the margin is bounded ABOVE.";
      c.statements[1].proof_tex = "New proof of the new claim.";
    }), base);
    expect(deriveStatus(g, "lem:helper")).toBe("to-prove");
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

  it("treats a direct whole-core resurrection of a tombstone as a new exhaustive claim", () => {
    const liveCore = fixtureCore();
    liveCore.statements.push({
      id: "oeq:reopen", kind: "openendedquestion", statement: "Can $n$ be bounded?",
      depends_on: [], free_symbols: [], status: "proved", proof_tex: "A purported answer.",
      justification: "j", gap: "g", consumer: "c",
    });
    const live = graphFromCore(liveCore);
    const question = live.nodes.get("oeq:reopen")!;
    if (question.node_type !== "statement") throw new Error("fixture question is not a statement");
    const tombstone = structuredClone(live);
    const resolved = { ...question, body: { ...question.body, resolved_by: "thm:main" } };
    tombstone.nodes.set("oeq:reopen", resolved);
    tombstone.tree["oeq:reopen"] = { ...tombstone.tree["oeq:reopen"], blob: blobId(resolved) };

    const reopenedCore = structuredClone(liveCore);
    reopenedCore.symbols.push({ name: "eta", type: "real", def: "a newly registered nuisance" });
    const reopened = graphFromCore(reopenedCore, tombstone);
    const reopenedBody = reopened.nodes.get("oeq:reopen");
    if (reopenedBody?.node_type !== "statement") throw new Error("reopened question is not a statement");
    expect(reopenedBody.body.free_symbols).toEqual(reopenedCore.symbols.map((symbol) => symbol.name));
    expect(deriveStatus(reopened, "oeq:reopen")).toBe("to-prove");
  });

  it("treats a direct whole-core addition as exhaustive and defers its proof", () => {
    const addedCore = renderCore(base);
    addedCore.statements.push({
      id: "lem:direct-new", kind: "lemma", statement: "The new claim uses $n$.",
      depends_on: [], free_symbols: [], status: "proved", proof_tex: "A same-action proof.",
      justification: "j", gap: "g", consumer: "c",
    });
    const added = graphFromCore(addedCore, base);
    const body = statementBlob(added, "lem:direct-new")!.body;
    expect(body.free_symbols).toEqual(addedCore.symbols.map((symbol) => symbol.name));
    expect(body.proof_basis).toBeUndefined();
    expect(deriveStatus(added, "lem:direct-new")).toBe("to-prove");

    const proofOnly = renderCore(added);
    proofOnly.statements.find((statement) => statement.id === "lem:direct-new")!.proof_tex = "A later proof.";
    expect(deriveStatus(graphFromCore(proofOnly, added), "lem:direct-new")).toBe("proved");
  });

  it("cannot narrow a direct scope in one commit and stamp a proof against it in the next", () => {
    const first = renderCore(base);
    first.statements.find((statement) => statement.id === "thm:main")!.free_symbols = [];
    const narrowed = graphFromCore(first, base);
    expect(statementBlob(narrowed, "thm:main")!.body.free_symbols).toHaveLength(2);
    expect(statementBlob(narrowed, "thm:main")!.body.free_symbols).toEqual(expect.arrayContaining(["\\bar d", "n"]));

    const second = renderCore(narrowed);
    const main = second.statements.find((statement) => statement.id === "thm:main")!;
    main.free_symbols = [];
    main.proof_tex = "A replacement proof after attempted narrowing.";
    const reproved = graphFromCore(second, narrowed);
    expect(statementBlob(reproved, "thm:main")!.body.free_symbols).toHaveLength(2);
    expect(statementBlob(reproved, "thm:main")!.body.free_symbols).toEqual(expect.arrayContaining(["\\bar d", "n"]));
    const changed = renderCore(reproved);
    changed.symbols.find((symbol) => symbol.name === "n")!.def = "changed sample size";
    expect(deriveStatus(graphFromCore(changed, reproved), "thm:main")).toBe("to-prove");
  });

  it("cannot swap an old symbol scope for a newly added exact alias", () => {
    const edited = renderCore(base);
    edited.symbols.push({ name: "$\\bar d$", type: "real", def: "a distinct exact alias" });
    const helper = edited.statements.find((statement) => statement.id === "lem:helper")!;
    helper.free_symbols = ["$\\bar d$"];
    helper.proof_tex = "A replacement proof attempting an alias swap.";
    const graph = graphFromCore(edited, base);
    expect(statementBlob(graph, "lem:helper")!.body.free_symbols).toEqual(["\\bar d"]);
    const changed = renderCore(graph);
    changed.symbols.find((symbol) => symbol.name === "\\bar d")!.def = "changed original meaning";
    expect(deriveStatus(graphFromCore(changed, graph), "lem:helper")).toBe("to-prove");
  });

  it("materializes a normalized fallback before a new exact alias can shadow it", () => {
    const initial = renderCore(base);
    const helper = initial.statements.find((statement) => statement.id === "lem:helper")!;
    helper.free_symbols = ["$n$"];
    const prior = graphFromCore(initial);
    const shadowedCore = renderCore(prior);
    shadowedCore.symbols.push({ name: "$n$", type: "integer", def: "a distinct exact alias" });
    const shadowed = graphFromCore(shadowedCore, prior);
    expect(statementBlob(shadowed, "lem:helper")!.body.free_symbols).toEqual(["n"]);
    const proofCore = renderCore(shadowed);
    proofCore.statements.find((statement) => statement.id === "lem:helper")!.proof_tex = "A fresh proof after shadowing.";
    const reproved = graphFromCore(proofCore, shadowed);
    const changed = renderCore(reproved);
    changed.symbols.find((symbol) => symbol.name === "n")!.def = "changed old identity";
    expect(deriveStatus(graphFromCore(changed, reproved), "lem:helper")).toBe("to-prove");
  });

  it("does not narrow a legacy undefined all-symbol scope during symbol growth", () => {
    const legacyCore = renderCore(base);
    delete legacyCore.statements.find((statement) => statement.id === "lem:helper")!.free_symbols;
    const legacy = graphFromCore(legacyCore);
    const edited = renderCore(legacy);
    edited.symbols.push({ name: "eta", type: "real", def: "a new symbol" });
    const helper = edited.statements.find((statement) => statement.id === "lem:helper")!;
    helper.free_symbols = ["\\bar d", "n"];
    helper.proof_tex = "A fresh proof attempting to omit eta.";
    const reproved = graphFromCore(edited, legacy);
    expect(statementBlob(reproved, "lem:helper")!.body.free_symbols).toEqual(["\\bar d", "n", "eta"]);
    const changed = renderCore(reproved);
    changed.symbols.find((symbol) => symbol.name === "eta")!.def = "changed new symbol";
    expect(deriveStatus(graphFromCore(changed, reproved), "lem:helper")).toBe("to-prove");
  });
});

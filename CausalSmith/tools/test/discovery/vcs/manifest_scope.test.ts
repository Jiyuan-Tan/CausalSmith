import { mkdtemp, rm } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, beforeEach, describe, expect, it } from "vitest";
import { SolveUnitOutputSchema, type SolveUnitOutput } from "../../../src/discovery/solve/schemas.js";
import type { Core } from "../../../src/discovery/core/schema.js";
import { commitOrThrow } from "../../../src/discovery/vcs/commit.js";
import { loadGraph, statementBlob } from "../../../src/discovery/vcs/graph.js";
import { applyUnitOutput, foldUnitHeads, mergePr, openPr } from "../../../src/discovery/vcs/pr.js";
import { graphFromCore, renderCore } from "../../../src/discovery/vcs/render.js";
import { VcsStore } from "../../../src/discovery/vcs/store.js";
import { deriveStatus } from "../../../src/discovery/vcs/validity.js";
import { fixtureCore } from "./fixture.js";

const out = (partial: Partial<SolveUnitOutput>): SolveUnitOutput => SolveUnitOutputSchema.parse(partial);

describe("per-node symbol manifests", () => {
  let dir: string; let store: VcsStore; let base: string;
  const openCore = (): Core => {
    const core = fixtureCore();
    for (const s of core.statements) if (s.status === "proved") { s.status = "to-prove"; delete s.proof_tex; }
    return core;
  };
  beforeEach(async () => {
    dir = await mkdtemp(path.join(os.tmpdir(), "vcs-manifest-"));
    store = new VcsStore(dir);
    const init = await commitOrThrow({ store, graph: graphFromCore(openCore()), parents: [], author: "test", kind: "initial", message: "init", expectedHead: null });
    base = init.id;
  });
  afterEach(async () => { await rm(dir, { recursive: true, force: true }); });

  it("a declared manifest survives fold and merge; only a declared symbol's change stales the proof", async () => {
    const { pr } = await openPr({ store, base, round: 1, submissions: [
      { unit: "u1", targets: ["lem:helper"], output: out({ added_lemmas: [{
        id: "lem:narrow", kind: "lemma", statement: "A claim about $n$ only.", depends_on: [], free_symbols: ["n"], status: "proved", proof_tex: "Count.",
      }] }) },
      { unit: "u2", targets: ["thm:main"], output: out({ proposed_core_edits: [{
        kind: "symbol-add", name: "\\eta", proposed: { name: "\\eta", type: "scalar", def: "sibling symbol" }, reason: "add", direction: "correct",
      }] }) },
    ] });
    const merged = await mergePr({ store, pr, verdict: { accept: "all", note: "ok", by: "test" } });
    expect(merged.ok).toBe(true); if (!merged.ok) return;
    expect(statementBlob(merged.graph, "lem:narrow")!.body.free_symbols).toEqual(["n"]);
    expect(deriveStatus(merged.graph, "lem:narrow")).toBe("proved");
    // undeclared symbol changes: proof stands
    const unrelated = renderCore(merged.graph);
    unrelated.symbols.find((s) => s.name === "\\bar d")!.def = "changed unrelated meaning";
    const g1 = graphFromCore(unrelated, merged.graph);
    expect(deriveStatus(g1, "lem:narrow")).toBe("proved");
    // declared symbol changes: proof stale
    const related = renderCore(merged.graph);
    related.symbols.find((s) => s.name === "n")!.def = "changed sample size";
    expect(deriveStatus(graphFromCore(related, merged.graph), "lem:narrow")).toBe("to-prove");
  });

  it("a declared manifest is widened by a table symbol the proof visibly uses", () => {
    const born = applyUnitOutput(graphFromCore(openCore()), { unit: "u1", targets: ["lem:helper"], output: out({ added_lemmas: [{
      id: "lem:proof-only", kind: "lemma", statement: "A claim about $n$ only.", depends_on: [], free_symbols: ["n"], status: "proved",
      proof_tex: "By the definition of $\\bar d$.",
    }] }) });
    expect(statementBlob(born.graph, "lem:proof-only")!.body.free_symbols).toEqual(["n", "\\bar d"]);
  });

  it("an omitted manifest is the all-symbol scope and widens with the table", () => {
    const baseGraph = graphFromCore(openCore());
    const born = applyUnitOutput(baseGraph, { unit: "u1", targets: ["lem:helper"], output: out({ added_lemmas: [{
      id: "lem:wide", kind: "lemma", statement: "Uses something.", depends_on: [], status: "proved", proof_tex: "P.",
    }] }) });
    expect(statementBlob(born.graph, "lem:wide")!.body.free_symbols).toEqual(["\\bar d", "n"]);
    const symbolHead = applyUnitOutput(baseGraph, { unit: "u2", targets: ["thm:main"], output: out({ proposed_core_edits: [{
      kind: "symbol-add", name: "\\eta", proposed: { name: "\\eta", type: "scalar", def: "x" }, reason: "add", direction: "correct",
    }] }) });
    const folded = foldUnitHeads(baseGraph, [born, symbolHead]).graph;
    expect(statementBlob(folded, "lem:wide")!.body.free_symbols).toEqual(["\\bar d", "n", "\\eta"]);
    expect(deriveStatus(folded, "lem:wide")).toBe("to-prove");
  });

  it("a PR-born answer whose resolution is detached loses its basis even with no symbol pointing at the question", async () => {
    const core = openCore();
    core.statements.push({ id: "oeq:q", kind: "openendedquestion", statement: "Is it sharp?", depends_on: [], free_symbols: [], status: "to-prove", justification: "j", gap: "g", consumer: "c" });
    const initial = await commitOrThrow({ store, graph: graphFromCore(core), parents: [base], author: "test", kind: "direct", message: "q", expectedHead: base });
    base = initial.id;
    const { pr } = await openPr({ store, base, round: 1, submissions: [{ unit: "u1", targets: ["oeq:q"], output: out({
      resolved_oeqs: [{ source_id: "oeq:q", theorem: { id: "thm:ans", kind: "theorem", statement: "It is sharp.", depends_on: ["oeq:q"], free_symbols: [], status: "proved", proof_tex: "Answer." } }],
    }) }] });
    const mainCore = renderCore(await loadGraph(store, base));
    mainCore.statements.find((s) => s.id === "oeq:q")!.statement = "Is the corrected thing sharp?";
    await commitOrThrow({ store, graph: graphFromCore(mainCore, await loadGraph(store, base)), parents: [base], author: "main", kind: "direct", message: "fix q", expectedHead: base });
    const merged = await mergePr({ store, pr, verdict: { accept: "all", conflicts: { "oeq:q": "main" }, note: "keep main", by: "adj" } });
    expect(merged.ok).toBe(true); if (!merged.ok) return;
    expect(merged.graph.nodes.get("oeq:q")).not.toMatchObject({ body: { resolved_by: expect.anything() } });
    expect(statementBlob(merged.graph, "thm:ans")!.body.proof_basis).toBeUndefined();
    expect(deriveStatus(merged.graph, "thm:ans")).toBe("to-prove");
  });
});

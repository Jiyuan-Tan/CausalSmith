import { mkdtemp, readFile, rm } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, beforeEach, describe, expect, it } from "vitest";
import type { Core } from "../../../src/discovery/core/schema.js";
import { SolveUnitOutputSchema, type SolveUnitOutput } from "../../../src/discovery/solve/schemas.js";
import { commitOrThrow, headGraph } from "../../../src/discovery/vcs/commit.js";
import { loadGraph } from "../../../src/discovery/vcs/graph.js";
import { applyUnitOutput, closePr, describePr, listPrs, mergePr, openPr, readPr, reapplyPr, reconcileToBase } from "../../../src/discovery/vcs/pr.js";
import { graphFromCore, renderCore } from "../../../src/discovery/vcs/render.js";
import { VcsStore } from "../../../src/discovery/vcs/store.js";
import { deriveStatus } from "../../../src/discovery/vcs/validity.js";
import { fixtureCore } from "./fixture.js";

// A solver round is a pull request. These cover the whole contract: additive rounds
// merge on their own; claim / definition / assumption changes wait for a verdict;
// a rejected change leaves its proof stale instead of pairing anything; two units
// on one node conflict at fold time; nothing a solver emits can echo state.

const out = (partial: Partial<SolveUnitOutput>): SolveUnitOutput => SolveUnitOutputSchema.parse(partial);

describe("vcs pull requests", () => {
  let dir: string;
  let store: VcsStore;
  let base: string;
  /** The fixture with thm:main and lem:helper still open. */
  const openCore = (): Core => {
    const core = fixtureCore();
    for (const s of core.statements) if (s.status === "proved") { s.status = "to-prove"; delete s.proof_tex; }
    return core;
  };
  beforeEach(async () => {
    dir = await mkdtemp(path.join(os.tmpdir(), "vcs-pr-"));
    store = new VcsStore(dir);
    const init = await commitOrThrow({ store, graph: graphFromCore(openCore()), parents: [], author: "test", kind: "initial", message: "init", expectedHead: null });
    base = init.id;
  });
  afterEach(async () => { await rm(dir, { recursive: true, force: true }); });

  it("an additive round (proofs, a helper lemma, an obligation) opens with nothing to approve and merges", async () => {
    const { pr, head } = await openPr({
      store, base, round: 1,
      submissions: [{
        unit: "u1", targets: ["lem:helper", "thm:main"],
        output: out({
          proofs: [{ id: "lem:helper", proof_tex: "By ass:overlap." }],
          added_lemmas: [{ id: "lem:new", kind: "lemma", statement: "A new helper.", depends_on: ["ass:overlap"], free_symbols: [], status: "proved", proof_tex: "Clear." }],
          open_obligations: [{ node_id: "thm:main", what_is_open: "the rate", obstruction: "needs lem:new sharpened", attempted: "direct" }],
        }),
      }],
    });
    expect(pr.approval).toEqual([]);
    expect(pr.units[0].rejected).toEqual([]);
    expect(deriveStatus(head, "lem:helper")).toBe("proved");
    expect(deriveStatus(head, "lem:new")).toBe("proved");
    expect(deriveStatus(head, "thm:main")).toBe("to-prove");
    const merged = await mergePr({ store, pr, verdict: { accept: "all", note: "auto", by: "pipeline" } });
    expect(merged.ok).toBe(true);
    const { graph } = await headGraph(store);
    const core = renderCore(graph);
    expect(core.statements.find((s) => s.id === "thm:main")?.obligation?.what_is_open).toBe("the rate");
    expect(core.statements.find((s) => s.id === "lem:new")?.status).toBe("proved");
    expect((await readPr(store, pr.id)).status).toBe("merged");
    expect((await listPrs(store, "open")).length).toBe(0);
  });

  it("approval-gates a fresh theorem carrying intrinsic statement prose", async () => {
    const { pr } = await openPr({
      store, base, round: 1,
      submissions: [{ unit: "u1", targets: ["lem:helper"], proseRole: "omit", output: out({
        added_lemmas: [{
          id: "thm:fresh", kind: "theorem", statement: "A fresh headline claim.",
          depends_on: [], free_symbols: [], status: "proved", proof_tex: "Direct.",
          justification: "intrinsic rationale", gap: "new gap", consumer: "new consumer",
        }],
      }) }],
    });
    expect(pr.approval.map((item) => [item.id, item.change])).toContainEqual(["thm:fresh", "added"]);
  });

  it("a claim change waits for a verdict; rejecting it leaves the proof of the proposed claim stale", async () => {
    const submission = {
      unit: "u1", targets: ["thm:main", "lem:helper"],
      output: out({
        proposed_statement_changes: [{ id: "thm:main", current: "ignored", proposed: "The estimand is identified over def:class at rate $n^{-1/4}$.", reason: "the $n^{-1/2}$ rate fails", direction: "narrow" }],
        proofs: [{ id: "thm:main", proof_tex: "Proof of the narrowed claim." }, { id: "lem:helper", proof_tex: "By ass:overlap." }],
      }),
    };
    const { pr, head } = await openPr({ store, base, round: 1, submissions: [submission] });
    expect(pr.approval.map((a) => [a.id, a.change, a.content])).toEqual([["thm:main", "changed", true]]);
    expect(pr.approval[0].reasons[0]).toMatch(/narrow: the/);
    expect(deriveStatus(head, "thm:main")).toBe("proved"); // on the PR head, the proof matches the proposed claim
    expect(describePr(pr, await loadGraph(store, base), head)).toMatch(/NEEDS APPROVAL/);

    const rejected = await mergePr({ store, pr, verdict: { accept: [], reject: ["thm:main"], note: "keep the original rate", by: "adjudicator" } });
    expect(rejected.ok).toBe(true);
    const { graph } = await headGraph(store);
    expect(deriveStatus(graph, "lem:helper")).toBe("proved");
    expect(deriveStatus(graph, "thm:main")).toBe("to-prove");
    expect(renderCore(graph).statements.find((s) => s.id === "thm:main")?.statement).toMatch(/n\^\{-1\/2\}/);

    // The same round accepted instead: the narrowed claim lands with its proof.
    const again = await openPr({ store, base: (await store.readRef("main"))!, round: 2, submissions: [submission] });
    const accepted = await mergePr({ store, pr: again.pr, verdict: { accept: "all", note: "narrowing is honest", by: "adjudicator" } });
    expect(accepted.ok).toBe(true);
    const after = (await headGraph(store)).graph;
    expect(deriveStatus(after, "thm:main")).toBe("proved");
    expect(renderCore(after).statements.find((s) => s.id === "thm:main")?.statement).toMatch(/n\^\{-1\/4\}/);
  });

  it("two units changing one definition conflict at fold time; the second unit's change is dropped and recorded", async () => {
    const change = (construction: string, unit: string, target: string): Parameters<typeof openPr>[0]["submissions"][number] => ({
      unit, targets: [target],
      output: out({
        proposed_definition_changes: [{ id: "def:class", current: "x", proposed: construction, reason: `${unit} needs it`, direction: "correct" }],
        proposed_core_edits: [{ kind: "definition-replace", id: "def:class", proposed: { id: "def:class", name: "P", construction, free_symbols: ["\\bar d"], by_member_properties: ["ass:overlap"] }, reason: `${unit}`, direction: "correct" }],
        proofs: [{ id: target, proof_tex: `Proof against the corrected class.` }],
      }),
    });
    const { pr, head } = await openPr({
      store, base, round: 1,
      submissions: [change("$\\{P : A\\}$", "u1", "lem:helper"), change("$\\{P : B\\}$", "u2", "thm:main")],
    });
    expect(pr.dropped).toEqual([{ unit: "u2", id: "def:class", reason: "another unit changed the same node" }]);
    expect(deriveStatus(head, "lem:helper")).toBe("proved");
    expect(deriveStatus(head, "thm:main")).toBe("to-prove"); // its proof rested on B, which did not land
    expect(pr.approval.map((a) => a.id)).toEqual(["def:class"]);
  });

  it("rejects out-of-ownership proofs, re-emitted ids with a different claim, and dangling additions, keeping the rest", async () => {
    const { pr, head } = await openPr({
      store, base, round: 1,
      submissions: [{
        unit: "u1", targets: ["lem:helper"],
        output: out({
          proofs: [{ id: "thm:main", proof_tex: "not mine" }, { id: "lem:helper", proof_tex: "mine" }],
          added_lemmas: [
            { id: "lem:cited", kind: "lemma", statement: "A DIFFERENT claim.", depends_on: [], free_symbols: [], status: "proved", proof_tex: "x" },
            { id: "lem:dangling", kind: "lemma", statement: "Uses a ghost.", depends_on: ["ass:ghost"], free_symbols: [], status: "proved", proof_tex: "x" },
          ],
        }),
      }],
    });
    expect(pr.units[0].rejected.map((r) => [r.channel, r.id])).toEqual([["added_lemmas", "lem:cited"], ["proofs", "thm:main"]]);
    expect(pr.dropped.map((d) => d.id)).toEqual(["lem:dangling"]);
    expect(deriveStatus(head, "lem:helper")).toBe("proved");
    expect(head.nodes.has("lem:dangling")).toBe(false);
  });

  it("drops the dependents of a rejected item with it, and says so", async () => {
    const { pr } = await openPr({
      store, base, round: 1,
      submissions: [{
        unit: "u1", targets: ["lem:helper"],
        output: out({
          proposed_assumptions: [{ id: "ass:extra", condition: "an extra condition", free_symbols: [], reason: "needed", standard_or_novel: "novel: new", not_crux: "side condition" }],
          proposed_core_edits: [{ kind: "definition-add", id: "def:aux", proposed: { id: "def:aux", name: "Q", construction: "$\\{P : \\text{ass:extra}\\}$", by_member_properties: ["ass:extra"] }, reason: "class under the extra condition", direction: "correct" }],
        }),
      }],
    });
    expect(pr.approval.map((a) => a.id).sort()).toEqual(["ass:extra", "def:aux"]);
    const partial = await mergePr({ store, pr, verdict: { accept: ["def:aux"], reject: ["ass:extra"], note: "no new assumption", by: "adjudicator" } });
    expect(partial.ok).toBe(true);
    if (!partial.ok) return;
    expect(partial.conflicts.map((c) => c.id)).toEqual(["def:aux"]);
    expect(partial.conflicts[0].reason).toMatch(/rejected item/);
    const after = (await headGraph(store)).graph;
    expect(after.nodes.has("def:aux")).toBe(false);
    expect(after.nodes.has("ass:extra")).toBe(false);
  });

  it("a unit may not change, prove, annotate or re-emit a sibling unit's target", async () => {
    const { pr, head } = await openPr({
      store, base, round: 1,
      submissions: [
        { unit: "u1", targets: ["lem:helper"], output: out({
          proofs: [{ id: "lem:helper", proof_tex: "mine" }],
          open_obligations: [{ node_id: "thm:main", what_is_open: "x", obstruction: "y", attempted: "z" }],
          proposed_statement_changes: [{ id: "thm:main", proposed: "A narrowed main claim.", reason: "r", direction: "narrow" }],
        }) },
        { unit: "u2", targets: ["thm:main"], output: out({ proofs: [{ id: "thm:main", proof_tex: "the owner's proof" }] }) },
      ],
    });
    expect(pr.units[0].rejected.map((r) => [r.channel, r.id])).toEqual([["proposed_statement_changes", "thm:main"], ["open_obligations", "thm:main"]]);
    expect(pr.approval).toEqual([]);
    expect(deriveStatus(head, "thm:main")).toBe("proved");
    expect(deriveStatus(head, "lem:helper")).toBe("proved");
  });

  it("does not let a re-emitted existing statement manufacture prose ownership", async () => {
    const cited = openCore().statements.find((statement) => statement.id === "lem:cited")!;
    const { pr, head } = await openPr({
      store, base, round: 1,
      submissions: [{
        unit: "u1", targets: ["lem:helper"], proseRole: "owner", output: out({
          added_lemmas: [cited],
          prose_updates: {
            statement_notes: [{ id: "lem:cited", gap: "smuggled non-target note" }],
          },
        }),
      }],
    });
    expect(pr.units[0].rejected.map((rejection) => [rejection.channel, rejection.id, rejection.reason]))
      .toContainEqual(["prose_updates", "lem:cited", "not a target or statement created by this unit"]);
    expect(renderCore(head).statements.find((statement) => statement.id === "lem:cited")?.gap).toBe("g");
  });

  it("keeps statement prose in the leased channel and requires target ownership", async () => {
    const core = openCore();
    const helper = core.statements.find((statement) => statement.id === "lem:helper")!;
    const main = core.statements.find((statement) => statement.id === "thm:main")!;
    const { proof_tex: _helperProof, ...helperReplacement } = helper;
    const { proof_tex: _mainProof, ...mainReplacement } = main;
    const { pr, head } = await openPr({
      store, base, round: 1,
      submissions: [{
        unit: "u1", targets: ["lem:helper"], proseRole: "omit", output: out({
          proposed_core_edits: [
            {
              kind: "statement-replace", id: "lem:helper",
              proposed: { ...helperReplacement, gap: "stale helper prose" },
              reason: "mathematical metadata refresh", direction: "correct",
            },
            {
              kind: "statement-replace", id: "thm:main",
              proposed: { ...mainReplacement, gap: "smuggled non-target prose" },
              reason: "not this unit's target", direction: "correct",
            },
          ],
        }),
      }],
    });
    expect(renderCore(head).statements.find((statement) => statement.id === "lem:helper")?.gap).toBe("g");
    expect(pr.units[0].rejected.map((rejection) => [rejection.channel, rejection.id, rejection.reason]))
      .toContainEqual(["statement-replace", "thm:main", "not a target of this unit"]);
  });

  it("rejects a claim change to a live non-target statement", async () => {
    const { pr, head } = await openPr({
      store, base, round: 1,
      submissions: [{
        unit: "u1", targets: ["lem:helper"], output: out({
          proposed_statement_changes: [{
            id: "thm:main", proposed: "A materially different non-target claim.",
            reason: "not this unit's work", direction: "narrow",
          }],
        }),
      }],
    });
    expect(pr.units[0].rejected.map((rejection) => [rejection.channel, rejection.id, rejection.reason]))
      .toContainEqual(["proposed_statement_changes", "thm:main", "not a target of this unit"]);
    expect(renderCore(head).statements.find((statement) => statement.id === "thm:main")?.statement)
      .toMatch(/identified over def:class/);
  });

  it("rejects deletion of a live non-target statement", async () => {
    const { pr, head } = await openPr({
      store, base, round: 1,
      submissions: [{ unit: "u1", targets: ["lem:helper"], output: out({
        proposed_core_edits: [{
          kind: "statement-delete", id: "thm:main", reason: "not my target", direction: "delete-obsolete",
        }],
      }) }],
    });
    expect(pr.units[0].rejected.map((rejection) => [rejection.channel, rejection.id, rejection.reason]))
      .toContainEqual(["statement-delete", "thm:main", "not a target of this unit"]);
    expect(head.nodes.has("thm:main")).toBe(true);
  });

  it("records rejected symbol edits with canonical graph ids", async () => {
    const { pr } = await openPr({
      store, base, round: 1,
      submissions: [{
        unit: "u1", targets: ["thm:main"], output: out({
          proposed_core_edits: [{
            kind: "symbol-replace", name: "\\bar d",
            proposed: { name: "wrong", type: "function", def: "invalid rename" },
            reason: "bad edit", direction: "correct",
          }],
        }),
      }],
    });
    expect(pr.units[0].rejected.map((rejection) => rejection.id)).toContain("sym:\\bar d");
  });

  it("treats legacy multi-unit replay inputs without a prose role as non-owners", async () => {
    const { head } = await openPr({
      store, base, round: 1,
      submissions: [
        {
          unit: "legacy-u1", targets: ["lem:helper"], output: out({
            prose_updates: { tldr: "stale partial-component framing", statement_notes: [] },
          }),
        },
        { unit: "legacy-u2", targets: ["thm:main"], output: out({}) },
      ],
    });
    expect(renderCore(head).tldr).toBe("A fixture.");
  });

  it("treats a legacy singleton without a prose role as a non-owner", async () => {
    const { head } = await openPr({
      store, base, round: 1,
      submissions: [{ unit: "legacy-u1", targets: ["lem:helper"], output: out({
        prose_updates: { tldr: "legacy stale prose", statement_notes: [] },
      }) }],
    });
    expect(renderCore(head).tldr).toBe("A fixture.");
  });

  it("removing an assumption edge from a proved statement needs approval; a violation on an untouched node is attributed to the edit that caused it", async () => {
    // Prove everything first.
    const proved = await openPr({ store, base, round: 1, submissions: [{ unit: "u", targets: ["lem:helper", "thm:main"], output: out({ proofs: [{ id: "lem:helper", proof_tex: "p" }, { id: "thm:main", proof_tex: "q" }] }) }] });
    await mergePr({ store, pr: proved.pr, verdict: { accept: "all", note: "", by: "pipeline" } });
    const main = (await store.readRef("main"))!;
    const { pr } = await openPr({
      store, base: main, round: 2,
      submissions: [{ unit: "u", targets: ["thm:main"], output: out({
        proposed_core_edits: [
          { kind: "statement-replace", id: "thm:main", proposed: { id: "thm:main", kind: "theorem", statement: "The estimand is identified over def:class at rate $n^{-1/2}$.", depends_on: ["def:class", "lem:helper", "lem:cited"], free_symbols: ["n", "\\bar d"], status: "proved", justification: "j", gap: "g", consumer: "c" }, reason: "drop the overlap edge", direction: "correct" },
          // A symbol whose refs point at a symbol declared after it: G1 blames `symbol:<name>`.
          { kind: "symbol-add", name: "\\rho", proposed: { name: "\\rho", type: "scalar", def: "uses $\\sigma$", refs: ["\\sigma"] }, reason: "new", direction: "correct" },
          { kind: "symbol-add", name: "\\sigma", proposed: { name: "\\sigma", type: "scalar", def: "noise level" }, reason: "new", direction: "correct" },
          // A deletion an untouched statement depends on: the violation lands on the consumer.
          { kind: "definition-delete", id: "def:class", reason: "obsolete", direction: "delete-obsolete" },
        ],
      }) }],
    });
    expect(pr.approval.some((a) => a.id === "thm:main" && a.fields.some((f) => f.startsWith("depends_on −ass:overlap")))).toBe(true);
    expect(pr.dropped.map((d) => d.id)).toContain("def:class");
    expect((await loadGraph(store, pr.id)).nodes.has("def:class")).toBe(true);
  });

  it("attributes an untouched consumer's missing free symbol to the symbol deletion", async () => {
    const core = openCore();
    core.statements.push({
      id: "oeq:symbol-user", kind: "openendedquestion", statement: "Can $\\eta$ be removed?",
      depends_on: [], free_symbols: ["\\eta"], status: "to-prove", justification: "j", gap: "g", consumer: "c",
    });
    core.symbols.push({ name: "\\eta", type: "scalar", def: "legacy symbol" });
    const init = await commitOrThrow({ store, graph: graphFromCore(core), parents: [], author: "test", kind: "initial", message: "symbol fixture", expectedHead: null, detached: true });
    const { pr, head } = await openPr({
      store, base: init.id, round: 2,
      submissions: [{ unit: "u", targets: ["thm:main"], output: out({
        proposed_core_edits: [
          { kind: "symbol-delete", name: "\\eta", reason: "obsolete", direction: "delete-obsolete" },
          { kind: "symbol-add", name: "\\zeta", proposed: { name: "\\zeta", type: "scalar", def: "new symbol" }, reason: "new", direction: "correct" },
        ],
      }) }],
    });
    expect(pr.dropped.map((d) => d.id)).toEqual(["sym:\\eta"]);
    expect(head.nodes.has("sym:\\eta")).toBe(true);
    expect(head.nodes.has("sym:\\zeta")).toBe(true);
  });

  it("a PR whose base fell behind main is refused until the orchestrator picks a side per conflicting node", async () => {
    const { pr } = await openPr({
      store, base, round: 1,
      submissions: [{
        unit: "u1", targets: ["lem:helper"],
        output: out({ proofs: [{ id: "lem:helper", proof_tex: "By ass:overlap." }], proposed_core_edits: [{ kind: "bibliography-replace", key: "R1983", proposed: { key: "R1983", citation: "solver's citation" }, reason: "fix", direction: "correct" }] }),
      }],
    });
    // Meanwhile the orchestrator corrects the same bibliography row directly on main.
    const { head: mainId, graph } = await headGraph(store);
    const core = renderCore(graph);
    core.bibliography[0].citation = "orchestrator's citation";
    await commitOrThrow({ store, graph: graphFromCore(core, graph), parents: [mainId], author: "orchestrator", kind: "direct", message: "bib", expectedHead: mainId });
    const refused = await mergePr({ store, pr, verdict: { accept: "all", note: "ok", by: "pipeline" } });
    expect(refused.ok).toBe(false);
    if (refused.ok) return;
    expect(refused.unresolved.map((u) => u.id)).toEqual(["bib:R1983"]);
    expect(refused.unresolved[0].main).toBeDefined();
    expect(refused.unresolved[0].pr).toBeDefined();
    expect(await store.readRef("main")).not.toBe(base); // main untouched by the refusal
    const merged = await mergePr({ store, pr: await readPr(store, pr.id), verdict: { accept: "all", conflicts: { "bib:R1983": "main" }, note: "keep mine", by: "adjudicator" } });
    expect(merged.ok).toBe(true);
    if (!merged.ok) return;
    expect(merged.conflicts.map((c) => c.id)).toEqual(["bib:R1983"]);
    const after = renderCore(merged.graph);
    expect(after.bibliography[0].citation).toBe("orchestrator's citation");
    expect(after.statements.find((s) => s.id === "lem:helper")?.status).toBe("proved");
  });

  it("every round keeps its raw solver outputs beside the PR record", async () => {
    const { pr } = await openPr({ store, base, round: 1, submissions: [{ unit: "u1", targets: ["lem:helper"], output: out({ proofs: [{ id: "thm:main", proof_tex: "not mine" }] }) }] });
    expect(pr.inputs).toBeDefined();
    const inputs = JSON.parse(await readFile(pr.inputs!, "utf8")) as { units: Array<{ unit: string; output: { proofs: Array<{ id: string }> } }> };
    expect(inputs.units[0].output.proofs[0].id).toBe("thm:main");
    expect(pr.units[0].rejected.map((r) => r.id)).toEqual(["thm:main"]);
  });

  it("closing a PR keeps main untouched and the head addressable", async () => {
    const { pr } = await openPr({ store, base, round: 1, submissions: [{ unit: "u1", targets: ["lem:helper"], output: out({ proofs: [{ id: "lem:helper", proof_tex: "x" }] }) }] });
    await closePr(store, pr, "discarded");
    expect((await readPr(store, pr.id)).status).toBe("closed");
    expect(await store.readRef("main")).toBe(base);
    expect(store.hasCommit(pr.id)).toBe(true);
    await expect(mergePr({ store, pr: await readPr(store, pr.id), verdict: { accept: "all", note: "", by: "x" } })).rejects.toThrow(/closed/);
  });

  it("applyUnitOutput resolves an open question into a theorem with a tombstone and rewired consumers", () => {
    const core = openCore();
    core.statements.push({ id: "oeq:sharp", kind: "openendedquestion", statement: "Is the rate sharp?", depends_on: ["ass:overlap"], free_symbols: [], status: "to-prove", justification: "j", gap: "g", consumer: "c" });
    core.statements[2].depends_on.push("oeq:sharp");
    const g = graphFromCore(core);
    const head = applyUnitOutput(g, {
      unit: "u1", targets: ["oeq:sharp"],
      output: out({ resolved_oeqs: [{ source_id: "oeq:sharp", theorem: { id: "thm:sharp", kind: "theorem", statement: "The rate is sharp.", depends_on: ["ass:overlap", "oeq:sharp"], free_symbols: [], status: "proved", proof_tex: "This settles oeq:sharp." } }] }),
    });
    expect(head.rejected).toEqual([]);
    const rendered = renderCore(head.graph);
    expect(rendered.statements.map((s) => s.id)).not.toContain("oeq:sharp");
    expect(rendered.statements.find((s) => s.id === "thm:main")?.depends_on).toContain("thm:sharp");
    expect(rendered.statements.find((s) => s.id === "thm:sharp")?.depends_on).not.toContain("thm:sharp");
    expect(head.graph.nodes.get("oeq:sharp")).toMatchObject({ body: { resolved_by: "thm:sharp" } });
  });

  it("reopens an older resolution when a later edit stales its answer", () => {
    const core = openCore();
    core.statements.push({ id: "oeq:sharp", kind: "openendedquestion", statement: "Is the rate sharp?", depends_on: ["ass:overlap"], free_symbols: [], status: "to-prove", justification: "j", gap: "g", consumer: "c" });
    const resolved = applyUnitOutput(graphFromCore(core), {
      unit: "u1", targets: ["oeq:sharp"],
      output: out({ resolved_oeqs: [{ source_id: "oeq:sharp", theorem: { id: "thm:sharp", kind: "theorem", statement: "The rate is sharp.", depends_on: ["ass:overlap"], free_symbols: [], status: "proved", proof_tex: "By ass:overlap." } }] }),
    }).graph;
    const edited = renderCore(resolved);
    edited.assumptions[0].condition = "$\\bar d \\ge 2\\epsilon$";
    const candidate = graphFromCore(edited, resolved);
    expect(deriveStatus(candidate, "thm:sharp")).toBe("to-prove");

    const reconciled = reconcileToBase(resolved, candidate);
    expect(reconciled.dropped).toEqual([]);
    expect(reconciled.graph.nodes.get("oeq:sharp")).not.toMatchObject({ body: { resolved_by: expect.anything() } });
  });

  it("accepts at most one answer for each open question in a solver payload", () => {
    const core = openCore();
    core.statements.push({ id: "oeq:sharp", kind: "openendedquestion", statement: "Is the rate sharp?", depends_on: ["ass:overlap"], free_symbols: [], status: "to-prove", justification: "j", gap: "g", consumer: "c" });
    const graph = applyUnitOutput(graphFromCore(core), {
      unit: "u1", targets: ["oeq:sharp"], output: out({ resolved_oeqs: [
        { source_id: "oeq:sharp", theorem: { id: "thm:first", kind: "theorem", statement: "First answer.", depends_on: ["oeq:sharp"], free_symbols: [], status: "proved", proof_tex: "First." } },
        { source_id: "oeq:sharp", theorem: { id: "thm:second", kind: "theorem", statement: "Second answer.", depends_on: ["oeq:sharp"], free_symbols: [], status: "proved", proof_tex: "Second." } },
      ] }),
    });
    expect(graph.graph.nodes.get("oeq:sharp")).toMatchObject({ body: { resolved_by: "thm:first" } });
    expect(graph.graph.nodes.has("thm:first")).toBe(true);
    expect(graph.graph.nodes.has("thm:second")).toBe(false);
    expect(graph.rejected).toContainEqual(expect.objectContaining({ channel: "resolved_oeqs", id: "oeq:sharp", reason: "not a live open question" }));
  });

  it("keeps a resolution answer atomic against later channels in the same payload", () => {
    const core = openCore();
    core.statements.push({ id: "oeq:sharp", kind: "openendedquestion", statement: "Is the rate sharp?", depends_on: [], free_symbols: [], status: "to-prove", justification: "j", gap: "g", consumer: "c" });
    const result = applyUnitOutput(graphFromCore(core), { unit: "u1", targets: ["oeq:sharp"], output: out({
      resolved_oeqs: [{ source_id: "oeq:sharp", theorem: { id: "thm:answer", kind: "theorem", statement: "The answer.", depends_on: ["oeq:sharp"], free_symbols: [], status: "proved", proof_tex: "Resolution proof." } }],
      proofs: [{ id: "thm:answer", proof_tex: "Cross-channel proof." }],
    }) });
    expect(result.graph.nodes.get("thm:answer")).toMatchObject({ body: { proof_tex: "Resolution proof." } });
    expect(result.rejected).toContainEqual(expect.objectContaining({ channel: "resolved_oeqs", id: "thm:answer", reason: expect.stringContaining("another output channel") }));
  });

  it("excludes a rejected existing-id resolution from provenance cleanup", async () => {
    const core = openCore();
    core.statements.push({ id: "oeq:sharp", kind: "openendedquestion", statement: "Is the rate sharp?", depends_on: [], free_symbols: [], status: "to-prove", justification: "j", gap: "g", consumer: "thm:main" });
    core.statements.find((statement) => statement.id === "thm:main")!.depends_on.push("oeq:sharp");
    const initial = await commitOrThrow({ store, graph: graphFromCore(core), parents: [base], author: "test", kind: "direct", message: "question", expectedHead: base });
    base = initial.id;
    const { pr, head } = await openPr({ store, base, round: 1, submissions: [{ unit: "u1", targets: ["oeq:sharp"], output: out({
      resolved_oeqs: [{ source_id: "oeq:sharp", theorem: { id: "thm:main", kind: "theorem", statement: "The answer.", depends_on: ["oeq:sharp"], free_symbols: [], status: "proved", proof_tex: "Answer." } }],
    }) }] });
    expect(pr.units[0].rejected).toContainEqual(expect.objectContaining({ id: "oeq:sharp", reason: expect.stringContaining("already exists") }));
    expect(head.nodes.get("oeq:sharp")).not.toMatchObject({ body: { resolved_by: expect.anything() } });
    expect(head.nodes.get("thm:main")).toMatchObject({ body: { depends_on: expect.arrayContaining(["oeq:sharp"]) } });
  });

  it("reserves OEQ sources and answer IDs across parallel solver units", async () => {
    const core = openCore();
    for (const id of ["oeq:first", "oeq:second"]) core.statements.push({ id, kind: "openendedquestion", statement: `Question ${id}?`, depends_on: [], free_symbols: [], status: "to-prove", justification: "j", gap: "g", consumer: "c" });
    const initial = await commitOrThrow({ store, graph: graphFromCore(core), parents: [base], author: "test", kind: "direct", message: "questions", expectedHead: base });
    base = initial.id;
    const answer = (source_id: string, theoremId: string) => ({ source_id, theorem: { id: theoremId, kind: "theorem" as const, statement: "The shared answer claim.", depends_on: [source_id], free_symbols: [], status: "proved" as const, proof_tex: "Proof." } });
    const { pr, head } = await openPr({ store, base, round: 1, submissions: [
      { unit: "u1", targets: ["oeq:first"], output: out({ resolved_oeqs: [answer("oeq:first", "thm:answer")] }) },
      { unit: "u2", targets: ["oeq:first"], output: out({ resolved_oeqs: [answer("oeq:first", "thm:other")] }) },
      { unit: "u3", targets: ["oeq:second"], output: out({ resolved_oeqs: [answer("oeq:second", "thm:answer")] }) },
    ] });
    expect(head.nodes.has("thm:answer")).toBe(true);
    expect(head.nodes.has("thm:other")).toBe(false);
    expect(head.nodes.get("oeq:first")).toMatchObject({ body: { resolved_by: "thm:answer" } });
    expect(head.nodes.get("oeq:second")).not.toMatchObject({ body: { resolved_by: expect.anything() } });
    expect(pr.units[1].rejected).toContainEqual(expect.objectContaining({ id: "oeq:first", reason: expect.stringContaining("reserved") }));
    expect(pr.units[2].rejected).toContainEqual(expect.objectContaining({ id: "oeq:second", reason: expect.stringContaining("answer id") }));
  });

  it("does not bind an OEQ to another unit's unrelated same-id theorem", async () => {
    const core = openCore();
    core.statements.push({ id: "oeq:sharp", kind: "openendedquestion", statement: "Is the rate sharp?", depends_on: [], free_symbols: [], status: "to-prove", justification: "j", gap: "g", consumer: "thm:main" });
    core.statements.find((statement) => statement.id === "thm:main")!.depends_on.push("oeq:sharp");
    core.symbols.push({ name: "rSharp", type: "rate", def: "the sharp rate", ref: "oeq:sharp" });
    const initial = await commitOrThrow({ store, graph: graphFromCore(core), parents: [base], author: "test", kind: "direct", message: "question", expectedHead: base });
    base = initial.id;
    const { head } = await openPr({ store, base, round: 1, submissions: [
      { unit: "u1", targets: ["lem:helper"], output: out({ added_lemmas: [{ id: "thm:collision", kind: "theorem", statement: "The answer to the rate question.", depends_on: [], free_symbols: [], status: "proved", proof_tex: "Unrelated proof." }] }) },
      { unit: "u2", targets: ["oeq:sharp"], output: out({ resolved_oeqs: [{ source_id: "oeq:sharp", theorem: { id: "thm:collision", kind: "theorem", statement: "The answer to the rate question.", depends_on: ["oeq:sharp"], free_symbols: [], status: "proved", proof_tex: "Answer proof." } }] }) },
    ] });
    expect(head.nodes.get("oeq:sharp")).not.toMatchObject({ body: { resolved_by: expect.anything() } });
    expect(head.nodes.get("sym:rSharp")).toMatchObject({ body: { ref: "oeq:sharp" } });
    expect(head.nodes.get("thm:collision")).toMatchObject({ body: { proof_tex: "Unrelated proof." } });
    expect(head.nodes.get("thm:main")).toMatchObject({ body: { depends_on: expect.arrayContaining(["oeq:sharp"]) } });
  });

  it("reverses resolution rewires when three-way conflict keeps a live source question", async () => {
    const core = openCore();
    core.statements.push({ id: "oeq:sharp", kind: "openendedquestion", statement: "Is the rate sharp?", depends_on: [], free_symbols: [], status: "to-prove", justification: "j", gap: "g", consumer: "thm:main" });
    core.statements.find((statement) => statement.id === "thm:main")!.depends_on.push("oeq:sharp");
    core.symbols.push({ name: "rSharp", type: "rate", def: "the sharp rate", ref: "oeq:sharp" });
    const initial = await commitOrThrow({ store, graph: graphFromCore(core), parents: [base], author: "test", kind: "direct", message: "question", expectedHead: base });
    base = initial.id;
    const { pr } = await openPr({ store, base, round: 1, submissions: [{ unit: "u1", targets: ["oeq:sharp"], output: out({
      resolved_oeqs: [{ source_id: "oeq:sharp", theorem: { id: "thm:answer", kind: "theorem", statement: "A diagnostic answer.", depends_on: ["oeq:sharp"], free_symbols: [], status: "proved", proof_tex: "Proof." } }],
    }) }] });
    const mainCore = renderCore(await loadGraph(store, base));
    mainCore.statements.find((statement) => statement.id === "oeq:sharp")!.statement = "Is the corrected rate sharp?";
    await commitOrThrow({ store, graph: graphFromCore(mainCore, await loadGraph(store, base)), parents: [base], author: "main", kind: "direct", message: "correct question", expectedHead: base });
    const merged = await mergePr({ store, pr, verdict: { accept: "all", conflicts: { "oeq:sharp": "main" }, note: "keep corrected question", by: "adjudicator" } });
    expect(merged.ok).toBe(true);
    if (!merged.ok) return;
    expect(merged.graph.nodes.get("oeq:sharp")).toMatchObject({ body: { statement: "Is the corrected rate sharp?" } });
    expect(merged.graph.nodes.get("oeq:sharp")).not.toMatchObject({ body: { resolved_by: expect.anything() } });
    expect(merged.graph.nodes.get("sym:rSharp")).toMatchObject({ body: { ref: "oeq:sharp" } });
    expect(merged.graph.nodes.get("thm:main")).toMatchObject({ body: { depends_on: expect.arrayContaining(["oeq:sharp"]) } });
    expect(deriveStatus(merged.graph, "thm:answer")).toBe("proved");
  });

  it("detaches a resolution when three-way merge keeps source-pointing symbol content", async () => {
    const core = openCore();
    core.statements.push({ id: "oeq:sharp", kind: "openendedquestion", statement: "Is the rate sharp?", depends_on: [], free_symbols: [], status: "to-prove", justification: "j", gap: "g", consumer: "c" });
    core.symbols.push({ name: "rSharp", type: "rate", def: "old definition", ref: "oeq:sharp" });
    const initial = await commitOrThrow({ store, graph: graphFromCore(core), parents: [base], author: "test", kind: "direct", message: "question", expectedHead: base });
    base = initial.id;
    const { pr } = await openPr({ store, base, round: 1, submissions: [{ unit: "u1", targets: ["oeq:sharp"], output: out({
      resolved_oeqs: [{ source_id: "oeq:sharp", theorem: { id: "thm:answer", kind: "theorem", statement: "A diagnostic answer.", depends_on: ["oeq:sharp"], free_symbols: [], status: "proved", proof_tex: "Proof." } }],
    }) }] });
    const mainCore = renderCore(await loadGraph(store, base));
    const symbol = mainCore.symbols.find((candidate) => candidate.name === "rSharp")!;
    symbol.def = "new definition on main";
    await commitOrThrow({ store, graph: graphFromCore(mainCore, await loadGraph(store, base)), parents: [base], author: "main", kind: "direct", message: "refine symbol", expectedHead: base });
    const merged = await mergePr({ store, pr, verdict: { accept: "all", conflicts: { "sym:rSharp": "main" }, note: "keep main symbol", by: "adjudicator" } });
    expect(merged.ok).toBe(true);
    if (!merged.ok) return;
    expect(merged.graph.nodes.get("sym:rSharp")).toMatchObject({ body: { def: "new definition on main", ref: "oeq:sharp" } });
    expect(merged.graph.nodes.get("oeq:sharp")).not.toMatchObject({ body: { resolved_by: expect.anything() } });
    expect(deriveStatus(merged.graph, "thm:answer")).toBe("proved");
  });

  it("keeps an explicitly rejected symbol reference and detaches its accepted diagnostic answer", async () => {
    const core = openCore();
    core.statements.push({ id: "oeq:sharp", kind: "openendedquestion", statement: "Is the rate sharp?", depends_on: ["ass:overlap"], free_symbols: [], status: "to-prove", justification: "j", gap: "g", consumer: "c" });
    core.statements.find((statement) => statement.id === "thm:main")!.depends_on.push("oeq:sharp");
    core.symbols.push({ name: "rSharp", type: "rate", def: "the sharp rate", ref: "oeq:sharp" });
    const initial = await commitOrThrow({ store, graph: graphFromCore(core), parents: [base], author: "test", kind: "direct", message: "question", expectedHead: base });
    base = initial.id;
    const { pr } = await openPr({
      store, base, round: 1,
      submissions: [{ unit: "u1", targets: ["oeq:sharp"], output: out({
        resolved_oeqs: [{ source_id: "oeq:sharp", theorem: { id: "thm:not-sharp", kind: "theorem", statement: "The frozen handle in oeq:sharp is not sharp.", depends_on: ["ass:overlap", "oeq:sharp"], free_symbols: [], status: "proved", proof_tex: "This resolves oeq:sharp by counterexample." } }],
      }) }],
    });
    expect(pr.approval.map((item) => item.id)).toEqual(expect.arrayContaining(["thm:not-sharp", "sym:rSharp"]));
    const result = await mergePr({ store, pr, verdict: { accept: ["thm:not-sharp"], reject: ["sym:rSharp"], note: "keep the question live", by: "adjudicator" } });
    expect(result.ok).toBe(true);
    if (!result.ok) return;
    expect(result.graph.nodes.get("sym:rSharp")).toMatchObject({ body: { ref: "oeq:sharp" } });
    expect(result.graph.nodes.get("oeq:sharp")).not.toMatchObject({ body: { resolved_by: expect.anything() } });
    expect(result.graph.nodes.get("thm:not-sharp")).toMatchObject({ body: { depends_on: ["ass:overlap"] } });
    expect(result.graph.nodes.get("thm:not-sharp")).not.toMatchObject({ body: { proof_basis: expect.objectContaining({ "oeq:sharp": expect.anything() }) } });
    expect(deriveStatus(result.graph, "thm:not-sharp")).toBe("proved");
    expect(result.graph.nodes.get("thm:main")).toMatchObject({ body: { depends_on: expect.arrayContaining(["oeq:sharp"]) } });
    expect((result.graph.nodes.get("thm:main") as { body: { depends_on: string[] } }).body.depends_on).not.toContain("thm:not-sharp");
  });

  it("keeps the ordinary accepted OEQ-resolution wiring", async () => {
    const core = openCore();
    core.statements.push({ id: "oeq:sharp", kind: "openendedquestion", statement: "Is the rate sharp?", depends_on: ["ass:overlap"], free_symbols: [], status: "to-prove", justification: "j", gap: "g", consumer: "c" });
    core.symbols.push({ name: "rSharp", type: "rate", def: "the sharp rate", ref: "oeq:sharp" });
    const initial = await commitOrThrow({ store, graph: graphFromCore(core), parents: [base], author: "test", kind: "direct", message: "question", expectedHead: base });
    base = initial.id;
    const { pr } = await openPr({
      store, base, round: 1,
      submissions: [{ unit: "u1", targets: ["oeq:sharp"], output: out({
        resolved_oeqs: [{ source_id: "oeq:sharp", theorem: { id: "thm:sharp", kind: "theorem", statement: "The rate is sharp.", depends_on: ["ass:overlap", "oeq:sharp"], free_symbols: [], status: "proved", proof_tex: "A proof." } }],
      }) }],
    });
    const result = await mergePr({ store, pr, verdict: { accept: "all", note: "resolved", by: "adjudicator" } });
    expect(result.ok).toBe(true);
    if (!result.ok) return;
    expect(result.graph.nodes.get("sym:rSharp")).toMatchObject({ body: { ref: "thm:sharp" } });
    expect(result.graph.nodes.get("oeq:sharp")).toMatchObject({ body: { resolved_by: "thm:sharp" } });
  });

  it("reopens an interacting resolution whose fold-time rewire is absent from its proof basis", async () => {
    const core = openCore();
    for (const id of ["oeq:q1", "oeq:q2"]) core.statements.push({ id, kind: "openendedquestion", statement: id, depends_on: [], free_symbols: [], status: "to-prove", justification: "j", gap: "g", consumer: "c" });
    const initial = await commitOrThrow({ store, graph: graphFromCore(core), parents: [base], author: "test", kind: "direct", message: "questions", expectedHead: base });
    base = initial.id;
    const answer = (source_id: string, id: string, depends_on: string[]) => ({ source_id, theorem: { id, kind: "theorem" as const, statement: `Answer ${id}.`, depends_on, free_symbols: [], status: "proved" as const, proof_tex: "Proof." } });
    const { head } = await openPr({ store, base, round: 1, submissions: [
      { unit: "u1", targets: ["oeq:q1"], output: out({ resolved_oeqs: [answer("oeq:q1", "thm:a1", ["oeq:q1", "oeq:q2"])] }) },
      { unit: "u2", targets: ["oeq:q2"], output: out({ resolved_oeqs: [answer("oeq:q2", "thm:a2", ["oeq:q2"])] }) },
    ] });
    expect(head.nodes.get("oeq:q1")).not.toMatchObject({ body: { resolved_by: expect.anything() } });
    expect(head.nodes.get("oeq:q2")).toMatchObject({ body: { resolved_by: "thm:a2" } });
    expect(head.nodes.has("thm:a1")).toBe(false);
  });

  it("keeps an OEQ live while a definition structurally references it", async () => {
    const core = openCore();
    core.statements.push({ id: "oeq:sharp", kind: "openendedquestion", statement: "Is it sharp?", depends_on: [], free_symbols: [], status: "to-prove", justification: "j", gap: "g", consumer: "def:qinput" });
    core.definitions.push({ id: "def:qinput", name: "QInput", construction: "an ordinary object", inputs: ["input specified by oeq:sharp"] });
    const initial = await commitOrThrow({ store, graph: graphFromCore(core), parents: [base], author: "test", kind: "direct", message: "question input", expectedHead: base });
    base = initial.id;
    const { head } = await openPr({ store, base, round: 1, submissions: [{ unit: "u1", targets: ["oeq:sharp"], output: out({
      resolved_oeqs: [{ source_id: "oeq:sharp", theorem: { id: "thm:answer", kind: "theorem", statement: "A diagnostic answer.", depends_on: ["oeq:sharp"], free_symbols: [], status: "proved", proof_tex: "Proof." } }],
    }) }] });
    expect(head.nodes.get("oeq:sharp")).not.toMatchObject({ body: { resolved_by: expect.anything() } });
    expect(head.nodes.get("def:qinput")).toMatchObject({ body: { inputs: ["input specified by oeq:sharp"] } });
  });

  it("audit fixes: typo in --accept throws; rejecting a claim change keeps the proof (stale); cascaded drops are recorded on the PR", async () => {
    const { pr } = await openPr({
      store, base, round: 1,
      submissions: [{ unit: "u1", targets: ["thm:main"], output: out({
        proposed_statement_changes: [{ id: "thm:main", proposed: "A narrowed main claim.", reason: "r", direction: "narrow" }],
        proofs: [{ id: "thm:main", proof_tex: "proof of the narrowed claim" }],
        open_obligations: [],
        proposed_assumptions: [{ id: "ass:extra", condition: "an extra condition", free_symbols: [], reason: "needed", standard_or_novel: "novel: new", not_crux: "side" }],
        proposed_core_edits: [{ kind: "definition-add", id: "def:aux", proposed: { id: "def:aux", name: "Q", construction: "$\\{P : \\text{ass:extra}\\}$", by_member_properties: ["ass:extra"] }, reason: "class", direction: "correct" }],
      }) }],
    });
    await expect(mergePr({ store, pr, verdict: { accept: ["thm:mian"], note: "typo", by: "x" } })).rejects.toThrow(/not an approval item/);
    expect((await readPr(store, pr.id)).status).toBe("open");
    const merged = await mergePr({ store, pr, verdict: { accept: ["def:aux"], reject: ["thm:main", "ass:extra"], note: "keep the claim", by: "adjudicator" } });
    expect(merged.ok).toBe(true);
    const after = (await headGraph(store)).graph;
    const main = after.nodes.get("thm:main");
    expect(main?.node_type === "statement" && main.body.proof_tex).toBe("proof of the narrowed claim"); // kept as stale bytes
    expect(deriveStatus(after, "thm:main")).toBe("to-prove");
    expect(renderCore(after).statements.find((s) => s.id === "thm:main")?.statement).toMatch(/n\^\{-1\/2\}/);
    const record = await readPr(store, pr.id);
    expect(record.dropped.map((d) => d.id)).toContain("def:aux"); // dropped with the rejected assumption, and recorded
  });

  it("attributes a violation to a touched node by its display name (a definition name quoted by G3)", async () => {
    const { pr, head } = await openPr({
      store, base, round: 1,
      submissions: [{ unit: "u1", targets: ["lem:helper"], output: out({
        proofs: [{ id: "lem:helper", proof_tex: "By ass:overlap." }],
        // A class named like a word the fixture assumption's condition uses in a membership phrase: G3 fires ON the untouched assumption.
        proposed_core_edits: [{ kind: "definition-add", id: "def:margin-class", proposed: { id: "def:margin-class", name: "epsilon", construction: "$\\{P : \\text{ass:overlap}\\}$", by_member_properties: ["ass:overlap"] }, reason: "new class", direction: "correct" }],
      }) }],
    });
    // Either the addition landed (no violation in this fixture) or it alone was dropped — never the proof.
    expect(deriveStatus(head, "lem:helper")).toBe("proved");
    expect(pr.dropped.every((d) => d.id === "def:margin-class")).toBe(true);
  });

  it("layout never drops content: two units' new symbols referencing each other, and a replaced symbol referencing a new one, all land in reference order", async () => {
    const sym = (name: string, refs: string[] = []) => ({ kind: "symbol-add" as const, name, proposed: { name, type: "scalar", def: `uses ${refs.join(",") || "nothing"}`, refs }, reason: "new", direction: "correct" as const });
    const { pr, head } = await openPr({
      store, base, round: 1,
      submissions: [
        { unit: "u1", targets: ["thm:main"], output: out({ proposed_core_edits: [
          sym("A"), sym("B", ["A"]),
          // an EARLY existing symbol now references a symbol added this round
          { kind: "symbol-replace", name: "\\bar d", proposed: { name: "\\bar d", type: "function", space: "[0,1]", def: "the overlap margin, via B", refs: ["B"] }, reason: "refine", direction: "correct" },
        ] }) },
        // numbered from the same base as u1: positions collide at fold time
        { unit: "u2", targets: ["lem:helper"], output: out({ proposed_core_edits: [sym("C", ["B"])] }) },
      ],
    });
    expect(pr.dropped).toEqual([]);
    const names = renderCore(head).symbols.map((x) => x.name);
    expect(names.indexOf("A")).toBeLessThan(names.indexOf("B"));
    expect(names.indexOf("B")).toBeLessThan(names.indexOf("C"));
    expect(names.indexOf("B")).toBeLessThan(names.indexOf("\\bar d"));
  });

  it("verified attribution: a definition named like a deleted symbol is not blamed for the symbol's dangling declaration", async () => {
    // base: a symbol 'P' (the same display name as def:class) declared by the untouched lem:cited
    const core = openCore();
    core.symbols.push({ name: "P", type: "class", def: "the model class" });
    core.statements.find((x) => x.id === "lem:cited")!.free_symbols = ["n", "P"];
    const init = await commitOrThrow({ store, graph: graphFromCore(core), parents: [base], author: "test", kind: "direct", message: "add P", expectedHead: base });
    const { pr, head } = await openPr({
      store, base: init.id, round: 1,
      submissions: [{ unit: "u1", targets: ["thm:main"], output: out({
        proposed_core_edits: [{ kind: "symbol-delete", name: "P", reason: "obsolete", direction: "delete-obsolete" }],
        proposed_definition_changes: [{ id: "def:class", current: "x", proposed: "$\\{P : \\text{ass:overlap holds twice}\\}$", reason: "fix", direction: "correct" }],
      }) }],
    });
    expect(pr.dropped.map((d) => d.id)).toEqual(["sym:P"]); // the deletion is reverted (lossless); the definition change lands
    const def = head.nodes.get("def:class");
    expect(def?.node_type === "definition" && def.body.construction).toContain("twice");
    expect(head.nodes.has("sym:P")).toBe(true);
  });

  it("pr reapply replays the raw inputs against a repaired main: the deletion that could not land lands, the old PR is closed", async () => {
    const { pr } = await openPr({
      store, base, round: 1,
      submissions: [{ unit: "u1", targets: ["thm:main"], output: out({
        proposed_core_edits: [{ kind: "symbol-delete", name: "n", reason: "obsolete", direction: "delete-obsolete" }],
        proofs: [{ id: "thm:main", proof_tex: "Proof written alongside the deletion." }],
      }) }],
    });
    expect(pr.dropped.map((d) => d.id)).toEqual(["sym:n"]); // lem:cited and thm:main still declare n
    expect(describePr(pr, await loadGraph(store, pr.base), await loadGraph(store, pr.id))).toContain(`pr reapply ${pr.id.slice(0, 12)}`);
    // the orchestrator repairs main: nothing declares n any more
    const core = renderCore(await loadGraph(store, base));
    for (const st of core.statements) st.free_symbols = (st.free_symbols ?? []).filter((x) => x !== "n");
    const fixed = await commitOrThrow({ store, graph: graphFromCore(core, await loadGraph(store, base)), parents: [base], author: "orchestrator", kind: "direct", message: "drop n", expectedHead: base });
    const { pr: next, head } = await reapplyPr(store, pr, { base: fixed.id, note: "n is unused now" });
    expect(next.dropped).toEqual([]);
    expect(next.reapplied_from).toBe(pr.id);
    expect(next.base).toBe(fixed.id);
    expect(head.nodes.has("sym:n")).toBe(false);
    const main = head.nodes.get("thm:main");
    expect(main?.node_type === "statement" && main.body.proof_tex).toContain("alongside");
    expect((await readPr(store, pr.id)).status).toBe("closed");
    expect((await listPrs(store, "open")).map((x) => x.id)).toEqual([next.id]);
  });

  it("does not replay snapshot-derived owner prose onto a changed base", async () => {
    const { pr } = await openPr({
      store, base, round: 1,
      submissions: [{
        unit: "u1", targets: ["lem:helper"], proseRole: "owner",
        output: out({
          proofs: [{ id: "lem:helper", proof_tex: "A refreshed proof." }],
          prose_updates: { tldr: "stale snapshot prose", statement_notes: [] },
        }),
      }],
    });
    const core = renderCore(await loadGraph(store, base));
    core.tldr = "newer main prose";
    const fixed = await commitOrThrow({
      store, graph: graphFromCore(core, await loadGraph(store, base)), parents: [base],
      author: "orchestrator", kind: "direct", message: "refresh prose", expectedHead: base,
    });
    const { head } = await reapplyPr(store, pr, { base: fixed.id, note: "retain repaired main prose" });
    expect(renderCore(head).tldr).toBe("newer main prose");
  });

  it("refuses leased prose when main advances on a different node", async () => {
    const { pr } = await openPr({
      store, base, round: 1,
      submissions: [{
        unit: "u1", targets: ["lem:helper"], proseRole: "owner", output: out({
          proofs: [{ id: "lem:helper", proof_tex: "A refreshed proof." }],
          prose_updates: { tldr: "base-derived prose", statement_notes: [] },
        }),
      }],
    });
    const core = renderCore(await loadGraph(store, base));
    core.bibliography[0].citation = "a newer citation on main";
    await commitOrThrow({
      store, graph: graphFromCore(core, await loadGraph(store, base)), parents: [base],
      author: "orchestrator", kind: "direct", message: "advance main", expectedHead: base,
    });
    const result = await mergePr({ store, pr, verdict: { accept: "all", note: "try stale prose", by: "test" } });
    expect(result.ok).toBe(false);
    if (!result.ok) expect(result.unresolved.map((item) => item.reason)).toContain("leased paper prose was authored against an older base; reapply or rerun before merge");
  });

});

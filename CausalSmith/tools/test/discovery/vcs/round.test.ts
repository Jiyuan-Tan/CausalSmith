import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { afterEach, beforeEach, describe, expect, it } from "vitest";
import type { PipelineContext, StateJson } from "../../../src/types.js";
import type { StageDeps } from "../../../src/pipeline_support.js";
import { canonicalLeanSubdir, promptPath } from "../../../src/paths.js";
import { CoreSchema, type Core } from "../../../src/discovery/core/schema.js";
import { coreJsonPath } from "../../../src/discovery/stages/d0_core.js";
import { protoCoreJsonPath } from "../../../src/discovery/stages/neg1_2_author.js";
import { appendEscalationLog } from "../../../src/discovery/escalation_log.js";
import { headGraph } from "../../../src/discovery/vcs/commit.js";
import { listPrs, mergePr, readPr } from "../../../src/discovery/vcs/pr.js";
import { runVcsSolveRound } from "../../../src/discovery/vcs/round.js";
import type { SolveUnitOutput } from "../../../src/discovery/solve/schemas.js";
import { scopeSubmissionProse } from "../../../src/discovery/vcs/pr.js";
import { VcsStore } from "../../../src/discovery/vcs/store.js";
import { deriveStatus } from "../../../src/discovery/vcs/validity.js";
import { fixtureCore } from "./fixture.js";

// A D0 round end to end with a scripted solver: store auto-initialized from the
// proto, units dispatched for what is open, outputs folded into a PR, additive
// rounds merged, claim changes halted for a verdict, directives dispatched, and
// a resume with an unchanged prompt costing no model call.

type Script = (targets: string[], prompt: string) => Record<string, unknown>;

function companionize(payload: Record<string, unknown>): { payload: Record<string, unknown>; companion: string } {
  const longFields = new Set(["statement", "proof_tex", "construction", "condition", "partial_result"]);
  const blocks: string[] = [];
  const visit = (value: unknown, path = ""): void => {
    if (Array.isArray(value)) {
      value.forEach((item, i) => visit(item, `${path}[${i}]`));
      return;
    }
    if (value === null || typeof value !== "object") return;
    for (const [key, child] of Object.entries(value as Record<string, unknown>)) {
      const alias = key === "proposed" &&
        /(?:^|\.)(?:proposed_statement_changes|proposed_definition_changes)\[\d+\]$/.test(path);
      if ((longFields.has(key) || alias) && typeof child === "string") {
        const ref = `fixture-${blocks.length}`;
        blocks.push(`%%% FIELD ${ref}\n${child}\n`);
        (value as Record<string, unknown>)[key] = { tex_ref: ref };
      } else {
        visit(child, path.length === 0 ? key : `${path}.${key}`);
      }
    }
  };
  visit(payload);
  return { payload, companion: blocks.join("") };
}

function scriptedSolver(script: Script): StageDeps & { calls: string[][] } {
  const calls: string[][] = [];
  return {
    calls,
    runCodex: async ({ prompt }: { prompt: string }) => {
      const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
      const segment = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
      const targets = (JSON.parse(segment.slice(segment.indexOf("["), segment.lastIndexOf("]") + 1)) as Array<{ id: string }>).map((t) => t.id);
      calls.push(targets);
      const output = companionize(script(targets, prompt));
      const companionPath = /SOLVE_COMPANION_PATH:\s*(\S+)/.exec(prompt)![1];
      if (output.companion.length > 0) {
        await mkdir(path.dirname(companionPath), { recursive: true });
        await writeFile(companionPath, output.companion, "utf8");
      }
      await writeFile(outPath, JSON.stringify(output.payload), "utf8");
      return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
    },
    runClaude: async () => { throw new Error("unused"); },
    lean: undefined as never,
  } as StageDeps & { calls: string[][] };
}

describe("vcs solve round", () => {
  let repoRoot: string;
  let ctx: PipelineContext;
  let state: StateJson;
  const proto = (): Core => {
    const core = fixtureCore();
    for (const s of core.statements) if (s.status === "proved") { s.status = "to-prove"; delete s.proof_tex; }
    return core;
  };
  beforeEach(async () => {
    repoRoot = await mkdtemp(path.join(os.tmpdir(), "vcs-round-"));
    ctx = { repoRoot, qid: "stat_vcs_fixture", specialization: "v1", dryRun: false, resume: false };
    for (const name of ["stage0_common_discovery.txt", "stage0_setup_stat.txt", "stage0_solve.txt"]) {
      const target = promptPath(repoRoot, name);
      await mkdir(path.dirname(target), { recursive: true });
      await writeFile(target, `stub ${name}`, "utf8");
    }
    const protoPath = protoCoreJsonPath(ctx);
    await mkdir(path.dirname(protoPath), { recursive: true });
    await writeFile(protoPath, JSON.stringify(proto()), "utf8");
    state = {
      stage_completed: "-0.5",
      lean_subdir: canonicalLeanSubdir(ctx.qid),
      design_decisions: {},
      added_assumptions: [],
      proposed_from: { topic: "t", novelty_target: "field", cluster: "stat" },
      flags: {},
    } as unknown as StateJson;
  });
  afterEach(async () => { await rm(repoRoot, { recursive: true, force: true }); });

  const readCore = async (): Promise<Core> => CoreSchema.parse(JSON.parse(await readFile(coreJsonPath(ctx), "utf8")));

  it("deterministically scopes prose to its unit lease before PR routing", () => {
    const output = {
      proofs: [], resolved_oeqs: [], added_lemmas: [], proposed_statement_changes: [],
      proposed_definition_changes: [], proposed_assumptions: [], proposed_core_edits: [],
      open_obligations: [],
      prose_updates: {
        tldr: "canonical paper prose",
        statement_notes: [
          { id: "lem:helper", gap: "owned" },
          { id: "thm:main", gap: "sibling" },
        ],
      },
    } satisfies SolveUnitOutput;

    const owner = scopeSubmissionProse({ unit: "u1", targets: ["lem:helper"], output }, "owner").output;
    expect(owner.prose_updates?.tldr).toBe("canonical paper prose");
    expect(owner.prose_updates?.statement_notes.map((note) => note.id)).toEqual(["lem:helper"]);

    const nonOwner = scopeSubmissionProse({ unit: "u2", targets: ["thm:main"], output }, "omit").output;
    expect(nonOwner.prose_updates).toBeUndefined();
    expect(output.prose_updates?.statement_notes.map((note) => note.id)).toEqual(["lem:helper", "thm:main"]);
  });

  it("does not open a mergeable PR when one unit of a directive round fails", async () => {
    const mixed = proto();
    mixed.statements.push({
      id: "lem:unrelated", kind: "lemma", statement: "An unrelated finite-sample fact.",
      depends_on: [], free_symbols: ["n"], status: "to-prove",
      justification: "j", gap: "g", consumer: "c",
    });
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(mixed), "utf8");
    await appendEscalationLog(ctx, { round: 1, directive: "Revalidate the whole paper." });
    const deps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const segment = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = (JSON.parse(segment.slice(segment.indexOf("["), segment.lastIndexOf("]") + 1)) as Array<{ id: string }>).map((target) => target.id);
        if (targets.includes("lem:helper")) throw new Error("owner unit failed");
        await writeFile(outPath, JSON.stringify({ proofs: targets.map((id) => ({ id, proof_tex: "partial proof" })) }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    } as StageDeps;
    const outcome = await runVcsSolveRound({ ctx, state, deps, round: 1 });
    expect(outcome.kind).toBe("incomplete");
    expect(outcome.message).toMatch(/directive round 1 is atomic/);
    expect(await listPrs(VcsStore.at(ctx), "open")).toEqual([]);
  });

  it("returns an atomic incomplete result when every directive unit fails", async () => {
    await appendEscalationLog(ctx, {
      round: 1, directive: "Revalidate the helper.", required_core_targets: ["lem:helper"],
    });
    const deps = {
      runCodex: async () => { throw new Error("sole directive unit failed"); },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    } as StageDeps;
    const outcome = await runVcsSolveRound({ ctx, state, deps, round: 1 });
    expect(outcome.kind).toBe("incomplete");
    expect(outcome.message).toMatch(/sole directive unit failed/);
    expect(await listPrs(VcsStore.at(ctx), "open")).toEqual([]);
  });

  it("initializes the store from the proto, dispatches one unit per open component, and merges an additive round", async () => {
    const deps = scriptedSolver((targets) => ({ proofs: targets.map((id) => ({ id, proof_tex: `Proof of ${id}.` })) }));
    const outcome = await runVcsSolveRound({ ctx, state, deps, round: 1 });
    expect(outcome.kind).toBe("clean");
    expect(deps.calls).toEqual([["lem:helper", "thm:main"]]); // one weakly connected component
    expect(existsSync(coreJsonPath(ctx))).toBe(true);
    const core = await readCore();
    expect(core.statements.map((s) => [s.id, s.status])).toEqual([["lem:cited", "cited"], ["lem:helper", "proved"], ["thm:main", "proved"]]);
    const store = VcsStore.at(ctx);
    expect((await store.history((await store.readRef("main"))!)).map((c) => c.kind)).toEqual(["merge", "initial"]);
    expect((await listPrs(store, "merged")).length).toBe(1);
  });

  it("halts with the PR open when the solver narrows a claim, and a later round refuses to dispatch over it", async () => {
    const deps = scriptedSolver((targets) => ({
      proofs: targets.filter((id) => id === "lem:helper").map((id) => ({ id, proof_tex: "By ass:overlap." })),
      proposed_statement_changes: [{ id: "thm:main", proposed: "The estimand is identified over def:class at rate $n^{-1/4}$.", reason: "root-n fails", direction: "narrow" }],
    }));
    const first = await runVcsSolveRound({ ctx, state, deps, round: 1 });
    expect(first.kind).toBe("pr-open");
    expect(first.pr?.approval.map((a) => a.id)).toEqual(["thm:main"]);
    const second = await runVcsSolveRound({ ctx, state, deps, round: 2 });
    expect(second.kind).toBe("blocked");
    expect(deps.calls.length).toBe(1);
    const store = VcsStore.at(ctx);
    const pr = await readPr(store, first.pr!.id);
    const merged = await mergePr({ store, ctx, pr, verdict: { accept: "all", note: "honest narrowing", by: "adjudicator" } });
    expect(merged.ok).toBe(true);
    const core = await readCore();
    expect(core.statements.find((s) => s.id === "thm:main")?.statement).toMatch(/n\^\{-1\/4\}/);
    expect(core.statements.find((s) => s.id === "lem:helper")?.status).toBe("proved");
    // The narrowed claim is still open (no proof was given for it); the next round dispatches only it.
    const third = await runVcsSolveRound({ ctx, state, deps: scriptedSolver((t) => ({ proofs: t.map((id) => ({ id, proof_tex: "done" })) })), round: 3 });
    expect(third.kind).toBe("clean");
  });

  it("an open obligation halts the loop and is shown back as prior progress on the next dispatch", async () => {
    const deps = scriptedSolver((targets) => ({
      proofs: targets.filter((id) => id === "lem:helper").map((id) => ({ id, proof_tex: "By ass:overlap." })),
      open_obligations: [{ node_id: "thm:main", what_is_open: "the rate step", obstruction: "needs a maximal inequality", attempted: "chaining", partial_result: "rate $n^{-1/4}$ proved" }],
    }));
    const first = await runVcsSolveRound({ ctx, state, deps, round: 1 });
    expect(first.kind).toBe("open-gap");
    expect(first.obligations).toEqual([{ id: "thm:main", what_is_open: "the rate step" }]);
    const core = await readCore();
    expect(core.statements.find((s) => s.id === "thm:main")?.obligation?.partial_result).toMatch(/n\^\{-1\/4\}/);
    let seen = "";
    const next = scriptedSolver((targets, prompt) => { seen = prompt; return { proofs: targets.map((id) => ({ id, proof_tex: "extends the partial" })) }; });
    const second = await runVcsSolveRound({ ctx, state, deps: next, round: 2 });
    expect(second.kind).toBe("clean");
    expect(next.calls).toEqual([["thm:main"]]);
    expect(seen).toMatch(/PRIOR PARTIAL PROGRESS/);
    expect(seen).toMatch(/needs a maximal inequality/);
    expect((await readCore()).statements.find((s) => s.id === "thm:main")?.obligation).toBeUndefined();
  });

  it("a targeted directive reopens a proved statement for one round, is consumed, and is rendered to the solver", async () => {
    await runVcsSolveRound({ ctx, state, deps: scriptedSolver((t) => ({ proofs: t.map((id) => ({ id, proof_tex: "first proof" })) })), round: 1 });
    await appendEscalationLog(ctx, { round: 1, directive: "Tighten the proof constant in lem:helper.", required_core_targets: ["lem:helper"] });
    let seen = "";
    const deps = scriptedSolver((targets, prompt) => { seen = prompt; return { proofs: targets.map((id) => ({ id, proof_tex: "tightened proof" })) }; });
    const outcome = await runVcsSolveRound({ ctx, state, deps, round: 2 });
    expect(outcome.kind).toBe("clean");
    expect(deps.calls).toEqual([["lem:helper"]]);
    expect(seen).toMatch(/ACTIVE DIRECTIVE \[REQUIRED TARGETS: lem:helper\]/);
    expect(seen).toMatch(/PRIOR PROOF OF A DIRECTED TARGET/);
    expect(state.flags.d0_directives_consumed).toBe(1);
    const { graph } = await headGraph(VcsStore.at(ctx));
    expect(deriveStatus(graph, "lem:helper")).toBe("proved");
    expect((await readCore()).statements.find((s) => s.id === "lem:helper")?.proof_tex).toBe("tightened proof");
    // Nothing pending now: a further round dispatches nothing.
    const quiet = await runVcsSolveRound({ ctx, state, deps, round: 3 });
    expect(quiet.kind).toBe("clean");
    expect(deps.calls.length).toBe(1);
  });

  it("recognizes a directed definition as an existing graph target", async () => {
    await appendEscalationLog(ctx, {
      round: 1, directive: "Correct the class definition.", required_core_targets: ["def:class"],
    });
    const deps = scriptedSolver(() => ({
      proposed_definition_changes: [{
        id: "def:class", current: "$\\{P : \\text{ass:overlap holds}\\}$",
        proposed: "$\\{P : \\text{ass:overlap holds uniformly}\\}$",
        reason: "make the intended uniformity explicit", direction: "correct",
      }],
    }));
    const outcome = await runVcsSolveRound({ ctx, state, deps, round: 1 });
    expect(outcome.kind).toBe("pr-open");
    expect(outcome.message).not.toMatch(/not in the graph/);
    expect(outcome.unaddressedTargets).toEqual([]);
    expect(outcome.pr?.approval.map((a) => a.id)).toContain("def:class");
  });

  it("recognizes metadata aliases and requires their exact typed output channel", async () => {
    await appendEscalationLog(ctx, {
      round: 1, directive: "Correct the paper scope.", required_core_targets: ["metadata:honest-scope"],
    });
    const wrong = scriptedSolver(() => ({ prose_updates: { tldr: "unrelated prose" } }));
    const outcome = await runVcsSolveRound({ ctx, state, deps: wrong, round: 1 });
    expect(outcome.kind).toBe("pr-open");
    expect(outcome.message).not.toMatch(/not in the graph/);
    expect(outcome.unaddressedTargets).toEqual(["metadata:honest-scope"]);
  });

  it("does not consume a no-op typed metadata edit", async () => {
    const base = proto();
    base.honest_scope = "already current";
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(base), "utf8");
    await appendEscalationLog(ctx, {
      round: 1, directive: "Correct the paper scope.", required_core_targets: ["metadata:honest-scope"],
    });
    const deps = scriptedSolver(() => ({ prose_updates: { honest_scope: "already current" } }));
    const outcome = await runVcsSolveRound({ ctx, state, deps, round: 1 });
    expect(outcome.unaddressedTargets).toEqual(["metadata:honest-scope"]);
  });

  it("recognizes landed statement prose as an exact target receipt", async () => {
    await appendEscalationLog(ctx, {
      round: 1, directive: "Correct the helper explanation.", required_core_targets: ["lem:helper"],
    });
    const deps = scriptedSolver(() => ({
      prose_updates: {
        statement_notes: [{ id: "lem:helper", gap: "The repaired statement-specific gap." }],
      },
    }));
    const outcome = await runVcsSolveRound({ ctx, state, deps, round: 1 });
    expect(outcome.unaddressedTargets).toEqual([]);
  });

  it("consumes a directive with an unknown target so it cannot block every later resume", async () => {
    await appendEscalationLog(ctx, {
      round: 1, directive: "Repair the named node.", required_core_targets: ["def:missing"],
    });
    const deps = scriptedSolver(() => ({}));
    const outcome = await runVcsSolveRound({ ctx, state, deps, round: 1 });
    expect(outcome.kind).toBe("blocked");
    expect(outcome.message).toMatch(/def:missing/);
    expect(deps.calls).toEqual([]);
    expect(state.flags.d0_directives_consumed).toBe(1);
  });

  it("reuses a persisted validated output when the prompt is unchanged (no model call on resume)", async () => {
    const deps = scriptedSolver((targets) => ({ proofs: targets.filter((id) => id === "lem:helper").map((id) => ({ id, proof_tex: "x" })) }));
    const first = await runVcsSolveRound({ ctx, state, deps, round: 1 });
    expect(first.kind).toBe("incomplete"); // thm:main still open
    // Simulate a crash after the model wrote its output but before the merge: the
    // receipt is deleted by a successful merge, so restore the pre-merge situation.
    const store = VcsStore.at(ctx);
    const { head } = await headGraph(store);
    const receiptsDir = path.join(path.dirname(coreJsonPath(ctx)), "solve_receipts");
    expect(existsSync(receiptsDir)).toBe(false);
    void head;
    // A second round with the same open target and an unchanged prompt calls the model again
    // only because main moved (the prompt embeds the core); the reuse lane is exercised by
    // repeating a round on an unchanged main.
    const deps2 = scriptedSolver(() => ({ open_obligations: [{ node_id: "thm:main", what_is_open: "x", obstruction: "y", attempted: "z" }] }));
    const second = await runVcsSolveRound({ ctx, state, deps: deps2, round: 2 });
    expect(second.kind).toBe("open-gap");
    expect(deps2.calls.length).toBe(1);
  });
});

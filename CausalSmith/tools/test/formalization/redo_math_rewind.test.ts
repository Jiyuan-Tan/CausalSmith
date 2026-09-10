import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, beforeEach, describe, expect, it } from "vitest";
import type { PipelineContext, StateJson } from "../../src/types.js";
import type { StageDeps } from "../../src/pipeline_support.js";
import { canonicalLeanSubdir, promptPath } from "../../src/paths.js";
import { CoreSchema, type Core } from "../../src/discovery/core/schema.js";
import { coreJsonPath } from "../../src/discovery/stages/d0_core.js";
import { readEscalationLog } from "../../src/discovery/escalation_log.js";
import { adjudicateRedoMathRewind } from "../../src/formalization/dispatcher.js";
import { ensureStore } from "../../src/discovery/vcs/round.js";
import { runVcsSolveRound } from "../../src/discovery/vcs/round.js";
import { headGraph } from "../../src/discovery/vcs/commit.js";
import { deriveStatus } from "../../src/discovery/vcs/validity.js";

// An F3 refutation (a concrete witness against an intermediate Lean step) routes back
// to D0 as a TARGETED directive: only the core statements whose proofs rest on the
// refuted step are re-derived; every other established proof survives on main.

const CORE = {
  qid: "stat_redo_rewind",
  specialization: "v1",
  cluster: "stat",
  symbols: [{ name: "d", type: "scalar", space: "\\(\\mathbb N\\)", def: "feature dimension", role: "index" }],
  assumptions: [{ id: "ass:overlap", kind: "support", condition: "the propensity is bounded away from 0 and 1", free_symbols: [], standard: { name: "overlap", cite: "Rosenbaum1983" } }],
  definitions: [{ id: "def:minimax-risk", name: "R", construction: "the minimax risk over the model class", inputs: [] }],
  statements: [
    { id: "thm:localized-upper", kind: "theorem", statement: "the localized estimator attains the risk bound", depends_on: ["ass:overlap"], status: "proved", proof_tex: "Localize and apply the bounded-projection concentration lemma.", justification: "upper half", gap: "vs prior", consumer: "applied" },
    { id: "thm:erm-plugin-upper", kind: "theorem", statement: "the ERM plug-in attains the same rate", depends_on: ["ass:overlap"], status: "proved", proof_tex: "Convert the Gibbs regret identity into the plug-in bound.", justification: "plug-in half", gap: "vs prior", consumer: "applied" },
  ],
  target_estimand: "R",
  bibliography: [{ key: "Rosenbaum1983" }],
} as unknown as Core;

const RM = {
  obj_id: "aux_dimensionWitnessC",
  witness: { type: "counterexample", detail: "d=1 with a degenerate logging design refutes the coercivity step" },
  dependents: ["aux_cleanQ", "thm:erm-plugin-upper"],
  touchesProven: false,
};

function makeState(overrides: Partial<StateJson> = {}): StateJson {
  return {
    stage_completed: "2",
    lean_subdir: canonicalLeanSubdir(CORE.qid),
    pending_sorries: [],
    design_decisions: {},
    added_assumptions: [],
    proposed_from: { topic: "t", novelty_target: "field", cluster: "stat" },
    flags: {},
    ...overrides,
  } as unknown as StateJson;
}

describe("adjudicateRedoMathRewind — targeted incremental rewind", () => {
  let repoRoot: string;
  let ctx: PipelineContext;
  beforeEach(async () => {
    repoRoot = await mkdtemp(path.join(os.tmpdir(), "redo-rewind-"));
    ctx = { repoRoot, qid: CORE.qid, specialization: "v1", dryRun: false, resume: false };
    for (const name of ["stage0_common_discovery.txt", "stage0_setup_stat.txt", "stage0_solve.txt"]) {
      const target = promptPath(repoRoot, name);
      await mkdir(path.dirname(target), { recursive: true });
      await writeFile(target, `stub ${name}`, "utf8");
    }
    await mkdir(path.dirname(coreJsonPath(ctx)), { recursive: true });
    await writeFile(coreJsonPath(ctx), JSON.stringify(CORE), "utf8");
    await ensureStore(ctx, makeState());
  });
  afterEach(async () => { await rm(repoRoot, { recursive: true, force: true }); });

  it("appends a TARGETED escalation directive naming only CORE statement ids (never Lean aux ids)", async () => {
    const state = makeState();
    const result = await adjudicateRedoMathRewind({ ctx, state, rm: RM, reason: "claim-false" });
    expect(result.status).toBe("rewound");
    expect(state.stage_completed).toBe("-0.5");
    expect(state.flags.redo_math_witness).toMatchObject({ obj_id: RM.obj_id, type: "counterexample" });
    const log = await readEscalationLog(ctx);
    expect(log).toHaveLength(1);
    expect(log[0].required_core_targets).toEqual(["thm:erm-plugin-upper"]);
    expect((log[0].directive ?? "").trim().length).toBeGreaterThan(0);
    expect(log[0].provenance_only).not.toBe(true);
    // Established proofs are untouched on main: the directive reopens for one round only.
    const { graph } = await headGraph((await ensureStore(ctx, state)));
    expect(deriveStatus(graph, "thm:localized-upper")).toBe("proved");
    expect(deriveStatus(graph, "thm:erm-plugin-upper")).toBe("proved");
  });

  it("checkpoints (does NOT auto-rewind untargeted) when no core statement is among the dependents", async () => {
    const state = makeState();
    const result = await adjudicateRedoMathRewind({ ctx, state, rm: { ...RM, dependents: ["aux_cleanQ"], obj_id: "aux_x" }, reason: "claim-false" });
    expect(result.status).toBe("checkpoint");
    expect(state.stage_completed).toBe("2");
    expect(await readEscalationLog(ctx)).toHaveLength(0);
  });

  it("still checkpoints on touchesProven and past the per-node cap", async () => {
    const state = makeState();
    const result = await adjudicateRedoMathRewind({ ctx, state, rm: { ...RM, touchesProven: true }, reason: "claim-false" });
    expect(result.status).toBe("checkpoint");
    expect(await readEscalationLog(ctx)).toHaveLength(0);
  });

  it("end-to-end: the rewound D0 round re-derives ONLY the targeted theorem, keeps the other proof, and consumes the witness", async () => {
    const state = makeState();
    await adjudicateRedoMathRewind({ ctx, state, rm: RM, reason: "claim-false" });
    const calls: string[][] = [];
    let seen = "";
    const deps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        seen = prompt;
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const segment = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = (JSON.parse(segment.slice(segment.indexOf("["), segment.lastIndexOf("]") + 1)) as Array<{ id: string }>).map((t) => t.id);
        calls.push(targets);
        await writeFile(outPath, JSON.stringify({ proofs: targets.map((id) => ({ id, proof_tex: "Re-derived under the witness constraint." })) }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    } as unknown as StageDeps;
    const outcome = await runVcsSolveRound({ ctx, state, deps, round: 1 });
    expect(outcome.kind).toBe("clean");
    expect(calls).toEqual([["thm:erm-plugin-upper"]]);
    expect(seen).toMatch(/F3 REFUTATION/);
    expect(seen).toMatch(/degenerate logging design/);
    expect(state.flags.redo_math_witness).toBeUndefined();
    const core = CoreSchema.parse(JSON.parse(await readFile(coreJsonPath(ctx), "utf8")));
    expect(core.statements.find((s) => s.id === "thm:localized-upper")?.proof_tex).toBe("Localize and apply the bounded-projection concentration lemma.");
    expect(core.statements.find((s) => s.id === "thm:erm-plugin-upper")?.proof_tex).toBe("Re-derived under the witness constraint.");
    expect(core.statements.every((s) => s.status === "proved")).toBe(true);
  });
});

import { mkdtemp, mkdir, readFile, writeFile, rm } from "node:fs/promises";
import { existsSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { afterAll, beforeAll, describe, expect, it, vi } from "vitest";
import {
  runStageNeg1_2ProtoCore,
  protoCoreJsonPath,
} from "../../src/discovery/stages/neg1_2_author.js";
import { CoreSchema } from "../../src/discovery/core/schema.js";
import { modeUsesGapsContext, runStageNeg1_2Dual } from "../../src/discovery/stages/neg1_2.js";
import { formatNeg1EscalationContext } from "../../src/discovery/stageNeg1_directive.js";
import { MODEL_PLAN } from "../../src/constants.js";
import { artifactPaths, type StageDeps } from "../../src/pipeline_support.js";
import { promptPath } from "../../src/paths.js";
import type { CodexRunInput } from "../../src/shared/codex.js";
import type { PipelineContext, StateJson } from "../../src/types.js";

const QID = "stat_ate_overlap_decay";
const SPEC = "v1";

let repoRoot: string;
let goldenCore: string;

async function stubPrompts(root: string): Promise<void> {
  const stub = async (name: string, body: string) => {
    const target = promptPath(root, name);
    await mkdir(path.dirname(target), { recursive: true });
    await writeFile(target, body, "utf8");
  };
  await stub("stage_neg1_2_proto_core.txt", "stub proposal author (formal + prose contract)");
  // The author now composes a mode head + the body; stub every mode head.
  for (const m of ["cold_start", "revise", "pivot", "kernel_replace", "draft_rebuild"]) {
    await stub(`stage_neg1_2_proto_head_${m}.txt`, `stub ${m} head`);
  }
}

function makeCtx(root: string): PipelineContext {
  return { repoRoot: root, qid: QID, specialization: SPEC, dryRun: false, resume: false };
}

function makeState(): StateJson {
  return {
    stage_completed: "-1.2",
    lean_subdir: `CausalSmith/Stat/${QID}`,
    pending_sorries: [],
    design_decisions: {},
    added_assumptions: [],
    loop: "research",
    next_action: null,
    lineage: null,
    from_question_oq_id: null,
    method_id: null,
    closed_oq: null,
    flags: { local_fix_from_4d: false, missing_architecture: false },
    proposed_from: {
      topic: "test",
      novelty_target: "field",
      pivot_budget_used: 0,
      final_verdict: "accept",
      proposal_path: "",
      novelty_justification: "",
      chosen_qid: QID,
      chosen_specialization: SPEC,
      cluster: "stat",
    },
  } as unknown as StateJson;
}

function checklistRow(bibkey: string, relevant_to: string) {
  return {
    author: "Test Author",
    year: 2026,
    venue: "Test Journal",
    bibkey,
    one_line: "Comparator result used by this test.",
    relevant_to,
  };
}

function checklistRows(bibkey: string, relevant_to: string) {
  return Array.from({ length: 4 }, () => checklistRow(bibkey, relevant_to));
}

/** runCodex stub: writes `coreBody` to the core path, returns `extra` handoff keys. */
function authorDeps(
  coreBody: string | ((attempt: number) => string),
  extra: Record<string, unknown> = {},
  onInput?: (input: CodexRunInput) => void,
): StageDeps {
  let attempt = 0;
  return {
    runCodex: async (input: CodexRunInput) => {
      attempt++;
      onInput?.(input);
      const { prompt } = input;
      const m = prompt.match(/proposal core JSON to this path \(create it\): (.+)/);
      if (!m) throw new Error("authorDeps: no core path in prompt");
      const target = m[1].trim();
      await mkdir(path.dirname(target), { recursive: true });
      await writeFile(target, typeof coreBody === "function" ? coreBody(attempt) : coreBody, "utf8");
      return {
        stdout: JSON.stringify({ status: "completed", message: "core", artifacts: [target], ...extra }),
        stderr: "",
      };
    },
    runClaude: async () => {
      throw new Error("runClaude not expected");
    },
    lean: undefined as never,
  };
}

/** needs-pivot author: writes a diagnostic core but returns only the minimal status receipt. */
function needsPivotDeps(coreBody: string): StageDeps {
  return {
    runCodex: async ({ prompt }: { prompt: string }) => {
      const m = prompt.match(/proposal core JSON to this path \(create it\): (.+)/);
      if (!m) throw new Error("needsPivotDeps: no core path in prompt");
      const target = m[1].trim();
      await mkdir(path.dirname(target), { recursive: true });
      await writeFile(target, coreBody, "utf8");
      return {
        stdout: JSON.stringify({ status: "needs-pivot", message: "initial kernel is invalid" }),
        stderr: "",
      };
    },
    runClaude: async () => {
      throw new Error("runClaude not expected");
    },
    lean: undefined as never,
  };
}

async function installUpgradeParent(overrides: Record<string, unknown> = {}): Promise<Record<string, unknown>> {
  const parentDir = path.join(repoRoot, "doc", "research", "_bank", "accepted", "stat_parent_v1");
  await mkdir(path.join(parentDir, "discovery"), { recursive: true });
  await writeFile(path.join(parentDir, "README.md"), "---\nbanked_novelty_tier: field\n---\n", "utf8");
  const parentCore = JSON.parse(goldenCore) as Record<string, unknown>;
  Object.assign(parentCore, { qid: "stat_parent", specialization: "v1", cluster: "stat" }, overrides);
  parentCore.bibliography = (parentCore.bibliography as Array<Record<string, unknown>>).slice(0, 3);
  await writeFile(path.join(parentDir, "discovery", "proto_core.json"), JSON.stringify(parentCore), "utf8");
  return parentCore;
}

beforeAll(async () => {
  repoRoot = await mkdtemp(path.join(os.tmpdir(), "neg12single-"));
  await stubPrompts(repoRoot);
  goldenCore = await readFile(
    new URL("../fixtures/stat_ate_overlap_decay_proto_core.json", import.meta.url),
    "utf8",
  );
  const completeGolden = JSON.parse(goldenCore) as Record<string, unknown>;
  completeGolden.literature_checklist = checklistRows("Tsybakov2009", "thm:upper");
  completeGolden.seeds = ["fixture seed"];
  completeGolden.seed_details = [{ id: "fixture seed", opportunity: "fixture opportunity" }];
  completeGolden.literature_map = "Fixture literature map.";
  completeGolden.novelty_justification = "Fixture novelty justification.";
  goldenCore = JSON.stringify(completeGolden);
});

afterAll(async () => {
  await rm(repoRoot, { recursive: true, force: true });
});

describe("Stage -1.2 author (single artifact: formal + prose → gate → schema-validate)", () => {
  it("dispatches the Codex proposal author with the stage-specific Sol tier", async () => {
    const inputs: CodexRunInput[] = [];
    await runStageNeg1_2ProtoCore({
      ctx: makeCtx(repoRoot),
      state: makeState(),
      mode: "cold-start",
      deps: authorDeps(goldenCore, {}, (input) => inputs.push(input)),
    });

    expect(inputs).toHaveLength(1);
    expect(inputs[0].model).toBe("gpt-5.6-sol");
    expect(inputs[0].model).toBe(MODEL_PLAN.stageNeg1_2_draft.codex.model);
    expect(inputs[0].reasoningEffort).toBe(MODEL_PLAN.stageNeg1_2_draft.codex.effort);
  });

  it("selects the matching mode head and limits gaps to ideation modes", async () => {
    const modes = ["cold-start", "revise", "pivot", "kernel-replace", "draft-rebuild"] as const;
    const expectedGaps = new Set(["cold-start", "pivot"]);
    for (const mode of modes) {
      const prompts: string[] = [];
      await runStageNeg1_2ProtoCore({
        ctx: makeCtx(repoRoot),
        state: makeState(),
        mode,
        deps: authorDeps(goldenCore, {}, (input) => prompts.push(input.prompt)),
      });
      expect(prompts[0]).toMatch(new RegExp(`^stub ${mode.replace(/-/g, "_")} head`));
      expect(modeUsesGapsContext(mode)).toBe(expectedGaps.has(mode));
    }
  });

  it("keeps substantive revision obligations in scope after a structural-gate retry", async () => {
    const broken = JSON.parse(goldenCore);
    broken.statements[0].status = "proved";
    const prompts: string[] = [];
    const deps = authorDeps(
      (attempt) => attempt === 1 ? JSON.stringify(broken) : goldenCore,
      {},
      (input) => prompts.push(input.prompt),
    );

    await runStageNeg1_2ProtoCore({
      ctx: makeCtx(repoRoot),
      state: makeState(),
      mode: "revise",
      deps,
    });

    expect(prompts).toHaveLength(2);
    expect(prompts[1]).toContain("does not discharge or narrow those substantive obligations");
  });

  it("injects every current-angle directive and excludes abandoned angles", () => {
    const formatted = formatNeg1EscalationContext([
      { angle: 0, version: 0, directive: "stale directive with reused version" },
      { angle: 0, version: 9, directive: "old angle directive" },
      { angle: 1, version: 0, directive: "current directive A" },
      { angle: 1, version: 2, directive: "current directive B" },
    ], 1);

    expect(formatted).not.toContain("stale directive");
    expect(formatted).not.toContain("old angle directive");
    expect(formatted).toContain("current directive A");
    expect(formatted).toContain("current directive B");
  });

  it("backfills legacy angle segments across version resets and switch rows", () => {
    const formatted = formatNeg1EscalationContext([
      { version: 4, directive: "legacy angle zero" },
      { version: 0, directive: "legacy angle one root" },
      { version: 4, directive: "legacy angle one final" },
      { version: 0, directive: "legacy angle two root" },
      { version: 6, directive: "legacy angle three root", note: "angle-action:switch" },
      { version: 1, directive: "legacy angle three continuation", note: "angle-action:continue" },
      { angle: 3, version: 5, directive: "new provenance row" },
    ], 3);

    expect(formatted).not.toContain("angle zero");
    expect(formatted).not.toContain("angle one");
    expect(formatted).not.toContain("angle two");
    expect(formatted).toContain("legacy angle three root");
    expect(formatted).toContain("legacy angle three continuation");
    expect(formatted).toContain("new provenance row");
  });

  it("fails closed when equal-version legacy rows cannot identify a later angle", () => {
    expect(() => formatNeg1EscalationContext([
      { version: 0, directive: "could be angle zero" },
      { version: 0, directive: "could be angle zero or one" },
    ], 1)).toThrow(/cannot be safely mapped/);

    expect(formatNeg1EscalationContext([
      { version: 0, directive: "legacy angle zero" },
      {
        angle: 1,
        version: 0,
        directive: "",
        note: "angle-action:switch",
        provenance_only: true,
      },
    ], 1)).toBe("");

    expect(formatNeg1EscalationContext([
      { version: 10, directive: "legacy angle zero" },
      {
        angle: 1,
        version: 10,
        directive: "carry this repaired kernel into angle one",
        note: "user supplied note",
      },
      {
        angle: 1,
        version: 10,
        directive: "",
        note: "angle-action:switch",
        provenance_only: true,
      },
    ], 1)).toContain("carry this repaired kernel into angle one");
  });

  it("makes standalone orchestrator directives outrank an ACCEPT with no reviewer flags", async () => {
    const prompt = await readFile(
      new URL("../../src/discovery/prompts/D-1/stage_neg1_2_proto_head_revise.txt", import.meta.url),
      "utf8",
    );
    expect(prompt).toContain("overrides this mode's reviewer-flags-only / kernel-preserved scope");
    expect(prompt).toContain("prior verdict is `ACCEPT` with empty S / N / C flags");
    expect(prompt).toContain("Empty reviewer flags never authorize a no-op");
  });

  it("writes the core, passes the gate, and renders NO proposal .tex", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    const res = await runStageNeg1_2ProtoCore({ ctx, state, mode: "cold-start", deps: authorDeps(goldenCore) });
    expect(existsSync(res.protoCoreJsonPath)).toBe(true);
    // The proto_core JSON is the sole discovery artifact; no proposal .tex is rendered.
    expect(existsSync(artifactPaths(ctx, state).proposalTex)).toBe(false);
  });

  it("preserves the SC6 comparator promise table across schema canonicalization", async () => {
    const ctx = makeCtx(repoRoot);
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    core.comparator_promise_table = [{
      comparator_bibkey: "Tsybakov2009",
      comparator_claim: "A published minimax comparator claim.",
      matched_by: "Theorem 1",
      match_kind: "strict_tightening",
    }];

    const res = await runStageNeg1_2ProtoCore({
      ctx,
      state: makeState(),
      mode: "revise",
      deps: authorDeps(JSON.stringify(core)),
    });
    const persisted = JSON.parse(await readFile(res.protoCoreJsonPath, "utf8"));
    expect(persisted.comparator_promise_table).toEqual(core.comparator_promise_table);
  });

  it("warns with the key names when the persist boundary drops non-schema keys", async () => {
    const ctx = makeCtx(repoRoot);
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    core.__unknown_mandated_field = "the author complied but nothing persists this key";
    const warnSpy = vi.spyOn(console, "warn").mockImplementation(() => {});
    try {
      await runStageNeg1_2ProtoCore({
        ctx,
        state: makeState(),
        mode: "revise",
        deps: authorDeps(JSON.stringify(core)),
      });
      const calls = warnSpy.mock.calls.map((c) => c.join(" "));
      expect(
        calls.some((c) => c.includes("__unknown_mandated_field") && c.includes("dropped")),
        `expected a console.warn naming the dropped key; got: ${JSON.stringify(calls)}`,
      ).toBe(true);
    } finally {
      warnSpy.mockRestore();
    }
  });

  it("THROWS when the authored core fails the gate (GP2: a proven statement)", async () => {
    const ctx = makeCtx(repoRoot);
    const broken = JSON.parse(goldenCore);
    broken.statements[0].status = "proved";
    const canonical = protoCoreJsonPath(ctx);
    await writeFile(canonical, goldenCore, "utf8");
    await expect(
      runStageNeg1_2ProtoCore({ ctx, state: makeState(), mode: "cold-start", deps: authorDeps(JSON.stringify(broken)) }),
    ).rejects.toThrow(/proposal gate/);
    expect(await readFile(canonical, "utf8")).toBe(goldenCore);
  });

  it("THROWS when the authored core fails the gate (GP3: missing tldr)", async () => {
    const ctx = makeCtx(repoRoot);
    const broken = JSON.parse(goldenCore);
    delete broken.tldr;
    await expect(
      runStageNeg1_2ProtoCore({ ctx, state: makeState(), mode: "cold-start", deps: authorDeps(JSON.stringify(broken)) }),
    ).rejects.toThrow(/proposal gate/);
  });

  it("THROWS when the authored core omits the mandatory comparator promise table", async () => {
    const ctx = makeCtx(repoRoot);
    const broken = JSON.parse(goldenCore);
    delete broken.comparator_promise_table;
    await expect(
      runStageNeg1_2ProtoCore({ ctx, state: makeState(), mode: "revise", deps: authorDeps(JSON.stringify(broken)) }),
    ).rejects.toThrow(/proposal gate[\s\S]*comparator_promise_table/);
  });

  it("THROWS when the model reports failed", async () => {
    const ctx = makeCtx(repoRoot);
    const deps: StageDeps = {
      runCodex: async () => ({
        stdout: JSON.stringify({ status: "failed", message: "kernel not authorable" }),
        stderr: "",
      }),
      runClaude: async () => {
        throw new Error("unused");
      },
      lean: undefined as never,
    };
    await expect(runStageNeg1_2ProtoCore({ ctx, state: makeState(), mode: "cold-start", deps })).rejects.toThrow(/failed/);
  });

  it("rejects a malformed completed receipt even when the authored core is valid", async () => {
    const ctx = makeCtx(repoRoot);
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    core.literature_checklist = checklistRows("Author2026", "thm:pn");
    core.novelty_justification = "Independent review decides the mathematical claim.";
    core.message = "Complete proposal core authored.";
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const m = prompt.match(/proposal core JSON to this path \(create it\): (.+)/);
        if (!m) throw new Error("malformed-receipt deps: no core path in prompt");
        await mkdir(path.dirname(m[1].trim()), { recursive: true });
        await writeFile(m[1].trim(), JSON.stringify(core), "utf8");
        return { stdout: '{"status":"completed","message":"core",,"artifacts":[]}', stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await expect(runStageNeg1_2ProtoCore({
      ctx,
      state: makeState(),
      mode: "revise",
      deps,
    })).rejects.toThrow(/producer receipt is invalid/);
  });

  it("rejects malformed leading JSON followed by a valid completed receipt", async () => {
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const m = prompt.match(/proposal core JSON to this path \(create it\): (.+)/);
        if (!m) throw new Error("two-object deps: no core path in prompt");
        const target = m[1].trim();
        await writeFile(target, JSON.stringify(core), "utf8");
        return {
          stdout: `{"status":"needs-pivot",,}\n${JSON.stringify({ status: "completed", message: "ok", artifacts: [target] })}`,
          stderr: "",
        };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
    await expect(runStageNeg1_2ProtoCore({
      ctx: makeCtx(repoRoot), state: makeState(), mode: "revise", deps,
    })).rejects.toThrow(/producer receipt is invalid/);
  });

  it("rejects a bare completed receipt even when the authored core is valid", async () => {
    const ctx = makeCtx(repoRoot);
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    core.literature_checklist = checklistRows("Author2026", "thm:pn");
    core.novelty_justification = "Independent review decides the mathematical claim.";
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const m = prompt.match(/proposal core JSON to this path \(create it\): (.+)/);
        if (!m) throw new Error("bare-receipt deps: no core path in prompt");
        await mkdir(path.dirname(m[1].trim()), { recursive: true });
        await writeFile(m[1].trim(), JSON.stringify(core), "utf8");
        return { stdout: '{"status":"completed"}', stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
    await expect(runStageNeg1_2ProtoCore({
      ctx,
      state: makeState(),
      mode: "revise",
      deps,
    })).rejects.toThrow(/producer receipt is invalid/);
  });

  it("ignores extra receipt artifact paths and binds the canonical core", async () => {
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    const result = await runStageNeg1_2ProtoCore({
      ctx: makeCtx(repoRoot),
      state: makeState(),
      mode: "revise",
      deps: authorDeps(JSON.stringify(core), { artifacts: ["stale.json", "extra.json"] }),
    });
    expect(result.handoff.artifacts).toEqual([result.protoCoreJsonPath]);
  });

  it("feeds a malformed receipt back for a bounded re-author round instead of halting", async () => {
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    let attempt = 0;
    const prompts: string[] = [];
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        attempt++;
        prompts.push(prompt);
        const m = prompt.match(/proposal core JSON to this path \(create it\): (.+)/);
        if (!m) throw new Error("retry deps: no core path in prompt");
        await mkdir(path.dirname(m[1].trim()), { recursive: true });
        await writeFile(m[1].trim(), JSON.stringify(core), "utf8");
        return {
          stdout: attempt === 1 ? '{"status":"completed"}' : JSON.stringify({ status: "completed", message: "ok" }),
          stderr: "",
        };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
    const result = await runStageNeg1_2ProtoCore({ ctx: makeCtx(repoRoot), state: makeState(), mode: "revise", deps });
    expect(result.status).toBe("completed");
    expect(attempt).toBe(2);
    expect(prompts[1]).toMatch(/\[RECEIPT\]/);
  });

  it("binds a mistyped completed-receipt path to the validated canonical core", async () => {
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    core.novelty_justification = "Freshly authored content that must replace the stale canonical core.";
    const canonical = protoCoreJsonPath(makeCtx(repoRoot));
    const stale = JSON.parse(goldenCore) as Record<string, unknown>;
    stale.novelty_justification = "Stale canonical content.";
    await writeFile(canonical, JSON.stringify(stale), "utf8");
    const result = await runStageNeg1_2ProtoCore({
      ctx: makeCtx(repoRoot),
      state: makeState(),
      mode: "revise",
      deps: authorDeps(JSON.stringify(core), { artifacts: ["/mistyped/model/echo.json"] }),
    });

    expect(result.handoff.artifacts).toEqual([result.protoCoreJsonPath]);
    const persisted = JSON.parse(await readFile(result.protoCoreJsonPath, "utf8"));
    expect(persisted.novelty_justification).toBe(core.novelty_justification);
    expect(existsSync(`${result.protoCoreJsonPath}.next`)).toBe(false);
  });

  it("rejects an authored core from a different valid cluster", async () => {
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    core.cluster = "scm";
    await expect(runStageNeg1_2ProtoCore({
      ctx: makeCtx(repoRoot),
      state: makeState(),
      mode: "revise",
      deps: authorDeps(JSON.stringify(core)),
    })).rejects.toThrow(/cluster must equal run cluster stat/);
  });

  it.each(["seeds", "seed_details", "literature_map"])(
    "rejects a cold-start core missing required authored %s metadata",
    async (field) => {
      const core = JSON.parse(goldenCore) as Record<string, unknown>;
      delete core[field];
      await expect(runStageNeg1_2ProtoCore({
        ctx: makeCtx(repoRoot), state: makeState(), mode: "cold-start", deps: authorDeps(JSON.stringify(core)),
      })).rejects.toThrow(new RegExp(field));
    },
  );

  it.each(["seeds", "seed_details", "literature_map"])(
    "accepts a revise core without %s (ideation substrate lives in state outside cold-start)",
    async (field) => {
      const core = JSON.parse(goldenCore) as Record<string, unknown>;
      delete core[field];
      const result = await runStageNeg1_2ProtoCore({
        ctx: makeCtx(repoRoot), state: makeState(), mode: "revise", deps: authorDeps(JSON.stringify(core)),
      });
      expect(result.status).toBe("completed");
    },
  );

  it.each([
    ["qid", "stat_other", /qid must equal/],
    ["specialization", undefined, /specialization must equal/],
    ["cluster", undefined, /must declare cluster/],
  ] as const)("rejects a completed core with invalid run identity field %s", async (field, value, expected) => {
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    if (value === undefined) delete core[field];
    else core[field] = value;
    await expect(runStageNeg1_2ProtoCore({
      ctx: makeCtx(repoRoot), state: makeState(), mode: "revise", deps: authorDeps(JSON.stringify(core)),
    })).rejects.toThrow(expected);
  });

  it.each([
    ["relevant_to", "thm:deleted", /must name a current statement id/],
    ["bibkey", "MissingCitation", /must name a current bibliography key/],
  ] as const)("rejects a checklist row whose %s is dangling", async (field, value, expected) => {
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    (core.literature_checklist as Array<Record<string, unknown>>)[0][field] = value;
    await expect(runStageNeg1_2ProtoCore({
      ctx: makeCtx(repoRoot), state: makeState(), mode: "revise", deps: authorDeps(JSON.stringify(core)),
    })).rejects.toThrow(expected);
  });

  it("rejects upgrade provenance without three unique reused keys", async () => {
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    Object.assign(core, {
      upgrade_mode: true,
      parent_qid: "stat_parent",
      parent_spec: "v1",
      upgrade_axis: "estimation",
      delta_summary: "A concrete estimation delta.",
      reused_bibkeys: [],
      new_bibkeys: ["Kennedy2024"],
    });
    const ctx = {
      ...makeCtx(repoRoot),
      upgradeFrom: {
        parent_qid: "stat_parent",
        parent_spec: "v1",
        parent_tier: "accepted" as const,
        upgrade_axis: "estimation" as const,
      },
    };
    await installUpgradeParent();
    await expect(runStageNeg1_2ProtoCore({
      ctx, state: makeState(), mode: "revise", deps: authorDeps(JSON.stringify(core)),
    })).rejects.toThrow(/at least three unique parent bibliography keys/);
  });

  it("rejects duplicate bibliography keys before checklist joins", async () => {
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    const bibliography = core.bibliography as Array<Record<string, unknown>>;
    bibliography.push({ ...bibliography[0], citation: "A conflicting source." });
    await expect(runStageNeg1_2ProtoCore({
      ctx: makeCtx(repoRoot), state: makeState(), mode: "revise", deps: authorDeps(JSON.stringify(core)),
    })).rejects.toThrow(/bibliography keys must be unique/);
  });

  it("skips the parent-membership join when the banked parent identity is stale, keeping core-side checks", async () => {
    await installUpgradeParent({ qid: "stat_other" });
    const ctx = {
      ...makeCtx(repoRoot),
      upgradeFrom: {
        parent_qid: "stat_parent", parent_spec: "v1", parent_tier: "accepted" as const,
        upgrade_axis: "estimation" as const,
      },
    };
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    const upgradeMeta = {
      upgrade_mode: true, parent_qid: "stat_parent", parent_spec: "v1", upgrade_axis: "estimation",
      delta_summary: "A concrete estimation delta.",
      // Not the parent's first three keys: only tolerable because the join is skipped.
      reused_bibkeys: ["Tsybakov2009", "ChernozhukovEtAl2018", "vanderVaart1998"],
      new_bibkeys: ["Kennedy2024"],
    };
    const result = await runStageNeg1_2ProtoCore({
      ctx, state: makeState(), mode: "revise", deps: authorDeps(JSON.stringify({ ...core, ...upgradeMeta })),
    });
    expect(result.status).toBe("completed");
    // Core-side checks still bite: a reused key absent from the current bibliography.
    await expect(runStageNeg1_2ProtoCore({
      ctx, state: makeState(), mode: "revise",
      deps: authorDeps(JSON.stringify({ ...core, ...upgradeMeta, reused_bibkeys: ["Tsybakov2009", "Nope1", "Nope2"] })),
    })).rejects.toThrow(/must name a current bibliography key/);
  });

  it("fails closed on malformed stdout when no authored core exists", async () => {
    const deps: StageDeps = {
      runCodex: async () => ({ stdout: '{"status":"completed",,}', stderr: "" }),
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
    await expect(runStageNeg1_2ProtoCore({
      ctx: makeCtx(repoRoot),
      state: makeState(),
      mode: "revise",
      deps,
    })).rejects.toThrow(/producer receipt is invalid|without writing/);
  });

  it.each(["{}", '{"status":"blocked"}'])(
    "fails closed on a well-formed unknown disposition: %s",
    async (stdout) => {
      const core = JSON.parse(goldenCore) as Record<string, unknown>;
      core.literature_checklist = checklistRows("Author2026", "thm:pn");
      core.novelty_justification = "Independent review decides the mathematical claim.";
      core.message = "Complete proposal core authored.";
      const deps = authorDeps(JSON.stringify(core));
      deps.runCodex = async ({ prompt }: { prompt: string }) => {
        const m = prompt.match(/proposal core JSON to this path \(create it\): (.+)/);
        if (!m) throw new Error("unknown-status deps: no core path in prompt");
        await writeFile(m[1].trim(), JSON.stringify(core), "utf8");
        return { stdout, stderr: "" };
      };
      await expect(runStageNeg1_2ProtoCore({
        ctx: makeCtx(repoRoot), state: makeState(), mode: "revise", deps,
      })).rejects.toThrow(/producer receipt is invalid/);
    },
  );
});

describe("runStageNeg1_2Dual (rollout step 5 — one author + render + harvest)", () => {
  it("does not harvest metadata from an unvalidated needs-pivot diagnostic core", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    core.seeds = ["alternative lower-bound experiment", "certified-ratio coverage"];
    core.seed_details = [{ seed: "alternative lower-bound experiment", motif: "M7" }];
    core.literature_map = { anchor: "Dorn2025", gap: "finite-sample coverage" };
    core.novelty_justification = "unvalidated diagnostic novelty must not be harvested";
    core.literature_checklist = [{ author: "malformed diagnostic reviewer metadata" }];

    const res = await runStageNeg1_2Dual({
      ctx,
      state,
      deps: needsPivotDeps(JSON.stringify(core)),
      mode: "cold-start",
      nextVersion: 1,
      angleIndex: 0,
    });

    expect(res.status).toBe("completed");
    expect(state.proposed_from!.last_draft_status).toBe("needs-pivot");
    expect(state.proposed_from!.seed_list).toBeUndefined();
    expect(state.proposed_from!.seed_details).toBeUndefined();
    expect(state.proposed_from!.literature_map).toBeUndefined();
    expect(state.proposed_from!.novelty_justification).toBe("");
  });

  it("classifies a sandbox-startup needs-pivot as env-failure, not a dead angle", async () => {
    // The monolith called handoffSignalsEnvFailure on the needs-pivot receipt; the
    // carve lost that call, so `last_draft_status` was set to "needs-pivot"
    // unconditionally and the entire D-0.5 env-failure retry branch
    // (NEG1_ENV_FAILURE_RETRY_BUDGET, flags.neg1_env_failure_retries) was dead code —
    // a codex sandbox-spawn failure burned a healthy angle as "not authorable".
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const m = prompt.match(/proposal core JSON to this path \(create it\): (.+)/);
        if (!m) throw new Error("env-failure deps: no core path in prompt");
        const target = m[1].trim();
        await mkdir(path.dirname(target), { recursive: true });
        await writeFile(target, goldenCore, "utf8");
        return {
          stdout: JSON.stringify({
            status: "needs-pivot",
            message: "windows sandbox: spawn setup refresh (os error 740)",
          }),
          stderr: "",
        };
      },
      runClaude: async () => { throw new Error("runClaude not expected"); },
      lean: undefined as never,
    };

    const res = await runStageNeg1_2Dual({
      ctx, state, deps, mode: "cold-start", nextVersion: 1, angleIndex: 0,
    });
    expect(res.status).toBe("completed");
    expect(state.proposed_from!.last_draft_status).toBe("env-failure");
  });

  it("rejects a malformed status-only needs-pivot receipt", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    const deps: StageDeps = {
      runCodex: async () => ({ stdout: '{"status":"needs-pivot",,}', stderr: "" }),
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
    await expect(runStageNeg1_2Dual({
      ctx, state, deps, mode: "revise", nextVersion: 1, angleIndex: 0,
    })).rejects.toThrow(/producer receipt is invalid/);
  });

  it("projects a needs-pivot stdout receipt even when no diagnostic core exists", async () => {
    const state = makeState();
    const deps: StageDeps = {
      runCodex: async () => ({
        stdout: JSON.stringify({ status: "needs-pivot", message: "pivot" }),
        stderr: "",
      }),
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
    await runStageNeg1_2Dual({
      ctx: makeCtx(repoRoot), state, deps, mode: "revise", nextVersion: 1, angleIndex: 0,
    });
    expect(state.proposed_from!.novelty_justification).toBe("");
    expect(state.proposed_from!.seed_list).toBeUndefined();
  });

  it("authors the core (no .tex) and harvests core metadata into proposed_from", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    // A legacy core message is stripped: disposition text belongs to stdout.
    core.message = "stale prior disposition";
    core.seeds = ["coreSeed"];
    core.seed_details = [{ one_liner: "core overlap-decay rate" }];
    core.literature_map = "the core lit map";
    const deps = authorDeps(JSON.stringify(core));
    const res = await runStageNeg1_2Dual({
      ctx,
      state,
      deps,
      mode: "cold-start",
      nextVersion: 1,
      angleIndex: 0,
    });
    expect(res.status).toBe("completed");
    expect(existsSync(protoCoreJsonPath(ctx))).toBe(true);
    // No proposal .tex; proposal_path points at the proto_core JSON (the sole artifact).
    expect(existsSync(artifactPaths(ctx, state).proposalTex)).toBe(false);

    const pf = state.proposed_from as Record<string, unknown>;
    expect(pf.proposal_path).toBe(protoCoreJsonPath(ctx));
    expect(pf.current_version).toBe(1);
    expect(pf.last_draft_status).toBe("completed");
    expect(pf.cluster).toBe("stat");
    expect(pf.seed_list).toEqual(["coreSeed"]);
    expect(pf.seed_details).toEqual([{ one_liner: "core overlap-decay rate" }]);
    expect(pf.literature_map).toBe("the core lit map");
    expect(typeof pf.novelty_justification).toBe("string");
    expect(pf.last_draft_version).toBe(1);
    // Single-source contract: D-0.5 reads the persisted authored core.
    const persisted = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8")) as Record<
      string,
      unknown
    >;
    expect(persisted.literature_checklist).toEqual(checklistRows("Tsybakov2009", "thm:upper"));
    expect(persisted.message).toBeUndefined();
    expect(res.message).toContain("authored angle=0");
  });

  it("ignores checklist metadata on the stdout receipt (even malformed): the core is the authority", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    const result = await runStageNeg1_2Dual({
      ctx,
      state,
      deps: authorDeps(JSON.stringify(core), {
        literature_checklist: [
          ...checklistRows("ReceiptKey", "thm:pn").slice(0, 3),
          { author: "Receipt Author", year: 2026, venue: "Receipt Venue", Blur: "x" },
        ],
      }),
      mode: "cold-start",
      nextVersion: 1,
      angleIndex: 0,
    });
    const persisted = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(persisted.literature_checklist).toEqual(core.literature_checklist);
  });

  it("strips stray upgrade metadata outside an upgrade run", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    core.upgrade_mode = true;
    core.upgrade_axis = "estimation";
    const result = await runStageNeg1_2Dual({
      ctx,
      state,
      deps: authorDeps(JSON.stringify(core)),
      mode: "cold-start",
      nextVersion: 1,
      angleIndex: 0,
    });
    const persisted = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(persisted.upgrade_mode).toBeUndefined();
    expect(persisted.upgrade_axis).toBeUndefined();
  });

  it("ignores drift-spelled checklist metadata on the stdout receipt", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    const result = await runStageNeg1_2Dual({
      ctx,
      state,
      deps: authorDeps(JSON.stringify(core), {
        named_literature_checklist: checklistRows("FreshDriftSpelledKey", "thm:pn"),
      }),
      mode: "cold-start",
      nextVersion: 1,
      angleIndex: 0,
    });
    const persisted = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(persisted.literature_checklist).toEqual(core.literature_checklist);
    expect(persisted.named_literature_checklist).toBeUndefined();
  });

  it("drops stdout reviewer aliases instead of exposing them through the handoff", async () => {
    const ctx = makeCtx(repoRoot);
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    const result = await runStageNeg1_2ProtoCore({
      ctx,
      state: makeState(),
      mode: "revise",
      deps: authorDeps(JSON.stringify(core), {
        named_literature_checklist: checklistRows("ReceiptAlias", "thm:pn"),
        review_findings: "stdout-only metadata must not escape",
      }),
    });
    expect(result.handoff.named_literature_checklist).toBeUndefined();
    expect(result.handoff.review_findings).toBeUndefined();
  });

  it("harvests ideation metadata from the core when the stdout receipt is minimal", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    core.seeds = ["core seed A", "core seed B"];
    core.seed_details = [{ seed: "core seed A", motif: "M20" }];
    core.literature_map = { anchor: "Tian and Pearl", gap: "mediator-defier frontier" };
    core.novelty_justification = "core-authored novelty case";
    core.literature_checklist = checklistRows("Tsybakov2009", "thm:upper");

    const res = await runStageNeg1_2Dual({
      ctx,
      state,
      deps: authorDeps(JSON.stringify(core)),
      mode: "cold-start",
      nextVersion: 1,
      angleIndex: 0,
    });

    expect(res.status).toBe("completed");
    const pf = state.proposed_from as Record<string, unknown>;
    expect(pf.seed_list).toEqual(["core seed A", "core seed B"]);
    expect(pf.seed_details).toEqual([{ seed: "core seed A", motif: "M20" }]);
    expect(pf.literature_map).toBe(
      JSON.stringify({ anchor: "Tian and Pearl", gap: "mediator-defier frontier" }),
    );
    expect(pf.novelty_justification).toBe("core-authored novelty case");
    expect(pf.last_draft_version).toBe(1);
    const persisted = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8")) as Record<string, unknown>;
    expect(persisted.literature_checklist).toEqual(checklistRows("Tsybakov2009", "thm:upper"));
  });

  it("preserves a structured literature-map row array from the authored core", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    core.literature_map = [
      { candidate: "seed:primary", threads: ["Published theorem A"], occupation_check: "Open" },
      { candidate: "seed:inference", threads: ["Published theorem B"], occupation_check: "Open" },
    ];
    await runStageNeg1_2Dual({
      ctx, state, deps: authorDeps(JSON.stringify(core)), mode: "revise", nextVersion: 2, angleIndex: 0,
    });
    expect(state.proposed_from!.literature_map).toBe(JSON.stringify(core.literature_map));
    const persisted = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(persisted.literature_map).toEqual(core.literature_map);
  });

  it("canonicalizes a structured core-authored novelty justification", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    core.novelty_justification = {
      strict_delta: "A new sharp compatible-full-law interval.",
      closest_results: "Existing sequential and cross-sectional sensitivity results.",
    };

    const res = await runStageNeg1_2Dual({
      ctx,
      state,
      deps: authorDeps(JSON.stringify(core)),
      mode: "cold-start",
      nextVersion: 1,
      angleIndex: 0,
    });

    expect(res.status).toBe("completed");
    const expected =
      '{"closest_results":"Existing sequential and cross-sectional sensitivity results.","strict_delta":"A new sharp compatible-full-law interval."}';
    expect(state.proposed_from!.novelty_justification).toBe(expected);
    const persisted = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8")) as Record<string, unknown>;
    expect(persisted.novelty_justification).toBe(expected);
  });

  it.each([
    {},
    { strict_delta: "" },
    { closest_results: null },
    { sections: [{ text: "   " }, null] },
  ])("rejects a structured novelty justification without substantive text: %j", async (value) => {
    const ctx = makeCtx(repoRoot);
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    core.novelty_justification = value;

    await expect(runStageNeg1_2Dual({
      ctx,
      state: makeState(),
      deps: authorDeps(JSON.stringify(core)),
      mode: "cold-start",
      nextVersion: 1,
      angleIndex: 0,
    })).rejects.toThrow(/novelty_justification[\s\S]*substantive text/);
  });

  it("rehydrates missing seed state from a revised core after an interrupted run", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    state.proposed_from!.seed_list = [];
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    core.seeds = ["surviving pivot seed"];
    core.literature_map = "persisted literature map";

    await runStageNeg1_2Dual({
      ctx,
      state,
      deps: authorDeps(JSON.stringify(core)),
      mode: "revise",
      nextVersion: 6,
      angleIndex: 0,
    });

    expect(state.proposed_from!.seed_list).toEqual(["surviving pivot seed"]);
    expect(state.proposed_from!.literature_map).toBe("persisted literature map");
  });
});

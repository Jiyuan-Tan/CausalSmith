import { mkdir, mkdtemp, readFile, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { canonicalLeanSubdir, qidToCamel, statePath } from "../src/paths.js";
import { createInitialState, findActiveStates, loadState, saveState, stateSchema } from "../src/state.js";

describe("state schema", () => {
  it("defaults the flags a minimal state omits", () => {
    const parsed = stateSchema.parse({
      stage_completed: "0.5",
      lean_subdir: "CausalSmith/Panel/Q1_GenericMinimality",
      design_decisions: {},
      added_assumptions: [],
      flags: {},
    });

    expect(parsed.flags.missing_architecture).toBe(false);
  });

  it("loads and re-saves a state written by an older pipeline without dropping its undeclared keys", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-legacy-keys-"));
    const qid = "panel_minimal_basis";
    const spec = "p1_bernoulli";
    const legacyFlags = {
      rewound_from_stage0: "old rewind reason",
      rewound_from_stage0_5_pivot: "old pivot",
      rewound_from_stage4d: "round-2",
      local_fix_from_4d: true,
      theorem_splits: 2,
      theorem_splits_cap_hit: "cap",
      stage1_rewinds: 3,
      stage1_rewinds_cap_hit: "cap",
      stage0_budget_exhausted: "spent",
      scaffold_redirect_cap_hit: "cap",
      general_review_halt: "below floor",
      statement_correction_directive: "restated",
      stage0_rewind_intent_required: "untyped",
      escalate_to_proposer: "redraft",
      d0_cross_boundary_rewind: { intent: "extension", status: "pending" },
      scaffold_redirect_count: 4,
      source_rewind: { status: "applied", dirty_nodes: ["thm:main"], target: "D0 main abc" },
      substrate_build_required: "gate X",
      substrate_built: [{ gate_id: "lem:g", decl_name: "Causalean.G", module: "Causalean.M", nl_statement: "g" }],
      stage0_too_many_conjectures: "five",
      f4_localpatch_rounds: 1,
      assumption_review_count: 2,
      assumption_review_cap_hit: "cap",
      bucket_a_blocked: false,
      d0r_human_directive: "flip the framing",
      d0r_flagship_rounds: 1,
      d0r_best_tier: "field",
      d0r_best_note_path: "discovery/d0r_best.tex",
    };
    const legacyProposal = {
      topic: "legacy topic",
      novelty_target: "field",
      pivot_budget_used: 2,
      final_verdict: "ACCEPT",
      proposal_path: "discovery/proto_core.json",
      novelty_justification: "n",
      chosen_qid: qid,
      chosen_specialization: spec,
      accepted_scope_caveats: [{ label: "ass:a", caveat: "assumed", bound_claim: "sharp under A" }],
    };
    const legacyTop = {
      pending_sorries: [{ file: "Basic.lean", line: 12, track: "2", bursted: true }],
      loop: "research",
      next_action: "pending_checkpoint",
      lineage: { parent_run_id: "r0", parent_kind: "study" },
      from_question_oq_id: "oq-1",
      method_id: "did",
      closed_oq: { oq_id: "oq-1", bt_id: "bt-1" },
      ckpt_pending: false,
    };
    const onDisk = {
      ...createInitialState(qid),
      ...legacyTop,
      proposed_from: legacyProposal,
      stage_completed: "0",
      added_assumptions: [{ label: "A1", statement: "s", user_approved: true, reviewed: false }],
    } as unknown as Record<string, unknown>;
    onDisk.flags = { ...(onDisk.flags as Record<string, unknown>), ...legacyFlags };
    const file = statePath(repoRoot, qid, spec);
    await mkdir(path.dirname(file), { recursive: true });
    await writeFile(file, `${JSON.stringify(onDisk, null, 2)}\n`, "utf8");

    const loaded = await loadState(repoRoot, qid, spec);
    expect(loaded.flags).toMatchObject(legacyFlags);
    expect(loaded).toMatchObject(legacyTop);
    expect(loaded.proposed_from).toMatchObject(legacyProposal);
    await saveState(repoRoot, qid, spec, loaded);

    const resaved = JSON.parse(await readFile(file, "utf8")) as Record<string, unknown> & {
      flags: Record<string, unknown>;
      added_assumptions: Array<Record<string, unknown>>;
    };
    expect(resaved.flags).toMatchObject(legacyFlags);
    expect(resaved).toMatchObject(legacyTop);
    expect(resaved.proposed_from).toMatchObject(legacyProposal);
    expect(resaved.added_assumptions[0]).toMatchObject({ user_approved: true, reviewed: false });
  });

  it("round-trips a valid state and enforces qid/lean_subdir", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-state-"));
    const state = createInitialState("panel_minimal_basis");
    await saveState(repoRoot, "panel_minimal_basis", "p1_bernoulli", state);
    const loaded = await loadState(repoRoot, "panel_minimal_basis", "p1_bernoulli");
    expect(loaded.lean_subdir).toBe("CausalSmith/Panel/PANEL_MinimalBasis_Research");

    const file = statePath(repoRoot, "panel_minimal_basis", "p1_bernoulli");
    expect(await readFile(file, "utf8")).toContain('"stage_completed": "-1.2"');
  });

  it("migrates a legacy serialized draft handoff to the compact version marker", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-draft-marker-"));
    const qid = "panel_minimal_basis";
    const spec = "p1_bernoulli";
    const state = createInitialState(qid);
    state.proposed_from = {
      topic: "test",
      novelty_target: "field",
      final_verdict: "pending",
      proposal_path: "proto_core.json",
      novelty_justification: "test",
      chosen_qid: qid,
      chosen_specialization: spec,
      current_version: 4,
      last_draft_status: "completed",
      last_draft_handoff: '{"status":"completed","large":"payload"}',
    };
    const file = statePath(repoRoot, qid, spec);
    await mkdir(path.dirname(file), { recursive: true });
    await writeFile(file, `${JSON.stringify(state, null, 2)}\n`, "utf8");

    const loaded = await loadState(repoRoot, qid, spec);
    expect(loaded.proposed_from?.last_draft_version).toBe(4);
    expect(loaded.proposed_from?.last_draft_handoff).toBeUndefined();
  });

  it("converts qid to canonical CamelCase Lean subdir with mode suffix", () => {
    // Research-mode qids carry a `_Research` suffix.
    expect(qidToCamel("panel_spectral_threshold")).toBe("PANEL_SpectralThreshold_Research");
    expect(canonicalLeanSubdir("panel_spectral_threshold")).toBe(
      "CausalSmith/Panel/PANEL_SpectralThreshold_Research",
    );
    // Study-mode (insight-style) qids carry a `_Study` suffix.
    expect(qidToCamel("manski_nonparametric_bounds")).toBe("ManskiNonparametricBounds_Study");
  });

  it("rejects drifted lean_subdir", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-bad-state-"));
    const state = createInitialState("panel_minimal_basis");
    state.lean_subdir = "CausalSmith/Panel/PANEL_Wrong";
    await expect(saveState(repoRoot, "panel_minimal_basis", "p1_bernoulli", state)).rejects.toThrow(
      /invariant failed/,
    );
  });

  it("accepts a cluster-consistent proposal re-anchor", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-reanchored-state-"));
    const qid = "stat_bounds_kernel";
    const state = createInitialState(qid);
    state.proposed_from = {
      topic: "test",
      novelty_target: "field",
      final_verdict: "ACCEPT",
      proposal_path: "proto_core.json",
      novelty_justification: "test",
      chosen_qid: qid,
      chosen_specialization: "v1",
      cluster: "partialid",
    };
    state.lean_subdir = "CausalSmith/PartialID/STAT_BoundsKernel_Research";
    await saveState(repoRoot, qid, "v1", state);
    expect((await loadState(repoRoot, qid, "v1")).lean_subdir).toBe(state.lean_subdir);
  });

  // The re-anchor widening admits the DECLARED cluster's substrate and nothing
  // else: the module name still comes from the qid, and the substrate still comes
  // from a closed enum. Without this the widening has acceptance coverage only,
  // and a later refactor of the name extraction could let any path through while
  // the positive test stayed green.
  it("still rejects a destination the re-anchored cluster does not license", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-reanchor-reject-"));
    const qid = "stat_bounds_kernel";
    const base = createInitialState(qid);
    base.proposed_from = {
      topic: "test",
      novelty_target: "field",
      final_verdict: "ACCEPT",
      proposal_path: "proto_core.json",
      novelty_justification: "test",
      chosen_qid: qid,
      chosen_specialization: "v1",
      cluster: "partialid",
    };
    for (const subdir of [
      // a substrate the declared cluster does not name
      "CausalSmith/SCM/STAT_BoundsKernel_Research",
      // the right substrate, but a module name that is not this qid's
      "CausalSmith/PartialID/PID_SomethingElse_Research",
      // outside the package root
      "CausalSmith/PartialID/../../etc/STAT_BoundsKernel_Research",
    ]) {
      const state = { ...base, lean_subdir: subdir } as typeof base;
      await expect(
        saveState(repoRoot, qid, "v1", state),
        `${subdir} must not satisfy the invariant`,
      ).rejects.toThrow(/invariant failed/);
    }
  });

  it("accepts proposed_from.final_verdict: null so hand-edited resumes load", () => {
    // Manual operators sometimes need to clear the verdict between resume
    // attempts (e.g. re-run D0 with an upgraded solver on a previously
    // banked proposal). Schema must accept null.
    const parsed = stateSchema.parse({
      stage_completed: "-0.5",
      lean_subdir: "CausalSmith/ExactID/Foo",
      pending_sorries: [],
      design_decisions: {},
      added_assumptions: [],
      flags: { missing_architecture: false },
      proposed_from: {
        topic: "t",
        novelty_target: "flagship",
        pivot_budget_used: 0,
        final_verdict: null,
        proposal_path: "/tmp/p.tex",
        novelty_justification: "",
        chosen_qid: "eid_foo",
        chosen_specialization: "v1",
      },
    });
    expect(parsed.proposed_from?.final_verdict).toBeNull();
  });

  it("accepts proposed_from.iterations[].version: 0 (pre-draft pivot marker)", () => {
    // Historical pipelines emit `version: 0` when pivoting to a new angle
    // before drafting; banked entries with this artifact must load on resume.
    const parsed = stateSchema.parse({
      stage_completed: "-0.5",
      lean_subdir: "CausalSmith/ExactID/Foo",
      pending_sorries: [],
      design_decisions: {},
      added_assumptions: [],
      flags: { missing_architecture: false },
      proposed_from: {
        topic: "t",
        novelty_target: "flagship",
        pivot_budget_used: 0,
        final_verdict: "ACCEPT",
        proposal_path: "/tmp/p.tex",
        novelty_justification: "",
        chosen_qid: "eid_foo",
        chosen_specialization: "v1",
        iterations: [
          { angle: 2, version: 0, mode: "pivot", verdict: "REVISE" },
          { angle: 2, version: 1, mode: "revise", verdict: "REVISE" },
        ],
      },
    });
    expect(parsed.proposed_from?.iterations?.[0].version).toBe(0);
    expect(parsed.proposed_from?.iterations?.[1].version).toBe(1);
  });

  it("finds active states using qid prefix rather than underscore counting", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-active-state-"));
    await saveState(
      repoRoot,
      "panel_minimal_basis",
      "p1_iid_bernoulli",
      createInitialState("panel_minimal_basis"),
    );
    const active = await findActiveStates(repoRoot);
    expect(active).toHaveLength(1);
    expect(active[0].specialization).toBe("p1_iid_bernoulli");
  });

  it("finds study active states whose qid looks research-like", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-active-study-"));
    const qid = "stat_paper_insight";
    const dir = path.join(repoRoot, "doc", "study", "runs", qid);
    await mkdir(dir, { recursive: true });
    await writeFile(path.join(dir, "state.json"), JSON.stringify({
      ...createInitialState(qid),
      specialization: "default",
      qid,
      lean_subdir: "CausalSmith/Stat/STAT_PaperInsight_Research",
    }), "utf8");
    const active = await findActiveStates(repoRoot);
    expect(active.map((a) => a.path)).toEqual([path.join(dir, "state.json")]);
  });
});

describe("state schema — stage migration", () => {
  it("loads a banked state whose proposer stage is labelled -1", () => {
    const parsed = stateSchema.parse({
      stage_completed: "-1",
      lean_subdir: "CausalSmith/Stat",
      design_decisions: {},
      flags: { missing_architecture: false },
    });

    expect(parsed.stage_completed).toBe("-1.2");
  });
});

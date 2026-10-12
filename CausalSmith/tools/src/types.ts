import type { STAGE_ORDER } from "./constants.js";
import type { NoveltyTarget } from "./novelty.js";

export type Stage = (typeof STAGE_ORDER)[number];

export const UPGRADE_AXES = ["computation", "estimation", "generalization", "mechanism"] as const;
export type UpgradeAxis = (typeof UPGRADE_AXES)[number];

export const UPGRADE_PARENT_TIERS = ["accepted", "downgraded"] as const;

export interface UpgradeFrom {
  parent_qid: string;
  parent_spec: string;
  parent_tier: (typeof UPGRADE_PARENT_TIERS)[number];
  upgrade_axis: UpgradeAxis;
}

export interface AddedAssumption {
  label: string;
  statement: string;
  source?: string;
  /** The node the premise attaches to (`bin/gate.ts` records the gate's parent or consumer). */
  anchor?: string;
  /**
   * Faithfulness class of the premise, on the invariant-#10 crux-vs-gate axis:
   *  - `faithful-refinement`: the paper already states/implies it in this setting.
   *  - `regularity-bookkeeping`: a measurability/integrability/finiteness side-condition.
   *  - `substrate-gate`: a genuinely classical, dischargeable fact (must be built before banking).
   */
  classification?: "faithful-refinement" | "regularity-bookkeeping" | "substrate-gate";
}

export interface MissingItem {
  kind: string;
  name_suggestion: string;
  purpose: string;
  why_substantial: string;
  nl_artifact_reference?: string;
  suggested_location?: string;
}

/**
 * `StateJson` is the intersection of three interfaces:
 *
 *   • `SharedState` — the stage cursor, the Lean directory and the run coordinates.
 *   • `DiscoveryState` — literature gaps and proposer state.
 *   • `FormalizationState` — design decisions, added assumptions and F4 receipts.
 *
 * `StateJson` is the type for I/O (see `src/state.ts::stateSchema`). Its `flags`
 * object is `DiscoveryFlags & FormalizationFlags`.
 */

export interface DiscoveryFlags {
  stage_neg1_fallback?: string | null;
  /**
   * D0.5.G directed-reroute counter. Incremented when a below-floor note is offered a
   * reroute — sent back to D0 with a bounded improvement directive (better estimator /
   * derive an assumed condition / tighten a bound) rather than halted as unsalvageable.
   * Both paths stop at an operator checkpoint; this counts only the ones that hand D0
   * something to re-solve. Enforced against `GENERAL_REROUTE_CAP` (default 2) in
   * `runStage0_5Typed`, so a topic whose referee keeps emitting plausible-but-ineffective
   * directives cannot re-solve indefinitely. Persisted because each reroute ends the
   * process — an in-process bound would reset on every `--resume` and never bind.
   */
  general_reroute_count?: number;
  /**
   * F3 phase-B proof-fill directive. An optional load-bearing PROOF hint the
   * orchestrator injects for the filler agent (lemma names / tactic strategy /
   * Mathlib API) when the proof-fill loop is stuck. Loop-wide and persistent:
   * injected into EVERY filler call for the rest of phase B until the orchestrator
   * clears it (unlike the one-shot correction directives, it is NOT auto-cleared).
   * Mirrors the D0 escalation-log directive channel. It is a proof hint ONLY — the
   * per-iteration anti-laundering + assumption/def gates still reject any use that
   * changes a statement, adds an unsanctioned hypothesis, or axiomatizes a goal.
   */
  f3_filler_directive?: string | null;
  /** Persistent orchestrator F2 scaffold directive (analogue of `f3_filler_directive`):
   *  read on every scaffold/revise pass as a top-priority faithfulness constraint,
   *  persists across resumes until cleared via `bin/f2_directive.ts`. */
  f2_scaffold_directive?: string | null;
}

/**
 * Crosswalk verdict vocabulary: `equivalent` passes, `drift` blocks, and
 * `unmatched` marks a row the reviewer has not judged.
 */
export type CrosswalkVerdict = "equivalent" | "drift" | "unmatched";

/**
 * One row of the paper↔Lean crosswalk, projected from the graph. Durable anchors
 * are `obj_id` (paper side) and `(lean.file, lean.decl)` (Lean side); `lean.line`
 * and `tex.line_range` are convenience and re-derivable.
 */
export interface CrosswalkEntry {
  obj_id: string;
  kind: "definition" | "assumption" | "theorem" | "lemma" | "proposition";
  title: string;
  tex: { label: string; line_range: string };
  lean: { file: string; decl: string; decl_kind: string; line: number } | null;
  verdict: CrosswalkVerdict;
  note?: string;
}

export interface FormalizationFlags {
  missing_architecture: boolean;
  missing_architecture_items?: MissingItem[];
  /** One-shot re-scaffold directive from the proof-review loop; consumed by runStage2 then cleared on success. */
  scaffold_redirect?: string | null;
  /** The proof-review loop's iteration budgets, PERSISTED across resumes. These used to be
   * in-process locals, so every `--resume` silently handed the loop a fresh budget — an
   * orchestrator could re-roll the (non-deterministic) reviewer indefinitely with no flag, no
   * audit trail, and no gate. Persisting them makes a cap a real circuit breaker. */
  proof_loop_counters?: {
    iters: number;
    scaffold_rounds: number;
    stale: number;
    tag_reroutes: number;
    node_strikes: Record<string, number>;
    /** Hash-keyed counts of identical F2.5 target+diagnostic signatures. */
    review_error_strikes: Record<string, number>;
    /** Hash of the last red `lake build` diagnostic, so the identically-red no-progress
     * cap survives a `--resume` instead of resetting `stale` on every re-entry. */
    last_build_error_sig?: string;
    /** Last few one-line filler session summaries (the anti-identical-prompt memory).
     * Persisted for the same reason as the counters: as an in-process local, every
     * `--resume` restarted Phase B with byte-identical filler prompts until new summaries
     * accumulated — the exact repeat-dead-end waste the memory exists to stop. */
    filler_summaries?: string[];
  };
  /** Set when any `proof_loop_counters` budget is exhausted. BLOCKS `--resume` until cleared via
   * `--clear-gate proof_loop_cap_hit`. Only MAIN may clear it (a sub never resets its own cap). */
  proof_loop_cap_hit?: string;
  /** D-phase loop budgets, persisted for the same reason as `proof_loop_counters`: the D0
   *  solve loop and the D0.5 revise loop were plain in-process `for` bounds, so a plain
   *  `--resume` handed each a FRESH budget — 15 more multi-unit solve rounds, 3 more
   *  (3-referee panel + D0.R) rounds — unbounded and unaudited. `consistency_heals`
   *  migrated here from `design_decisions` so a cap gate can reset it. */
  d0_loop_counters?: {
    solve_rounds: number;
    revise_rounds: number;
    consistency_heals: number;
  };
  /** Set when any `d0_loop_counters` budget is exhausted. BLOCKS `--resume` until cleared
   *  via `--clear-gate d0_loop_cap_hit`. */
  d0_loop_cap_hit?: string;
  /** How many D0 escalation-journal entries have been shown to a solver round
   *  (see `discovery/escalation_log.ts`). Entries beyond it are pending. */
  d0_directives_consumed?: number;
  /** The graph's main commit when the current D0.5 invocation began; D0.R edits past
   *  it are provisional until PASS and are reset on the next entry otherwise. */
  d0_5_head_before?: string;
  /** D-0.5 producer env-failure retries, persisted for the same reason as the D0 counters:
   *  a process-local counter meant every resume re-granted the full retry budget while
   *  `last_draft_status` stayed "env-failure", looping forever. Reset by the
   *  `stage_neg1_fallback` gate. */
  neg1_env_failure_retries?: number;
  /**
   * Durable fail-closed record that the combined F2.5 proof-review loop returned
   * an escalation without converging. While present, the dispatcher must not
   * enter the retired F3/F3.5/F4 pass-through slots or F5. It is cleared only
   * after a genuine `runProofReviewLoop` completion.
   */
  proof_review_escalation_pending?: {
    route: string;
    reason: string;
  } | null;
  /** One-shot orchestrator directive for the F1 planner (`bin/f1_directive.ts`); consumed by runStage1's revise mode, then cleared once the plan is gate-clean. */
  f1_revise_directive?: string | null;
  /** F3→D0 rewind counter, keyed by the broken node's obj_id (cap `REDO_MATH_MAX`). Bumped each time
   * a witnessed `statement-wrong` bounces that node back to D0-solve; a node exceeding the cap (or one
   * whose re-solve would invalidate already-PROVEN dependents) checkpoints for orchestrator approval
   * instead of auto-rewinding. Persists across `--resume` so the cap bounds total ping-pong. */
  redo_math_rewinds?: Record<string, number>;
  /** The witness + blast-radius parked for the rewound D0-SOLVE to CONSUME: re-derive `obj_id` and its
   * `dependents` (never from scratch) treating the obstruction as a hard constraint, so the re-solve
   * cannot regenerate the same refuted claim. Cleared by D0-solve once consumed. */
  redo_math_witness?: { obj_id: string; type: string; detail: string; dependents: string[] };
}

/**
 * Cross-phase fields: stage cursor, target Lean directory, run coordinates.
 * Touched by orchestrator and both submodules.
 */
export interface SharedState {
  stage_completed: Stage;
  lean_subdir: string;
  /**
   * Self-identifying run coordinates. Stamped on every save (see `saveState`)
   * so the qid/spec survive the causalsmith-style bare `state.json` filename
   * that no longer encodes the spec. Optional for back-compat with pre-rename
   * state files (whose spec is still recoverable from their prefixed filename).
   */
  qid?: string;
  specialization?: string;
  /**
   * Auto mode — set by `--auto` (cold start or any `--resume`). When true the
   * meta-orchestrator makes every checkpoint decision itself per the skill and
   * `--resume`s WITHOUT asking the user; it stops only on a terminal failure or
   * at CKPT 2 (F5 bank/promote/commit, which always waits). Persisted so a run
   * stays autonomous across resumes even if a later `--resume` omits `--auto`,
   * and re-surfaced on every checkpoint line (`checkpointGuidance` banner) so
   * the orchestrator does not forget it is autonomous and revert to asking.
   */
  auto_mode?: boolean;
}

/**
 * Discovery-phase fields (Stages −1.1 … 1.5): literature gaps, proposer state.
 */
export interface DiscoveryState {
  /** The proposal invocation, persisted at init so a bare `--resume` after a halt
   * still knows the topic / tier / upgrade lineage (stage numbers alone cannot
   * say that). `scout_refresh` marks a deliberate D-1.1 re-entry. */
  pre_d0_intent?: {
    cursor_version: 1;
    topic: string;
    novelty_target: NoveltyTarget;
    upgrade_from?: UpgradeFrom;
    scout_refresh?: boolean;
  };
  /**
   * Open-problem substrate produced by Stage -1.1 (literature scout). Populated
   * before Stage -1.2 (proposer) runs, so the proposer's seed-generation step
   * can anchor every seed to either a published paper or a prior CausalSmith
   * proposal/reviewer signal listed here. Absent until Stage -1.1 succeeds; in
   * non-propose mode, never populated.
   */
  gaps?: {
    /** Absolute or repo-relative path to the gaps.json artifact on disk. */
    gaps_path: string;
    /** Number of open problems recorded; must be ≥ 3 when status is "completed". */
    n_open_problems: number;
    /**
     * "completed" → advance to Stage -1.2.
     * "needs-pivot" → quantity bar failed (<3 problems after G1–G5) OR the
     * scout returned an unrecognized verdict; orchestrator halts so the user
     * can broaden/replace the topic. (A separate "rejected" R1–R4 verdict was
     * documented here historically but never implemented — the prompt, zod
     * schema, and handler only know completed|needs-pivot. Do not write
     * "rejected" into state: the schema refuses it on load.)
     */
    status: "completed" | "needs-pivot";
  };
  proposed_from?: {
    topic: string;
    novelty_target: NoveltyTarget;
    final_verdict: string | null;
    proposal_path: string;
    novelty_justification: string;
    chosen_qid: string;
    chosen_specialization: string;
    cluster?: "panel" | "exactid" | "partialid" | "stat" | "experimentation" | "scm";
    seed_list?: string[];
    seed_details?: Array<Record<string, unknown>>;
    literature_map?: string;
    current_angle_index?: number;
    current_version?: number;
    current_mode?: "cold-start" | "revise" | "draft-rebuild" | "kernel-replace" | "pivot";
    /** Per-angle revision ceilings persisted by the angle-action CLI. Keys are
     * decimal angle indices. This replaces one-off environment-variable cap
     * bumps, so retries remain reproducible across resumes. */
    revision_cap_by_angle?: Record<string, number>;
    /** Halt written after a D-0.5 review and before another proposer starts.
     * `revise` lets the D-orchestrator persist a directive before continuing;
     * `angle-boundary` requires an explicit switch/retry/give-up decision. */
    angle_checkpoint?: {
      kind: "revise" | "angle-boundary";
      angle: number;
      version: number;
      verdict: string;
      reason: string;
      revise_cap: number;
      next_angle?: number;
    };
    kernel_replace_used_angles?: number[];
    draft_rebuild_used_angles?: number[];
    /** Version of the completed draft awaiting review. Equal to
     * `current_version` exactly when the current proto core is fresh. */
    last_draft_version?: number;
    /** @deprecated Read-only compatibility for states written before the
     * compact version marker. `loadState` migrates it in memory. */
    last_draft_handoff?: string;
    /** `producer-queued` is accepted on load only (migrated to `completed`). */
    last_draft_status?: "completed" | "producer-queued" | "needs-pivot" | "invalid-draft" | "env-failure";
    exhausted_angles?: number[];
    last_reviewer_verdict?: string;
    iterations?: Array<{
      angle: number;
      version: number;
      mode: string;
      verdict: string;
      tier?: string;
      clean_substance?: boolean;
    }>;
    archived_proposals?: string[];
    upgrade_from?: UpgradeFrom;
  };
}

/** One cited node's persisted F4 source-match verdict. See {@link FormalizationState.cited_checks}. */
export interface CitedCheck {
  name: string;
  check_status: string;
  cite_id?: string;
  locator?: string;
  reviewer?: "codex" | "claude";
}

/** Durable, source-bound proof that one F4 peer checked a delivered cited node.
 * Unlike the compatibility `cited_checks` summary, this preserves peer identity and locator. */
export interface CitedReviewReceipt {
  node_id: string;
  reviewer: "codex" | "claude";
  check_status: string;
  cite_id: string;
  locator: string;
  evidence_hash: string;
}

/** Durable proof that each F4 peer independently accepted one disclosed omission.
 * The evidence hash binds the receipt to the current plan/graph contribution evidence,
 * so changing a role, reason, or dependency closure invalidates an old receipt. */
export interface DeliveryReviewReceipt {
  node_id: string;
  reviewer: "codex" | "claude";
  verdict: "matched" | "drift";
  evidence_hash: string;
  note?: string;
}

/** Formalization-phase fields: free-form design notes, disclosed added assumptions, F4 receipts. */
export interface FormalizationState {
  design_decisions: Record<string, string>;
  added_assumptions: AddedAssumption[];
  /**
   * The F4 reviewer's CITED source-match verdicts. `cited-mismatch` / `cited-underspecified`
   * hard-block banking; persisting them lets `bankEntry` enforce that outside the review loop,
   * where the check previously lived only in memory.
   *
   * Optional for backward compatibility: every state written before this field existed omits it,
   * and the Zod schema defaults it to `[]` on parse. Absent ⇒ no cited nodes ⇒ nothing to block.
   */
  cited_checks?: CitedCheck[];
  cited_review_receipts?: CitedReviewReceipt[];
  delivery_review_receipts?: DeliveryReviewReceipt[];
}

export interface StateJson
  extends SharedState,
    DiscoveryState,
    FormalizationState {
  flags: DiscoveryFlags & FormalizationFlags;
}

export interface PipelineContext {
  repoRoot: string;
  qid: string;
  specialization: string;
  dryRun: boolean;
  resume: boolean;
  /** `--auto`: drive the run autonomously (see `SharedState.auto_mode`). Persisted onto state. */
  auto?: boolean;
  proposeTopic?: string;
  noveltyTarget?: NoveltyTarget;
  upgradeFrom?: UpgradeFrom;
}

export interface StageResult {
  stage: Stage;
  /**
   * Loop-control semantics:
   *  - `completed` / `skipped`: pipeline advances to `nextStage(stage)`.
   *  - `checkpoint`: pipeline halts; user must `--resume`. Use when the orchestrator must decide before the next stage can run (the CKPTs, a NO-PASS, a proof-review escalation).
   *  - `blocked`: pipeline halts; `state.flags` carries the block reason. Used for missing-architecture and pre-Stage-(-1) gates.
   *  - `rewound`: handler programmatically reset `state.stage_completed` to an earlier marker; pipeline continues from `nextStage(state.stage_completed)`. Use when an escalation routes back to an earlier stage WITHOUT needing a decision (the witnessed F3→D0 rewind). `advance: false` MUST be set so the loop does not overwrite the handler's reset.
   */
  status: "completed" | "checkpoint" | "blocked" | "skipped" | "rewound";
  message: string;
  advance?: boolean;
  completedStage?: Stage;
}

export interface PipelineLogEntry {
  timestamp: string;
  stage: Stage | "resume" | "init";
  model?: string;
  status: string;
  duration_ms: number;
  message?: string;
  /**
   * Condensed orchestrator reminder for a checkpoint/blocked halt: what to do
   * at this checkpoint + what the next phase is, with a pointer to the canonical
   * SKILL section. Populated by `checkpointGuidance`; absent on ordinary
   * `completed` transitions. The causalsmith-main skill tells the meta-orchestrator
   * to read this on the last pipeline.jsonl line so it re-grounds after a long run.
   */
  next_step_guidance?: string;
}

import { loadBankEntry, type BankEntry } from "./bank.js";
import type { ClaudeModel } from "../models.js";
import type { Lookup } from "./citations.js";
import { loadPaperState, savePaperState, freshPaperState } from "./state.js";
import { access } from "node:fs/promises";
import { join } from "node:path";
import { presentationDir } from "./paths.js";
import { type PaperStage, type PaperState } from "./types.js";
import { stageP0 } from "./stages/p0_literature.js";
import { stageP1 } from "./stages/p1_plan.js";
import { stageP2 } from "./stages/p2_draft.js";
import { stageP3 } from "./stages/p3_gates.js";
import { stageP4 } from "./stages/p4_emit.js";
import { stageP5 } from "./stages/p5_review.js";
import { loadPriorReview } from "./revision_brief.js";
import { PROMOTION_ESCALATION_MARKER, PROOF_AUDIT_FAILURE_MARKER, runPromotionRound } from "./promotion.js";
import { renderRoutingPlan } from "./revision_routing.js";
import { withPresentationTokenUsage } from "./token_usage.js";
import type { ModelTokenUsage } from "../token_usage.js";

/** Injected model runners (matches src/workers/claude.ts and src/shared/codex.ts). */
export interface PaperDeps {
  /** Resolved default model for model-sensitive presentation caches/logging. */
  codexModel?: string;
  runClaude: (args: {
    prompt: string;
    model: ClaudeModel;
    cwd: string;
    allowedTools?: string[];
    /** See ClaudeRunInput.onResolvedModel — surfaces the id an alias like "opus" resolved to. */
    onResolvedModel?: (modelId: string) => void;
    /** Exact aggregate usage from the terminal Claude result event. */
    onUsage?: (usage: ModelTokenUsage) => void;
    /** Strict JSON Schema for the reply (see reply_schemas.ts). */
    jsonSchema?: Record<string, unknown>;
  }) => Promise<string>;
  runCodex: (args: {
    prompt: string;
    cwd: string;
    reasoningEffort?: "minimal" | "low" | "medium" | "high" | "xhigh";
    leanLsp?: boolean;
    webSearch?: boolean;
    /** codex model id override (present mode defaults to MODELS.codexPresentation). */
    model?: string;
    /** Narrow this call to a read-only or cwd-scoped writable sandbox. */
    sandboxMode?: "read-only" | "workspace-write";
    /** Codex native sub-agents — default-off (opt-in); set true only for a lone low-concurrency call whose prompt uses spawn_agent (see CodexRunInput.multiAgent). */
    multiAgent?: boolean;
    /** Exact cumulative usage from this Codex session, including native subagents. */
    onUsage?: (usage: ModelTokenUsage) => void;
    /** Strict JSON Schema for the reply (see CodexRunInput.outputSchema). */
    outputSchema?: Record<string, unknown>;
  }) => Promise<{ stdout: string; stderr: string }>;
  /** Citation metadata lookup; defaults to live Crossref/arXiv (citations.defaultLookup). */
  lookup?: Lookup;
  dryRun: boolean;
}

export interface PaperCtx {
  repoRoot: string;
  qid: string;
  spec: string;
  deps: PaperDeps;
  resume?: boolean;
  /** Approve the P1/P2 human checkpoints automatically. Hard gates and the
   * hand-revision halt are unchanged. */
  auto?: boolean;
  stopAfter?: PaperStage;
  /** Re-enter the pipeline at this stage (e.g. `--from P4` to re-emit + re-review
   * after the orchestrator edits paper.tex per the P5 referee report). Loads
   * prior state and runs forward from here, ignoring stage_completed. */
  from?: PaperStage;
  /** Output dir override (tests MUST set this — the default is the live run dir). */
  outDir?: string;
  /** With `--from P1`: render the whole layer afresh instead of starting from approved bodies.
   * Replace the accepted bank bodies only after the new layer passes both judges. */
  refreshFrozenBodies?: boolean;
  /**
   * Grant one further P2 promotion round. The orchestrator sets this after reading the audit
   * findings on a `P2 promotion decision required` halt and judging that the failing proofs lack
   * a citable step rather than being mis-rendered.
   */
  promoteAgain?: boolean;
}

export interface StageIO {
  ctx: PaperCtx;
  state: PaperState;
  bank: BankEntry;
  outDir: string;
  /** P2 only, revision cycle: reassemble paper.tex from the on-disk authored
   * sources (hand-edited by the orchestrator); only a missing file is drafted. */
  reassemble?: boolean;
  /** Revision entry (`--from P2` over authored sources): P3 runs hard gates only and
   * skips the rubric — the P5 referee is the judge of a revision, so re-scoring it
   * here duplicates full-paper calls per cycle. */
  revisionCycle?: boolean;
}

export type StageFn = (io: StageIO) => Promise<void>;

function stageIO(
  ctx: PaperCtx,
  state: PaperState,
  bank: BankEntry,
  outDir: string,
  stage: PaperStage,
  options: Pick<StageIO, "reassemble" | "revisionCycle"> = {},
): StageIO {
  return {
    ctx: { ...ctx, deps: withPresentationTokenUsage(ctx.deps, outDir, stage) },
    state,
    bank,
    outDir,
    ...options,
  };
}

const ORDER: { stage: PaperStage; fn: StageFn; checkpointAfter?: "outline" | "draft" }[] = [
  { stage: "P0", fn: stageP0 },
  { stage: "P1", fn: stageP1, checkpointAfter: "outline" },
  { stage: "P2", fn: stageP2, checkpointAfter: "draft" },
  { stage: "P3", fn: stageP3 },
  { stage: "P4", fn: stageP4 },
  { stage: "P5", fn: stageP5 },
];

export async function runPaperPipeline(ctx: PaperCtx): Promise<{ halt: string }> {
  const outDir = ctx.outDir ?? presentationDir(ctx.repoRoot, ctx.qid, ctx.spec);
  // `--from P2` over an already-drafted bundle (front_matter.tex is P2's last authored write)
  // reassembles the authored sources instead of drafting: hand edits are the canonical text,
  // and only a missing file is drafted. Delete front_matter.tex to request a fresh draft.
  const reassembleP2 = ctx.from === "P2" && await access(join(outDir, "front_matter.tex")).then(() => true, () => false);
  let bank = await loadBankEntry(ctx.repoRoot, ctx.qid, ctx.spec);
  const prior = await loadPaperState(outDir, ctx.qid, ctx.spec);
  // A bundle with recorded state is continued, never silently restarted: a fresh state would
  // discard the promotion budget, the P5 pass count and every note, and re-pay P0.
  if (prior && !ctx.resume && !ctx.from && !ctx.auto && !ctx.deps.dryRun) {
    throw new Error(
      `presentation state for ${ctx.qid}/${ctx.spec} already exists (stage_completed ${prior.stage_completed ?? "none"}): ` +
        `continue with --resume, re-enter with --from <stage>, or delete the state file to start over`,
    );
  }
  const state = prior && (ctx.resume || ctx.from || ctx.auto) ? prior : freshPaperState(ctx.qid, ctx.spec);
  if (state.checkpoint_pending && ctx.resume) state.checkpoint_pending = null; // resume = checkpoint approved
  if (state.checkpoint_pending && ctx.auto) state.checkpoint_pending = null; // auto = checkpoint approved
  let startIdx: number;
  if (ctx.from) {
    startIdx = ORDER.findIndex((s) => s.stage === ctx.from);
    if (startIdx < 0) throw new Error(`unknown --from stage: ${ctx.from}`);
    state.checkpoint_pending = null; // explicit re-entry overrides any pending checkpoint

  } else {
    startIdx = state.stage_completed
      ? ORDER.findIndex((s) => s.stage === state.stage_completed) + 1
      : 0;
  }
  let promotionUsed = false;
  for (let i = startIdx; i < ORDER.length; i++) {
    const { stage, fn, checkpointAfter } = ORDER[i];
    // Once a referee review exists, P5 is the holistic judge: a plain --resume that lands on P3
    // must not re-buy the rubric and its advisory repair on a paper P5 already scored.
    const reviewed = stage === "P3" && (await loadPriorReview(outDir)) !== null;
    const io = stageIO(ctx, state, bank, outDir, stage, {
      reassemble: stage === "P2" && reassembleP2,
      revisionCycle: reassembleP2 || reviewed,
    });
    // Persist state BEFORE re-throwing a stage failure: stages push notes and set
    // hard_gate_failures while running, and state otherwise reaches disk only on stage
    // success — so every failure exit silently discarded its own diagnosis (P3 grew a
    // local workaround, failP3; every other stage lost its notes — audit, 2026-08-26).
    // Best-effort: a save failure must never mask the stage's real error.
    const failStage = async (err: unknown): Promise<never> => {
      try {
        await savePaperState(outDir, state);
      } catch { /* keep the original error */ }
      throw err;
    };
    try {
      await fn(io);
    } catch (err) {
      // PROMOTION ROUND (once per invocation): a P2 proof-audit failure usually means the
      // failing steps' content needs to become citable auxiliary lemmas. Author them
      // (agent call), re-run P1 as a cheap delta (only new statements render/audit),
      // and retry P2 once. Anything else — or a second failure — propagates as before.
      const msg = err instanceof Error ? err.message : String(err);
      // Never in a reassemble/revision re-entry: new formal environments are forbidden
      // there (no draft checkpoint would review them, and a promoted lemma has no
      // rendered proof for the reassemble guard to reuse).
      if (stage !== "P2" || promotionUsed || reassembleP2 || !msg.includes(PROOF_AUDIT_FAILURE_MARKER)) await failStage(err);
      // Bounded across the whole bundle, not just this invocation: `promotionUsed` caps rounds
      // per process, so re-entering P2 repeatedly grants a fresh round each time and the chain
      // grows without limit. The persisted budget is what actually terminates it; at the cap the
      // run halts for adjudication rather than promoting again.
      if (state.promotion_rounds > 0 && ctx.promoteAgain !== true) {
        state.notes.push(
          `P2 promotion decision required after ${state.promotion_rounds} round(s): the orchestrator decides ` +
            `whether another round closes a gap or the proofs need adjudicating.`,
        );
        await savePaperState(outDir, state);
        throw new Error(
          `${PROMOTION_ESCALATION_MARKER}: ${state.promotion_rounds} promotion round(s) already ran and proofs ` +
            `still fail the audit. Read the findings below and decide. A further round helps only when a proof ` +
            `lacks a CITABLE STEP; it cannot fix a rendering defect (leaked conventions, mis-attribution, an ` +
            `omitted conjunct, symbol shadowing), which needs the proof or the statement adjudicated instead. ` +
            `To grant another round, re-run with --promote-again.\n\n${msg}`,
        );
      }
      promotionUsed = true;
      // Record the round BEFORE the agent mutates graph.json: a crash between the graph edit and
      // this save would otherwise hand the next process a fresh automatic round over an
      // already-grown graph, which is the cascade this guards. The trade-off is that a crashed
      // or refused promotion still consumes the automatic round — recoverable, since the
      // orchestrator can grant another with --promote-again, and loud either way.
      state.promotion_rounds += 1;
      await savePaperState(outDir, state);
      const added = await runPromotionRound(io, msg);
      state.notes.push(
        `P2 promotion round ${state.promotion_rounds}: added ${added} — review at the draft checkpoint.`,
      );
      await savePaperState(outDir, state);
      // The promotion agent edited graph.json ON DISK; the loaded bank (graph, crosswalk,
      // lean pointers) is stale. Reload so the P1 re-run, the P2 retry, and every later
      // stage see the new nodes.
      bank = await loadBankEntry(ctx.repoRoot, ctx.qid, ctx.spec);
      const retryIo = { ...io, bank };
      try {
        await stageP1(stageIO(ctx, state, bank, outDir, "P1", { reassemble: false }));
        await fn(retryIo);
      } catch (retryErr) {
        await failStage(retryErr); // the retry's notes must survive its failure too
      }
    }
    state.stage_completed = stage;
    // A reassemble re-entry is a revision of an already-reviewed draft, not a first
    // draft awaiting approval — do not halt it at the P2 draft checkpoint.
    const skipCheckpoint = ctx.auto || (stage === "P2" && reassembleP2);
    if (checkpointAfter && !skipCheckpoint) state.checkpoint_pending = checkpointAfter;
    await savePaperState(outDir, state);
    if (ctx.stopAfter === stage) return { halt: `stopped:${stage}` };
    if (checkpointAfter && !skipCheckpoint) return { halt: `checkpoint:${checkpointAfter}` };
  }
  // The referee's findings are the orchestrator's to fix by hand: a review that is not a clean
  // accept halts with its routing plan (fix-by-hand / adjudication / user-scope) already written
  // by P5. There is no unattended reviser pass — on three papers hand rounds moved the score and
  // the reviser never did (2026-09-10).
  if (!ctx.deps.dryRun) {
    const review = await loadPriorReview(outDir);
    if (review && !(review.recommendation === "accept" && review.findings.length === 0)) {
      const note = `P5: review recorded (${review.recommendation}, ${review.findings.length} finding(s)); routed in p5_revision_routing.md for hand revision.`;
      if (!state.notes.includes(note)) state.notes.push(note);
      await savePaperState(outDir, state);
      return { halt: "p5:hand-revision" };
    }
  }
  return { halt: "done" };
}

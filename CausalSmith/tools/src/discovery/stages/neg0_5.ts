// Discovery Stage -0.5 (proposal reviewer + angle/revise/pivot loop).
// Extracted from pipeline_stages.ts in Step 2.2 of the three-submodules refactor.

import { MODEL_PLAN } from "../../constants.js";
import { saveState } from "../../state.js";
import type { PipelineContext, StageResult, StateJson } from "../../types.js";
import {
  artifactPaths,
  cleanupRenderedTemplate,
  readIfExists,
  readPrompt,
  type StageDeps,
} from "../../pipeline_support.js";
import { normalizeReviewerTier, tierFloorBlock, type NoveltyTarget } from "../../novelty.js";
import {
  runStageNeg1_2,
  logNeg1Review,
  NEG1_NONFLAGSHIP_KILL_VERSION,
  NEG1_PIVOT_BUDGET,
  NEG1_REVISE_CAP,
  NEG1_ENV_FAILURE_RETRY_BUDGET,
} from "./neg1_2.js";
import { protoCoreJsonPath } from "./neg1_2_author.js";
import {
  collectFlagCodes,
  decideRejectEscape,
  decideReviseOutcome,
  decideTierSaturationPromote,
  normalizeReviewVerdict,
} from "./neg0_5_decision.js";
import { renderRefereeTemplate, runReferee } from "../framework/referee.js";
import { parseRepairedModelJson } from "../core/core_io.js";

/**
 * Single-artifact review block for the D-0.5 reviewer.
 *
 * The reviewer judges ONE artifact: the typed proto_core (the authoritative
 * formal content and prose), inlined canonically. Its absence is a plumbing
 * failure (throws), never a review verdict.
 */
export async function buildProtoCoreReviewBlock(ctx: PipelineContext): Promise<string> {
  const src = await readIfExists(protoCoreJsonPath(ctx));
  if (!src) {
    // Single-artifact regime: the proto core IS the proposal, and the producer
    // either writes it or halts before the review boundary. Its absence here is
    // a plumbing failure, never a review verdict, and there is no .tex fallback.
    throw new Error(
      `D-0.5 cannot review: proto_core.json is absent or empty at ${protoCoreJsonPath(ctx)}. ` +
        `Re-run the D-1.2 producer before the review boundary.`,
    );
  }
  // Validate AND canonicalize before inlining. The proto core is written by the
  // AGENT (no atomic wrapper), and the resume guard only checks `existsSync` while
  // this function only checked non-empty — so a torn file was inlined verbatim and
  // a full reviewer dispatch was paid to review garbage, with the real failure
  // surfacing much later in D0-SOLVE. Reading through the three-layer escape
  // defense additionally rescues an under-escaped agent-raw core (`\alpha`) and a
  // legacy `\texttt`→tab corruption instead of inlining it for the reviewer.
  let canonical: string;
  try {
    canonical = JSON.stringify(parseRepairedModelJson(src, protoCoreJsonPath(ctx)), null, 2);
  } catch (err) {
    throw new Error(
      `D-0.5 cannot review: proto_core.json at ${protoCoreJsonPath(ctx)} is not valid JSON ` +
        `(${err instanceof Error ? err.message : String(err)}). This is a torn/partial producer write ` +
        `or unrecoverable escape corruption, NOT a review verdict — re-run the D-1.2 producer before ` +
        `the review boundary.`,
    );
  }
  // No adapter: the single-artifact rubric (stage_neg1_review_core.txt) is itself
  // retargeted at the typed core, so we only need to inline the core.
  return ["=== PROPOSAL CORE (the artifact under review — typed source of truth) ===", canonical, "=== END PROPOSAL CORE ==="].join("\n");
}


/**
 * Inspect a Stage -0.5 reviewer JSON and, when REJECTed for a localized
 * failure mode this angle hasn't yet rescued from, mutate `pf` to dispatch
 * the producer in the appropriate escape mode (kernel-replace > draft-rebuild),
 * record the angle in the corresponding used-angles array, and invoke
 * `runStageNeg1_2`. Returns true iff an escape was dispatched (caller should
 * `continue` the loop). Returns false when no escape applies, the angle has
 * already used the relevant escape, or the flag pattern doesn't match — in
 * which case the caller falls through to the pivot path.
 */
async function dispatchRejectEscape(args: {
  angle: number;
  reviewJson: Record<string, unknown>;
  pf: NonNullable<StateJson["proposed_from"]>;
  iterations: NonNullable<NonNullable<StateJson["proposed_from"]>["iterations"]>;
  ctx: PipelineContext;
  deps: StageDeps;
  state: StateJson;
  persistState: () => Promise<void>;
}): Promise<boolean> {
  const kernelUsed = args.pf.kernel_replace_used_angles ?? [];
  const draftUsed = args.pf.draft_rebuild_used_angles ?? [];
  const escapeMode = decideRejectEscape({
    codes: collectFlagCodes(args.reviewJson),
    angle: args.angle,
    kernelReplaceUsedAngles: kernelUsed,
    draftRebuildUsedAngles: draftUsed,
  });
  if (!escapeMode) return false;
  if (escapeMode === "kernel-replace") args.pf.kernel_replace_used_angles = [...kernelUsed, args.angle];
  else args.pf.draft_rebuild_used_angles = [...draftUsed, args.angle];

  args.pf.current_mode = escapeMode;
  // Keep current_version as-is; the producer increments it on entry. The
  // angle's iteration history is preserved so the producer's revise-style
  // head prompt can read the prior REJECT verdict.
  args.pf.iterations = args.iterations;
  await args.persistState();
  await runStageNeg1_2({ ctx: args.ctx, state: args.state, deps: args.deps });
  await args.persistState();
  return true;
}

/**
 * Stage -0.5 reviewer: review the current proto core and own the
 * angle / revise / pivot loop. On REVISE / REJECT / cap-exhausted, calls the
 * Stage -1.2 producer as a callback to draft the next version. Exits with
 * ACCEPT (advance forward) or NO-PASS (checkpoint).
 */
export async function runStageNeg0_5(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
}): Promise<StageResult> {
  // Stage -0.5 runs whenever the state carries a `proposed_from` record,
  // regardless of whether --propose was passed on this invocation. This makes
  // resumes after a programmatic rewind (e.g. Stage 0.5 boundary routing back
  // to "-1.2") correctly re-enter the proposal-review loop instead of skipping
  // ahead to Stage 0. Cold-start without --propose still skips: in that case
  // no proposed_from has been written by Stage -1.2 and we have nothing to review.
  if (!args.ctx.proposeTopic && !args.state.proposed_from) {
    return { stage: "-0.5", status: "skipped", message: "proposal review skipped" };
  }
  const pf = args.state.proposed_from;
  if (!pf) {
    return {
      stage: "-0.5",
      status: "blocked",
      advance: false,
      message: "Stage -0.5 has no proposed_from; run Stage -1.2 producer first",
    };
  }
  const paths = artifactPaths(args.ctx, args.state);
  const currentProposalArtifact = (): string => protoCoreJsonPath(args.ctx);
  // The flagship rubric (regime axes (a)–(j), soft tier-movers, hard caps) is
  // the proposal reviewer's standard, kept as its own block so the review
  // prompt holds only the stage-specific routing.
  // Single-artifact regime: the self-contained core reviewer rubric, always,
  // resolved once per loop; the producer either writes the core or halts pre-review.
  const reviewPromptOnce = (async () => {
    const [neg1ReviewBody, flagshipRubric] = await Promise.all([
      readPrompt(args.ctx, "stage_neg1_review_core.txt"),
      readPrompt(args.ctx, "stage_flagship_rubric.txt"),
    ]);
    return `${neg1ReviewBody}\n\n${flagshipRubric}`;
  })();
  const resolveReviewPrompt = (): Promise<string> => reviewPromptOnce;

  const iterations = pf.iterations ?? [];
  // The run's ambition floor. Both the tier-saturation auto-promote and the
  // early angle-kill below gate on "reached this floor tier" rather than the
  // literal "flagship", so a nonflagship target gets the full revise runway
  // and can converge to ACCEPT via clean revises. Default mirrors the
  // proposal-stage default novelty target (`field`).
  const noveltyTarget = pf.novelty_target ?? "field";

  const persistState = (): Promise<void> =>
    saveState(args.ctx.repoRoot, args.ctx.qid, args.ctx.specialization, args.state);

  const reviseCapForAngle = (angle: number): number =>
    pf.revision_cap_by_angle?.[String(angle)] ?? NEG1_REVISE_CAP;

  const checkpointAngle = async (checkpoint: NonNullable<typeof pf.angle_checkpoint>): Promise<StageResult> => {
    pf.angle_checkpoint = checkpoint;
    pf.iterations = iterations;
    await persistState();
    const actions = checkpoint.kind === "revise"
      ? "continue"
      : "switch | retry --extra-revisions N | give-up";
    return {
      stage: "-0.5",
      status: "checkpoint",
      advance: false,
      message:
        `D-0.5 ${checkpoint.kind} checkpoint on angle ${checkpoint.angle} v${checkpoint.version}: ` +
        `${checkpoint.reason}. Resolve atomically with ` +
        `\`causalsmith research --angle-action ${actions} <qid> <spec> ` +
        `[--angle-directive <text|->] --auto\`. No next proposer has started.`,
    };
  };

  // Counts environment-failure retries across the whole loop. An env failure
  // (codex sandbox could not start) is not a statement about the angle, so it
  // must NOT pivot; we retry the same draft up to the budget, then abort.
  // CARRIED across resumes. This was a process-local counter, so the abort below left
  // `last_draft_status === "env-failure"` in state, every resume re-entered the branch with
  // the counter at 0, and re-dispatched the producer a full budget of times — unbounded and
  // unaudited, with no cap gate.
  let envFailureRetries = args.state.flags.neg1_env_failure_retries ?? 0;

  while ((pf.current_angle_index ?? 0) < NEG1_PIVOT_BUDGET) {
    const angle = pf.current_angle_index ?? 0;
    const version = pf.current_version ?? 1;
    const mode = pf.current_mode ?? "cold-start";

    // Environment failure (sandbox/FS could not start) — distinct from a
    // mathematical judgment about the angle. Do NOT burn the angle: retry the
    // SAME draft a bounded number of times, then abort WITHOUT pivot so the
    // angle is preserved for `--resume` once the sandbox is repaired. (Observed:
    // angle 0 REVISE@field abandoned to a spurious pivot on a single
    // `spawn setup refresh`.)
    if (pf.last_draft_status === "env-failure") {
      envFailureRetries += 1;
      args.state.flags.neg1_env_failure_retries = envFailureRetries;
      if (envFailureRetries > NEG1_ENV_FAILURE_RETRY_BUDGET) {
        iterations.push({ angle, version, mode, verdict: "env-failure-abort" });
        pf.iterations = iterations;
        // Raise the cap gate, or the abort is UNRECOVERABLE by the resume it prescribes:
        // the over-budget counter persists with `last_draft_status` still "env-failure",
        // so a plain `--resume` re-enters this branch, increments again and re-aborts
        // forever — a healthy angle permanently presents as dead. `stage_neg1_fallback`
        // is the designed escape: its CapGate.clear resets `neg1_env_failure_retries`.
        args.state.flags.stage_neg1_fallback =
          `D-0.5 producer environment failure (sandbox could not start) ${envFailureRetries}× on angle ${angle}`;
        await persistState();
        return {
          stage: "-0.5",
          status: "blocked",
          advance: false,
          message:
            `Stage -1.2 producer hit a non-recoverable environment failure ` +
            `(codex sandbox could not start — e.g. 'spawn setup refresh') ` +
            `${envFailureRetries}× on angle ${angle} v${version} (${mode}). ` +
            `Aborting WITHOUT pivot so the angle is preserved. Repair the codex ` +
            `write sandbox (apply_patch), then resume with ` +
            `\`--clear-gate stage_neg1_fallback\` to retry this draft (a plain ` +
            `--resume cannot clear the exhausted retry counter).`,
        };
      }
      // eslint-disable-next-line no-console
      console.warn(
        `[stage -0.5] env-failure on angle ${angle} v${version} (${mode}); ` +
          `retry ${envFailureRetries}/${NEG1_ENV_FAILURE_RETRY_BUDGET} (NOT pivoting).`,
      );
      // Re-attempt the same mode/angle. runStageNeg1_2 re-dispatches the
      // producer; on success last_draft_status flips to "completed" and the
      // loop proceeds to review.
      await runStageNeg1_2({ ctx: args.ctx, state: args.state, deps: args.deps });
      await persistState();
      continue;
    }

    // Producer-side failure (invalid-draft / needs-pivot) → angle is dead.
    if (pf.last_draft_status && pf.last_draft_status !== "completed") {
      iterations.push({ angle, version, mode, verdict: pf.last_draft_status });
      pf.iterations = iterations;
      await persistState();
      return checkpointAngle({
        kind: "angle-boundary",
        angle,
        version,
        verdict: pf.last_draft_status,
        reason: `producer returned ${pf.last_draft_status}`,
        revise_cap: reviseCapForAngle(angle),
        ...(angle < NEG1_PIVOT_BUDGET - 1 ? { next_angle: angle + 1 } : {}),
      });
    }

    // Resume-aware producer-first guard. If we are entering -0.5 in
    // revise/pivot mode with no fresh draft version, drive the producer once
    // before reviewing — otherwise we would either (a) burn a Codex call
    // re-reviewing the already-judged proposal, or (b) push an iteration row
    // with version=0 (an angle switch wipes last_reviewer_verdict and resets
    // current_version=0, expecting stageNeg1_2 to bump it before the next review).
    const hasFreshDraft = pf.last_draft_version === (pf.current_version ?? 0);
    if (!hasFreshDraft && (mode === "revise" || mode === "pivot")) {
      await runStageNeg1_2({ ctx: args.ctx, state: args.state, deps: args.deps });
      // The next operation is another remote reviewer call. Persist the newly
      // authored version marker first so a reviewer crash resumes from review
      // instead of silently re-running and overwriting the proposer output.
      await persistState();
      continue;
    }

    // SINGLE SOURCE for drafter context: the RAW proto core. The persisted core
    // already carries everything the drafter handoff shows — the checklist,
    // comparator table, and UM8 upgrade metadata via CoreSchema/CORE_HANDOFF_KEYS.
    // Stdout is only a disposition receipt. The state stores only a compact freshness version,
    // never a second serialized copy of the author output.
    let draftJson: Record<string, unknown> = {};
    const rawCoreForHandoff = await readIfExists(protoCoreJsonPath(args.ctx));
    if (rawCoreForHandoff) {
      try {
        draftJson = parseRepairedModelJson(
          rawCoreForHandoff,
          protoCoreJsonPath(args.ctx),
        ) as Record<string, unknown>;
      } catch {
        // buildProtoCoreReviewBlock throws the loud, actionable error for a torn
        // core moments later; an empty drafter context here is fine meanwhile.
        draftJson = {};
      }
    }
    // Resolve this per attempt: a proto core can first appear during the loop.
    // In single-artifact mode every reviewer-facing path must name the core,
    // never a possibly stale legacy proposal.tex.
    const proposalReviewPath = currentProposalArtifact();
    await renderNeg1ReviewOutputTemplate({
      ctx: args.ctx,
      targetPath: paths.proposalReviewOutputJson,
      proposalPath: proposalReviewPath,
    });
    const reviewOut = await runNeg1Review({
      ctx: args.ctx,
      deps: args.deps,
      promptText: await resolveReviewPrompt(),
      proposalPath: proposalReviewPath,
      reviewOutputJsonPath: paths.proposalReviewOutputJson,
      draftJson,
      noveltyTarget: pf.novelty_target,
    });
    // A reviewer whose output could not be parsed has NOT reviewed anything. Halt on
    // it rather than letting the `?? "REVISE"` default below burn a revise round (cap
    // 5) plus a full producer re-author on a parsing artifact.
    if (reviewOut.parseError !== null) {
      await persistState();
      return {
        stage: "-0.5",
        status: "checkpoint",
        advance: false,
        message:
          `Stage -0.5 reviewer output was UNPARSEABLE on angle ${pf.current_angle_index ?? 0} ` +
          `v${pf.current_version ?? 0} (parseError=${reviewOut.parseError}). This is a PLUMBING fault, not a ` +
          `review verdict — no revise round was consumed and the proposal is untouched. Inspect the reviewer ` +
          `transcript in logs/stages/, then --resume to re-run the same review.`,
      };
    }
    pf.last_reviewer_verdict = reviewOut.raw;
    // Reviewer returned successfully — its rendered output template is now dead
    // scratch (the verdict lives in reviewOut.raw / reviews.jsonl). Drop it;
    // it is re-rendered on the next revise/pivot iteration.
    await cleanupRenderedTemplate(paths.proposalReviewOutputJson);
    // Same fail-loud contract as the parse-error checkpoint above, one layer deeper:
    // parseable JSON whose `verdict` is missing or junk is a SHAPE fault, not a review.
    // The old `?? "REVISE"` default burned a revise round + producer re-author on it.
    const normalizedVerdict = normalizeReviewVerdict(reviewOut.verdict);
    if (normalizedVerdict === null) {
      await persistState();
      return {
        stage: "-0.5",
        status: "checkpoint",
        advance: false,
        message:
          `Stage -0.5 reviewer JSON parsed but carried no usable verdict on angle ${pf.current_angle_index ?? 0} ` +
          `v${pf.current_version ?? 0} (verdict=${JSON.stringify(reviewOut.verdict)}; expected ACCEPT/REJECT/REVISE). ` +
          `This is a PLUMBING fault, not a review verdict — no revise round was consumed and the proposal is ` +
          `untouched. Inspect the reviewer transcript in logs/stages/, then --resume to re-run the same review.`,
      };
    }
    let verdict: string = normalizedVerdict;
    // Tier-saturation extras: tier_at_proposal + a boolean "clean_substance"
    // = no N-* flags AND no C-* flags (structure flags are OK). These feed
    // the auto-promote rule below; harmless when absent.
    const reviewJson = reviewOut.json as Record<string, unknown>;
    const tierStr =
      typeof reviewJson.publishability_tier === "string"
        ? normalizeReviewerTier(reviewJson.publishability_tier)
        : undefined;
    const novelArr = Array.isArray(reviewJson.novelty_flags) ? reviewJson.novelty_flags : [];
    const soundArr = Array.isArray(reviewJson.soundness_flags) ? reviewJson.soundness_flags : [];
    const cleanSubstance = novelArr.length === 0 && soundArr.length === 0;
    iterations.push({ angle, version, mode, verdict, tier: tierStr, clean_substance: cleanSubstance });

    // Stage -0.5 tier-saturation auto-promote (safe here because Stage -0.5
    // never verifies proofs — Conjectures are intentionally open and math
    // correctness is checked downstream at Stage 0.5). If the last 3
    // consecutive REVISEs on the CURRENT angle held at-or-above the run's
    // novelty floor tier with empty N-* and C-* flag arrays (only S-* /
    // prose-level flags left), promote to ACCEPT. Prevents the cap-bound trap
    // observed in Runs 4, 5, 7 where well-posedness nits dominate at the cap.
    // Gated on the run's floor (not the literal "flagship") so nonflagship
    // targets can converge to ACCEPT the same way.
    // NOT replicated at Stage 0.5 — there C-wellposed flags can be
    // load-bearing and must escalate to a user checkpoint instead.
    if (
      decideTierSaturationPromote({
        verdict,
        tier: tierStr,
        cleanSubstance,
        iterations,
        angle,
        noveltyTarget,
      })
    ) {
      verdict = "ACCEPT";
      // Patch the last iteration entry to record the auto-promote reason.
      iterations[iterations.length - 1] = {
        ...iterations[iterations.length - 1],
        verdict,
      };
      pf.last_reviewer_verdict =
        (pf.last_reviewer_verdict ?? "") +
        `\n[orchestrator note] Stage -0.5 tier-saturation auto-promote: 3 consecutive REVISE at-or-above the ${noveltyTarget} novelty floor with empty N-* and C-* flags; auto-set ACCEPT.`;
    }

    await logNeg1Review({
      ctx: args.ctx,
      angle,
      version,
      verdict,
      json: reviewOut.json,
    });
    pf.iterations = iterations;
    await persistState();

    if (verdict === "ACCEPT") {
      pf.iterations = iterations;
      pf.final_verdict = "ACCEPT";
      // Resolved at accept time: the accepted proposal is the proto core on disk now.
      pf.proposal_path = currentProposalArtifact();
      await persistState();
      return {
        stage: "-0.5",
        status: "completed",
        message: `Stage -0.5 ACCEPT on angle ${angle} v${version}`,
      };
    }

    if (verdict === "REJECT") {
      // REJECT-escape dispatcher (May 2026). Before pivoting to a new angle,
      // give the producer a single rescue attempt on the current angle when the
      // reviewer's flag pattern points at a localized failure mode:
      //   - kernel-replace: kernel claim is structurally a definitional unfold
      //     / unbounded epsilon / unnamed focal object; swap the kernel but
      //     keep the angle's seeds + literature anchor.
      //   - draft-rebuild: kernel is OK but the draft execution is broken
      //     (witness self-refuting, exhibit unhydrated, arithmetic wrong);
      //     rewrite the draft on top of the same kernel.
      // Each escape fires at most once per angle. Kernel-replace takes priority
      // over draft-rebuild when both flag patterns are present. If the angle
      // already burned the relevant escape, fall through to the pivot below.
      const escapeDispatched = await dispatchRejectEscape({
        angle,
        reviewJson: reviewOut.json as Record<string, unknown>,
        pf,
        iterations,
        ctx: args.ctx,
        deps: args.deps,
        state: args.state,
        persistState,
      });
      if (escapeDispatched) continue;
      return checkpointAngle({
        kind: "angle-boundary",
        angle,
        version,
        verdict,
        reason: "reviewer REJECT after same-angle rescue paths were unavailable or exhausted",
        revise_cap: reviseCapForAngle(angle),
        ...(angle < NEG1_PIVOT_BUDGET - 1 ? { next_angle: angle + 1 } : {}),
      });
    }

    // REVISE — tier-gated early-stop vs cap vs another round; see
    // decideReviseOutcome for the rationale (below-floor kill preserves the
    // full revise runway for angles whose problem is substance, not ceiling).
    const reviseCap = reviseCapForAngle(angle);
    const reviseOutcome = decideReviseOutcome({
      version,
      iterations,
      angle,
      noveltyTarget,
      reviseCap,
      killVersion: NEG1_NONFLAGSHIP_KILL_VERSION,
    });
    if (reviseOutcome !== "revise") {
      iterations.push({ angle, version, mode: "revise", verdict: reviseOutcome });
      pf.iterations = iterations;
      await persistState();
      return checkpointAngle({
        kind: "angle-boundary",
        angle,
        version,
        verdict: reviseOutcome,
        reason:
          reviseOutcome === "below-floor-kill"
            ? `angle never reached the ${noveltyTarget} novelty floor by v${version}`
            : `revision cap ${reviseCap} exhausted after reviewer REVISE`,
        revise_cap: reviseCap,
        ...(angle < NEG1_PIVOT_BUDGET - 1 ? { next_angle: angle + 1 } : {}),
      });
    }
    pf.current_mode = "revise";
    pf.iterations = iterations;
    return checkpointAngle({
      kind: "revise",
      angle,
      version,
      verdict,
      reason: "reviewer requested revision; D-orchestrator may inject a directive before continuing",
      revise_cap: reviseCap,
    });
  }

  // Every angle the cursor can hold is below the budget: `--angle-action switch` and the
  // cursor reset both refuse an angle at or past it.
  throw new Error(
    `D-0.5: proposal cursor angle ${pf.current_angle_index} is outside the pivot budget ${NEG1_PIVOT_BUDGET}`,
  );
}

/**
 * Render the Stage -0.5 reviewer's stdout-JSON template into the qid folder.
 * Pre-fills `proposal_path_read` with the one artifact the reviewer will read
 * (typed core in single-artifact mode, `.tex` in legacy mode) and lets the agent
 * fill the verdict and finding slots. Re-rendered on
 * every invocation so a fresh template is always next to the proposal.
 */
async function renderNeg1ReviewOutputTemplate(args: {
  ctx: PipelineContext;
  targetPath: string;
  proposalPath: string;
}): Promise<void> {
  await renderRefereeTemplate({
    ctx: args.ctx,
    templateName: "stage_neg1_review_output_template.json",
    targetPath: args.targetPath,
    prefill: (tmpl) => {
      tmpl.proposal_path_read = args.proposalPath;
    },
  });
}

const SOURCE_RECEIPT_REQUIRED_CODES = new Set([
  "N-mischar",
  "N-pub",
  "C-assumption-nonstandard",
]);

/** Fail closed when a source-dependent adverse finding has no inspectable
 * primary-source receipt. A review that cannot show its source must not burn a
 * proposal revision or trigger a mathematical rewrite. */
export function sourceReceiptValidationError(json: Record<string, unknown>): string | null {
  const required = new Set<string>();
  for (const key of ["novelty_flags", "soundness_flags"] as const) {
    const flags = Array.isArray(json[key]) ? json[key] : [];
    for (const flag of flags) {
      if (!flag || typeof flag !== "object") continue;
      const code = (flag as { code?: unknown }).code;
      if (typeof code === "string" && SOURCE_RECEIPT_REQUIRED_CODES.has(code)) required.add(code);
    }
  }
  if (required.size === 0) return null;

  const covered = new Set<string>();
  const receipts = Array.isArray(json.source_verification_receipts)
    ? json.source_verification_receipts
    : [];
  for (const receipt of receipts) {
    if (!receipt || typeof receipt !== "object") continue;
    const row = receipt as Record<string, unknown>;
    const wellFormed =
      typeof row.bibkey === "string" && row.bibkey.trim().length > 0 &&
      typeof row.source_url === "string" && /^https?:\/\//.test(row.source_url) &&
      typeof row.version === "string" && row.version.trim().length > 0 &&
      typeof row.locator === "string" && row.locator.trim().length > 0 &&
      typeof row.verified_claim === "string" && row.verified_claim.trim().length > 0;
    if (!wellFormed || !Array.isArray(row.supports_flag_codes)) continue;
    for (const code of row.supports_flag_codes) {
      if (typeof code === "string") covered.add(code);
    }
  }
  const missing = [...required].filter((code) => !covered.has(code));
  return missing.length > 0
    ? `source-dependent reviewer flag(s) lack a complete primary-source receipt: ${missing.join(", ")}`
    : null;
}

export async function runNeg1Review(args: {
  ctx: PipelineContext;
  deps: StageDeps;
  promptText: string;
  proposalPath: string;
  reviewOutputJsonPath: string;
  draftJson: Record<string, unknown>;
  noveltyTarget: NoveltyTarget;
}): Promise<{ raw: string; verdict: string | null; json: Record<string, unknown>; parseError: string | null }> {
  // (Fail-closed on the proposal source lives in `buildProtoCoreReviewBlock`
  // below: absent/empty/torn proto core throws a plumbing error there, never a
  // review verdict — the class of fault that fabricated a novelty tier at
  // D0.5.G.)
  // (The comparator backfill is retired: `draftJson` IS the raw proto core,
  // which carries `comparator_promise_table` and the checklist directly — there is
  // no second copy left to reconcile.)
  const upgradeMode = args.draftJson.upgrade_mode === true;
  const upgradeDirective = upgradeMode
    ? await readPrompt(args.ctx, "stage_neg1_review_upgrade_directive.txt")
    : "";
  const parts: string[] = [args.promptText, ""];
  if (upgradeDirective) {
    parts.push(upgradeDirective, "");
  }
  // Single-artifact: inline the authoritative typed core (throws loud on an
  // absent/torn core — a plumbing failure, never a review verdict).
  const protoCoreBlock = await buildProtoCoreReviewBlock(args.ctx);
  parts.push(protoCoreBlock, "");
  parts.push(
    "=== ORCHESTRATOR-PROVIDED INPUTS ===",
    `proposal_path: ${args.proposalPath}`,
    `Output JSON template (READ THIS, fill TODOs, emit on stdout): ${args.reviewOutputJsonPath}`,
    `novelty_target: ${args.noveltyTarget}`,
    "Return ONLY the JSON object obtained by filling the output template.",
    "",
    tierFloorBlock(args.noveltyTarget),
  );
  const prompt = parts.join("\n");
  // Referee harness: dispatch + parse + scaffolding-strip + verdict extraction.
  // A parse failure surfaces as parseError and must never masquerade as a
  // review verdict (the caller's `?? "REVISE"` default would otherwise turn it
  // into a PHANTOM REVISE consuming one of only five revise rounds). The
  // source-receipt validation runs as the harness's validate hook.
  const result = await runReferee({
    ctx: args.ctx,
    deps: args.deps,
    stage: "-0.5",
    label: "D-0.5 proposal review",
    prompt,
    promptSources: [
      "stage_neg1_review(_core).txt + stage_flagship_rubric.txt",
      args.proposalPath,
    ],
    model: MODEL_PLAN.stageNeg0_5_review.model,
    reasoningEffort: MODEL_PLAN.stageNeg0_5_review.effort,
    inactivityTimeoutMs: 40 * 60 * 1000,
    validate: sourceReceiptValidationError,
  });
  return { raw: result.raw, verdict: result.verdict, json: result.json, parseError: result.parseError };
}


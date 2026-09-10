// Typed-core D0 phase wiring (the only D0 path).
//
// D-1.2 emits a `proto_core.json` and D0 runs the typed path:
//   stage "0"   → runStage0Typed   = D0-SOLVE then D0-RENDER
//   stage "0.5" → runStage0_5Typed = typed D0.5 review ↔ directed D0.R revise loop
// Maps each to a StageResult the pipeline loop understands. A D0-SOLVE proposed
// statement change, or a D0.5 `fail` / revise-cap exhaustion, surfaces as a
// checkpoint (advance:false) — the human/orchestrator resolves it.
import { existsSync } from "node:fs";
import { createHash } from "node:crypto";
import { readFile, rm } from "node:fs/promises";
import path from "node:path";
import type { PipelineContext, StageResult, StateJson } from "../../types.js";
import { appendReview, artifactPaths, type StageDeps } from "../../pipeline_support.js";
import { runStage0Render } from "./d0_render.js";
import { runStage0_5Core } from "./d0_5_core.js";
import type { Stage0_5CoreResult } from "./d0_5_core.js";
import {
  runGeneralReview,
  buildGeneralTierVerdict,
  decideGeneralReroute,
  decideTriageKill,
  GENERAL_REROUTE_CAP,
  formatTriageTier,
  tierRank,
  TARGET_FLOOR_LABEL,
  type GeneralReviewResult,
} from "./d0_5_general.js";
import { proposalFindingRoute, runStage0RCore } from "./d0_r_core.js";
import { coreJsonPath } from "./d0_core.js";
import { d05AcceptanceReceiptPath, writeD05AcceptanceReceipt } from "./d0_acceptance.js";
import { saveState } from "../../state.js";
import { appendEscalationLog, readEscalationLog } from "../escalation_log.js";
import { readTypedCore } from "../core/core_io.js";
import { writeTextAtomic } from "../../shared/json_atomic.js";
import { resolveInDir } from "../../paths.js";
import {
  loadSemanticManifest,
  validateCoreManifest,
  validateRenderedManifest,
} from "../semantic_manifest.js";
import { runVcsSolveRound, ensureStore } from "../vcs/round.js";
import { commitGraph, headGraph, publishCore } from "../vcs/commit.js";
import { graphFromCore } from "../vcs/render.js";
import { blobId } from "../vcs/node.js";
import { orphanLemmas, danglingCitations } from "../vcs/hygiene.js";
import { formatViolations } from "../vcs/checks.js";
import { loadGraph } from "../vcs/graph.js";
import {
  consumePendingIncrementalRewind,
  finalizePendingExtensionRebase,
} from "./d0_cross_boundary_rewind.js";

export function citationVerificationCheckpoint(review: Stage0_5CoreResult): StageResult | null {
  if (review.citation_verification_required.length === 0) return null;
  return {
    stage: "0.5",
    status: "checkpoint",
    advance: false,
    message:
      "CITATION VERIFICATION REQUIRED — D0.5 could not retrieve the source of record for: " +
      review.citation_verification_required.map((c) => c.node_id).join(", ") +
      ". This is not revise/fail. Main must try a lawful source (arXiv/author copy/repository); " +
      "if unavailable, ask the user for the cited page or exact theorem statement, persist it as " +
      "source.verbatim_statement with provenance, then rerun D0.5. Agent memory is not verification.",
  };
}

/** Max directed D0.R revise rounds before the typed D0.5 loop checkpoints.
 *  Default 3: D0.R now OWNS the dependency graph / wiring (add/drop `depends_on` edges,
 *  re-route lemmas, faithful def-alignment) and fixes those in place durably — a passed
 *  D0.5 advances with no re-solve (see stage0_R_core prompt). So the common trailing
 *  D0.5-referee class (redundant/hidden dependency, redundant-assumption-declaration) is
 *  genuinely in-place-fixable, and the extra round closes the graph-hygiene tail instead
 *  of escalating. STATEMENT/CONCLUSION findings (overclaim / ill-typed target / narrow-a-
 *  premise) stay OUT of D0.R scope — it escalates those to the orchestrator (a proto edit),
 *  so they do not thrash the revise budget. The no-net-progress / persistent-finding
 *  backstops still escalate immediately when a round makes no headway (see the loop in
 *  runStage0_5Typed). Override via `CAUSALSMITH_D0_REVISE_CAP`. */
export const D0_REVISE_CAP = (() => {
  const v = parseInt(process.env.CAUSALSMITH_D0_REVISE_CAP ?? "", 10);
  return Number.isFinite(v) && v > 0 ? v : 3;
})();

export { GENERAL_REROUTE_CAP } from "./d0_5_general.js";

/** Persist the exact review payload before returning any D0.5 checkpoint that
 * routes back to D0. The content hash makes retries idempotent, and typed target
 * ids keep the next D0 solve off unrelated valid nodes. */
async function injectD0ReviewDirective(args: {
  ctx: PipelineContext;
  state: StateJson;
  reason: string;
  payload: unknown;
  targetIds?: string[];
  /** Record the verdict WITHOUT making it a re-solve directive. See
   *  `EscalationLogEntry.provenance_only` — an untargeted directive force-opens the whole
   *  paper, so bookkeeping entries must opt out explicitly. */
  provenanceOnly?: boolean;
}): Promise<string> {
  // Fingerprint the WHOLE dispatch, not just the payload.
  //
  // Hashing `payload` alone made the dedup actively harmful. The `fail`,
  // persistent-finding, no-net-progress and cap-exhausted call sites all pass the
  // identical payload shape {stage, overall, verdicts}, so the second to fire was
  // suppressed along with its materially different `reason`. Worse, a verdict that
  // is byte-identical across rounds IS the persistent-finding case — the strongest
  // signal in the system ("this survived a full re-derivation") was the one most
  // certain to be dropped. Including reason, targets and round keeps genuine
  // re-delivery while still collapsing a true duplicate append.
  const round = d0Counters(args.state).solve_rounds;
  const encoded = JSON.stringify({
    payload: args.payload,
    reason: args.reason,
    targets: [...(args.targetIds ?? [])].sort(),
    round,
  });
  const fingerprint = createHash("sha256").update(encoded).digest("hex").slice(0, 16);
  const marker = `[D0.5 REVIEW ${fingerprint}]`;
  const prior = await readEscalationLog(args.ctx);
  if (prior.some((entry) => entry.directive?.includes(marker))) return marker;

  const core = await readTypedCore(coreJsonPath(args.ctx));
  const targets = partitionReviewTargets([...(args.targetIds ?? [])], core);
  const requiredCoreTargets = targets.required;
  await appendEscalationLog(args.ctx, {
    round,
    directive: [
      `${marker} ${args.reason}`,
      "The following is the complete current reviewer payload. Treat every finding as directed D0 input;",
      "repair the same paper and do not substitute a different target.",
      // Targets D0 cannot bind to an exact-emission check are named explicitly rather
      // than dropped: a finding on a def:/ass: node is still directed input, and the
      // orchestrator must be able to see that it was raised but is unenforced.
      ...(targets.nonStatement.length > 0
        ? [
            `UNENFORCED TARGETS (non-statement core nodes — repair these too; D0's exact-target check ` +
              `cannot bind them): ${targets.nonStatement.join(", ")}`,
          ]
        : []),
      ...(targets.unknown.length > 0
        ? [
            `UNRESOLVED TARGETS (named by a referee but present in no core store — treat as a reviewer ` +
              `id error, do NOT invent these nodes): ${targets.unknown.join(", ")}`,
          ]
        : []),
      JSON.stringify(args.payload, null, 2),
    ].join("\n"),
    ...(requiredCoreTargets.length > 0 ? { required_core_targets: requiredCoreTargets } : {}),
    ...(args.provenanceOnly === true ? { provenance_only: true } : {}),
  });
  return marker;
}

function reviewTargetIds(review: Stage0_5CoreResult): string[] {
  return review.verdicts.flatMap((verdict) =>
    verdict.findings.flatMap((finding) => finding.node_id ? [finding.node_id] : []),
  );
}

/** Max incomplete proof-carry rounds in D0 before checkpointing. Proposed changes halt immediately. */
export const D0_SOLVE_CAP = (() => {
  const v = parseInt(process.env.CAUSALSMITH_D0_SOLVE_CAP ?? "", 10);
  return Number.isFinite(v) && v > 0 ? v : 15;
})();

async function renderAndComplete(args: { ctx: PipelineContext; state: StateJson; message: string }): Promise<StageResult> {
  const store = await ensureStore(args.ctx, args.state);
  let { head, graph } = await headGraph(store);
  // Orphan-lemma prune (safe ONLY here, on the clean discharge): a lemma no non-lemma
  // claim reaches is an abandoned proof route's helper. Deleted by a pipeline commit —
  // reversible, journaled, and visible in `d0_vc log`.
  let pruneNote = "";
  const orphans = orphanLemmas(graph);
  if (orphans.length > 0) {
    const nodes = new Map(graph.nodes);
    const tree = { ...graph.tree };
    for (const id of orphans) { nodes.delete(id); delete tree[id]; }
    const pruned = await commitGraph({
      store, graph: { tree, nodes }, parents: [head], author: "pipeline", kind: "direct",
      message: `prune ${orphans.length} orphan lemma(s): ${orphans.join(", ")}`, expectedHead: head,
    });
    if (pruned.ok) {
      ({ head, graph } = { head: pruned.id, graph: pruned.graph });
      await publishCore(args.ctx, store);
      pruneNote = `\nPruned ${orphans.length} orphan lemma(s) no longer reachable from any result: ${orphans.join(", ")} (commit ${pruned.id.slice(0, 12)}; \`d0_vc reset\` restores them).`;
    } else {
      console.warn(`[D0] orphan-lemma prune refused: ${pruned.violations.map((v) => `${v.code}@${v.where}`).join(", ")}`);
    }
  }

  // CONSISTENCY GATE (deterministic, ~0 cost): a proof that INVOKES a helper the solver
  // never EMITTED reads as "fully proved" yet carries an unproven step. ONE capped,
  // targeted self-heal: delete the citing proofs (a pipeline commit) and direct a
  // re-solve of exactly those nodes; then halt if it recurs.
  const dangling = danglingCitations(graph);
  if (dangling.length > 0) {
    const citers = [...new Set(dangling.map((d) => d.node))];
    const pairs = dangling.map((d) => `${d.node}→${d.ref}`).join(", ");
    const heals = d0Counters(args.state).consistency_heals;
    if (heals < 1) {
      const nodes = new Map(graph.nodes);
      const tree = { ...graph.tree };
      for (const id of citers) {
        const blob = nodes.get(id);
        if (blob?.node_type !== "statement") continue;
        const { proof_tex: _p, proof_basis: _b, ...body } = blob.body;
        const next = { node_type: "statement" as const, body };
        nodes.set(id, next);
        tree[id] = { ...tree[id], blob: blobId(next) };
      }
      const reopened = await commitGraph({
        store, graph: { tree, nodes }, parents: [head], author: "pipeline", kind: "direct",
        message: `consistency gate: reopen ${citers.join(", ")} (dangling citations ${pairs})`, expectedHead: head,
      });
      if (!reopened.ok) throw new Error(`consistency gate could not reopen the citing nodes: ${reopened.violations.map((v) => `${v.code}@${v.where}`).join(", ")}`);
      await publishCore(args.ctx, store);
      await appendEscalationLog(args.ctx, {
        round: d0Counters(args.state).solve_rounds,
        directive:
          `D0 CONSISTENCY GATE (auto-heal). The following proofs CITE ids that are NOT defined ` +
          `members of the core (cite-without-emit): ${dangling.map((d) => `${d.node} -> ${d.ref}`).join("; ")}. ` +
          `Re-prove the citing node(s) [${citers.join(", ")}] and EMIT every cited helper as a defined ` +
          `member (a lemma with its own proof), AND list it in the citing node's depends_on. Do NOT delete ` +
          `the citation to make it parse — supply the missing member. No proof may reference an id absent from the core.`,
        required_core_targets: citers,
        note: "auto-heal: cite-without-emit dangling citations detected at D0 discharge",
      });
      args.state.flags.d0_loop_counters = { ...d0Counters(args.state), consistency_heals: heals + 1 };
      args.state.stage_completed = "-0.5";
      return {
        stage: "0", status: "rewound", advance: false, completedStage: "-0.5",
        message: `D0 CONSISTENCY GATE — ${dangling.length} dangling citation(s) (${pairs}); reopened [${citers.join(", ")}] with an emit-directive, re-solving BEFORE the D0.5 panel.`,
      };
    }
    args.state.flags.d0_loop_cap_hit = "D0 consistency-gate self-heal exhausted";
    return {
      stage: "0", status: "checkpoint", advance: false,
      message:
        `D0 CONSISTENCY GATE — dangling citation(s) persist after auto-heal: ${pairs}. Inject a directive to EMIT the ` +
        `missing member(s), or edit core.json and \`d0_vc commit\`; then resume with --clear-gate d0_loop_cap_hit.`,
    };
  }

  const rendered = await runStage0Render({ ctx: args.ctx, state: args.state });
  // D0 → D0.5 MAXIMALITY CHECKPOINT. `advance` is left default (true) so
  // `stage_completed` becomes "0" and `--resume` proceeds to D0.5.
  return {
    stage: "0",
    status: "checkpoint",
    message:
      `${args.message}; ${rendered.message}.${pruneNote}\nD0 MAXIMALITY CHECKPOINT — the paper is fully proved/discharged (main ${head.slice(0, 12)}). ` +
      `Review whether the WHOLE paper is maximized BEFORE D0.5; iterate D0 if not, else --resume to proceed to the D0.5 review.`,
    artifacts: [coreJsonPath(args.ctx), rendered.texPath],
  };
}

/** Stage "0" (typed): the D0 SOLVE loop on the versioned graph. Each round is a pull
 * request; an additive round merges itself and the loop continues; a round that needs
 * a verdict, isolates an open gap, or exhausts the cap halts for the orchestrator. */
export async function runStage0Typed(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
}): Promise<StageResult> {
  await consumePendingIncrementalRewind({ ctx: args.ctx, state: args.state });
  await finalizePendingExtensionRebase({ ctx: args.ctx, state: args.state });
  // A D0 round after an interrupted D0.5 means the orchestrator moved on: D0.R's
  // commits are part of history now, not a pending rollback.
  delete args.state.flags.d0_5_head_before;
  const solveStart = d0Counters(args.state).solve_rounds;
  for (let round = solveStart; round < D0_SOLVE_CAP; round++) {
    args.state.flags.d0_loop_counters = { ...d0Counters(args.state), solve_rounds: round + 1 };
    // Persist the increment BEFORE dispatch so a thrown round still costs budget.
    await saveState(args.ctx.repoRoot, args.ctx.qid, args.ctx.specialization, args.state);
    const outcome = await runVcsSolveRound({ ctx: args.ctx, state: args.state, deps: args.deps, round: round + 1 });
    await saveState(args.ctx.repoRoot, args.ctx.qid, args.ctx.specialization, args.state);
    switch (outcome.kind) {
      case "clean":
        return renderAndComplete({ ctx: args.ctx, state: args.state, message: outcome.message });
      case "incomplete":
        if (round + 1 < D0_SOLVE_CAP) continue;
        return { stage: "0", status: "checkpoint", advance: false, message: `${outcome.message}\n(cap reached on an incomplete round)` };
      case "open-gap":
        // A blind re-solve reproduces an isolated obstruction: halt for a directive.
        return {
          stage: "0", status: "checkpoint", advance: false,
          message: `${outcome.message}\nSupply a direction with d0_directive.ts (a construction, a paper to adapt, a reframing), then --resume.`,
        };
      case "pr-open":
      case "blocked":
        // Adjudication is progress, not a stuck solver: give the budget back.
        args.state.flags.d0_loop_counters = { ...d0Counters(args.state), solve_rounds: round };
        await saveState(args.ctx.repoRoot, args.ctx.qid, args.ctx.specialization, args.state);
        return { stage: "0", status: "checkpoint", advance: false, message: outcome.message };
    }
  }
  args.state.flags.d0_loop_cap_hit = `D0 solve cap (${D0_SOLVE_CAP} rounds) exhausted`;
  return {
    stage: "0",
    status: "checkpoint",
    advance: false,
    message:
      `D0 solve loop hit the cap (${D0_SOLVE_CAP} incomplete proof-carry rounds, CARRIED across resumes) ` +
      `without a clean discharge. Circuit breaker: re-resuming is a re-roll of a non-deterministic ` +
      `solver, not a retry. Fix the root cause, then resume with --clear-gate d0_loop_cap_hit.`,
  };
}

/** Stage "0.5" (typed): review ↔ directed-revise loop on the solved core. */

/** Persisted D-phase loop counters. These were plain in-process `for` bounds, so a resume
 *  silently granted a fresh budget; see `flags.d0_loop_counters` and the `d0_loop_cap_hit`
 *  cap gate. Reading through a helper keeps the default shape in one place. */
function d0Counters(state: StateJson): { solve_rounds: number; revise_rounds: number; consistency_heals: number } {
  const c = state.flags.d0_loop_counters;
  return {
    solve_rounds: c?.solve_rounds ?? 0,
    revise_rounds: c?.revise_rounds ?? 0,
    consistency_heals: c?.consistency_heals ?? 0,
  };
}

export async function runStage0_5Typed(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
}): Promise<StageResult> {
  // A new review attempt revokes any prior pass authority immediately. If this
  // attempt fails, checkpoints, or crashes, F entry must require another full
  // pass even when the reviewed files happened to remain byte-identical.
  await rm(d05AcceptanceReceiptPath(args.ctx), { force: true });
  // D0.R edits are provisional until a subsequent core panel passes. Snapshot every
  // durable and in-memory state field D0.R may mutate so a non-converging/failing
  // review cannot contaminate the authoritative D0 package or a same-revision resume.
  const corePath = coreJsonPath(args.ctx);
  const texPath = artifactPaths(args.ctx, args.state).tex;
  const pendingPath = resolveInDir(path.dirname(corePath), "d0r_pending_changes.json", [
    `${args.ctx.qid}_d0r_pending_changes.json`,
  ]);
  const semanticManifest = await loadSemanticManifest(args.ctx);
  if (semanticManifest) {
    const core = await readTypedCore(corePath);
    validateCoreManifest(semanticManifest, "core", core);
    if (!existsSync(texPath)) throw new Error("Stage 0 semantic manifest render: writeup.tex is absent");
    validateRenderedManifest(semanticManifest, await readFile(texPath, "utf8"));
  }
  // D0.R edits are provisional until a subsequent core panel passes. They are
  // committed to main as they are made (so history keeps them); a D0.5 exit
  // without PASS resets main to the head this invocation started from.
  const store = await ensureStore(args.ctx, args.state);
  {
    // A previous D0.5 invocation that died without PASS (kill, timeout) left its
    // provisional D0.R commits on main; reconcile before reviewing anything.
    const prior = args.state.flags.d0_5_head_before;
    const { head } = await headGraph(store);
    // Only D0.R's own commits are provisional. Anything else on top of `prior` (a
    // merged solver round, an orchestrator commit) is accepted work; then the flag is
    // simply stale and the D0.R edits below it stand.
    const onlyD0r = prior !== undefined && prior !== head && store.hasCommit(prior) &&
      (await store.history(head)).every((c) => c.id === prior || c.author === "d0r" || (c.kind === "reset" && c.author === "pipeline"));
    if (prior !== undefined && prior !== head && store.hasCommit(prior) && !onlyD0r) {
      console.warn(`[D0.5] stale d0_5_head_before ${prior.slice(0, 12)}: later non-D0.R commits exist on main; the earlier D0.R edits stand`);
    }
    if (onlyD0r) {
      const reset = await commitGraph({
        store, graph: await loadGraph(store, prior), parents: [head], author: "pipeline", kind: "reset",
        message: `D0.5 interrupted without PASS: discard unvetted D0.R edits (back to ${prior.slice(0, 12)})`, expectedHead: head, meta: { target: prior },
      });
      if (!reset.ok) throw new Error(`D0.R rollback refused: ${formatViolations(reset.violations)}`);
      await publishCore(args.ctx, store);
    }
  }
  const headBefore = (await headGraph(store)).head;
  args.state.flags.d0_5_head_before = headBefore;
  await saveState(args.ctx.repoRoot, args.ctx.qid, args.ctx.specialization, args.state);
  const transaction = {
    pending: existsSync(pendingPath) ? await readFile(pendingPath, "utf8") : null,
    designDecisions: structuredClone(args.state.design_decisions),
    addedAssumptions: structuredClone(args.state.added_assumptions),
  };
  let d0rTouched = false;
  let d0_5Passed = false;
  const rollbackUnvettedD0R = async (): Promise<void> => {
    if (!d0rTouched || d0_5Passed) return;
    const { head } = await headGraph(store);
    if (head !== headBefore) {
      const reset = await commitGraph({
        store, graph: await loadGraph(store, headBefore), parents: [head], author: "pipeline", kind: "reset",
        message: `D0.5 exited without PASS: discard unvetted D0.R edits (back to ${headBefore.slice(0, 12)})`, expectedHead: head,
        meta: { target: headBefore },
      });
      if (!reset.ok) throw new Error(`D0.R rollback refused: ${formatViolations(reset.violations)}`);
    }
    await publishCore(args.ctx, store);
    delete args.state.flags.d0_5_head_before;
    if (transaction.pending === null) await rm(pendingPath, { force: true });
    else await writeTextAtomic(pendingPath, transaction.pending);
    args.state.design_decisions = transaction.designDecisions;
    args.state.added_assumptions = transaction.addedAssumptions;
  };

  try {
  let prevKeys = new Set<string>();
  let lastReview: Stage0_5CoreResult | null = null;
  const target = args.ctx.noveltyTarget ?? "field";
  const floor = TARGET_FLOOR_LABEL[target];
  // The triage tier read (see below). Survives past its own round so that a LATER
  // non-pass exit — cap exhaustion, a round-3 backstop — still reports it, labelled as
  // the first-round read it is.
  let triage: GeneralReviewResult | null = null;
  const triageNote = (): string => (triage ? formatTriageTier(triage, target) : "");
  const reviseStart = d0Counters(args.state).revise_rounds;
  // Three D0.R EDITS require up to four panel reads: the initial read plus one
  // verification read after each edit.  The old `< D0_REVISE_CAP` bound made the
  // third edit at round 2 and then exited without ever reviewing it; `finally`
  // correctly rolled that unvetted edit back, turning a successful final repair
  // into a cap checkpoint.  Permit one verification-only round at the bound, but
  // never dispatch D0.R from that round, so the edit budget remains exactly three.
  for (let round = reviseStart; round <= D0_REVISE_CAP; round++) {
    // D0.5.G TRIAGE — dispatched CONCURRENTLY with the core panel on the first round of
    // each D0.5 invocation, instead of strictly after a panel pass.
    //
    // What it buys: every non-pass exit below routes back to a D0 re-solve while carrying
    // no tier, so the pipeline repeatedly paid for re-derivations of notes the cold referee
    // would have killed on sight. One concurrent read supplies that signal to all of them,
    // and licenses the early kill further down.
    //
    // What it COSTS — a real net spend, not a free win. When the panel passes on this same
    // round the verdict is reused below (same core, no write in between, same prompt), so
    // that path is unchanged and merely stops waiting for the referee serially. Every OTHER
    // path of an invocation that reaches here — fail, both backstops, D0.R escalation, cap
    // exhaustion, citation halt, and revise-then-pass (which re-reads authoritatively on the
    // later round) — pays one extra call of the run's priciest model
    // (MODEL_PLAN.stage0_5_general is claude/opus vs the panel's codex mechanicalTier).
    //
    // In aggregate that is roughly an EIGHTFOLD increase in cold-referee calls, not a
    // rounding error: measured over the 47 pipeline.jsonl histories under doc/research as of
    // 2026-07-31, 206 D0.5 halts previously bought ~24 referee calls (only the 16 PASS + 8
    // below-floor halts reached the pass branch); one call per invocation makes it ~206. The
    // tier signal on every non-pass exit, and the early kill, are bought at that price.
    //
    // Why the FIRST round of each invocation, not round 0 of the run: `revise_rounds` is
    // persisted, so after a non-pass halt the operator injects a D0 directive and re-runs,
    // and D0.5 re-enters with reviseStart > 0. Keying on round 0 would give the tier only to
    // the very first invocation and starve exactly the re-solve cycle this signal exists to
    // inform — the cycle where a fresh D0 derivation is most likely to have moved the tier.
    //
    // Why not EVERY round: D0.R repairs the proofs this referee grades, so its tier can move
    // across rounds — a stale verdict is not a safe stand-in for the authoritative call
    // (hence `roundTriage` below) — but re-dispatching each round would multiply the cost
    // above for a kernel that a directed in-place repair rarely changes.
    const wantTriage = round === reviseStart;
    const [coreSettled, genSettled] = await Promise.allSettled([
      runStage0_5Core(args),
      wantTriage
        ? runGeneralReview({ ctx: args.ctx, state: args.state, deps: args.deps, attempt: round + 1 })
        : Promise.resolve(null),
    ]);
    if (wantTriage) {
      // A cold-referee failure is ADVISORY here and must not fail the stage on a round
      // the panel may yet pass: the pass branch below re-runs it authoritatively, where a
      // throw is the correct (and unchanged) behaviour.
      if (genSettled.status === "fulfilled") triage = genSettled.value;
      else {
        const reason = genSettled.reason instanceof Error ? genSettled.reason.message : String(genSettled.reason);
        console.warn(`[causalsmith] D0.5.G triage referee failed (advisory, continuing): ${reason}`);
      }
    }
    // Settle both before rethrowing, so a panel throw cannot orphan a running codex
    // referee. The cost is that a fast panel precondition throw (missing core, bad node id)
    // now waits out the referee — acceptable, since that run is already failing.
    if (coreSettled.status === "rejected") throw coreSettled.reason;
    const review = coreSettled.value;
    // This round's read only — `null` on every later round, so a stale verdict can never
    // stand in for the authoritative call.
    const roundTriage = genSettled.status === "fulfilled" ? genSettled.value : null;
    lastReview = review;
    const curKeys = findingKeys(review.verdicts);
    // The first complete panel after a D0.R edit is the authority for whether
    // that edit cleared its assigned findings. Bank cleared prose before ANY
    // panel-result branch can return (citation, pass/tier, fail, proposal route,
    // or convergence), while formal bytes remain inside the transaction.
    const citationCheckpoint = citationVerificationCheckpoint(review);
    if (citationCheckpoint) {
      // Source access failure is not evidence that the cited claim is false and
      // must not be routed through D0.R as a mathematical revise. Stop at the
      // D boundary so main can seek a lawful source; if still unavailable, main
      // escalates to the user for the relevant page/exact statement. Once
      // attested in source.verbatim_statement, the same D0.5 audit reruns.
      //
      // Record the panel's verdicts before returning. This checkpoint fires on a
      // SOURCE-ACCESS problem, but `review` is a fully-paid panel result that may also
      // carry genuine math findings (including the cited-* findings synthesized into
      // math.findings). Returning without an escalation entry discarded all of them:
      // recoverable only because a rerun re-executes the whole panel — i.e. by paying
      // for it twice. The entry is provenance, not a re-solve directive, so it carries
      // no targets.
      await injectD0ReviewDirective({
        ctx: args.ctx,
        state: args.state,
        reason:
          "D0.5 halted on citation source-access, not on mathematics. These panel verdicts are recorded for " +
          "provenance so a resume does not re-pay for them; do not re-solve on this entry alone.",
        payload: { stage: "D0.5.citation", overall: review.overall, verdicts: review.verdicts },
        targetIds: [],
        provenanceOnly: true,
      });
      return { ...citationCheckpoint, message: citationCheckpoint.message + triageNote() };
    }
    if (review.overall === "pass") {
      // D0.5.G — cold tier referee. The core panel checked math soundness node by
      // node; this INDEPENDENT referee answers "is the delivered note actually good,
      // and at the target level?". It is TOLD the novelty floor and assesses the tier
      // of the PROVED content, then gates the pass on it. Recorded on every run so the
      // tier is greppable history (the gap the core panel's concise verdict left).
      //
      // Reuse this round's TRIAGE read when there is one: it was dispatched against the
      // same core this panel just passed, with no write in between, from the same prompt —
      // so it is the authoritative verdict, already paid for. Any other round (or a failed
      // triage dispatch) runs the referee here, exactly as before.
      const gen =
        roundTriage ??
        (await runGeneralReview({
          ctx: args.ctx,
          state: args.state,
          deps: args.deps,
          attempt: round + 1,
        }));
      const meetsFloor = tierRank(gen.tier) >= tierRank(floor);
      if (meetsFloor) {
        // D0.R edits core.json only. Publish the revised source preview once,
        // after the complete D0.5 panel and tier gate have accepted the edit.
        if (d0rTouched) await runStage0Render({ ctx: args.ctx, state: args.state });
        // The accepted core.json (with D0.R's in-place edits) becomes what the stores
        // render, so a later re-solve keeps those edits instead of dropping them.
        // Fail-safe: a refusal leaves the pass exactly as before.
        const foldNote = `accepted main=${(await headGraph(store)).head.slice(0, 12)}`;
        d0rTouched = false;
        delete args.state.flags.d0_5_head_before;
        // D0.R is transactional across the ENTIRE D0.5 gate. Core-panel approval
        // alone is insufficient: a below-floor cold review leaves the run at D0,
        // so its provisional edits must not replace the authoritative package.
        // This is the typed D0.5 authority for F entry. Emit it on EVERY full
        // pass, including ordinary pure-render stores and sanctioned rebases;
        // proposal-review iterations are a distinct earlier gate.
        await writeD05AcceptanceReceipt(args.ctx, args.state);
        d0_5Passed = true;
        // Record the tier on PASS too (greppable history), then advance.
        await appendReview(args.ctx, "stage_0.5.G", round + 1, {
          status: "pass",
          notes:
            `D0.5.G cold referee tier=${gen.tier} ≥ floor=${floor} (target=${target})` +
            `${gen.flagship_potential ? " | flagship_potential" : ""} | ${foldNote}`,
        }).catch(() => {});
        // CKPT (D0.5 → F1 go/no-go). A passing D0.5 (math panel + novelty floor BOTH
        // cleared) does NOT auto-flow into the expensive F1–F5 formalization. Return a
        // `checkpoint` (not `completed`) so the dispatch loop HALTS and the orchestrator
        // explicitly decides whether to commit to F1. `advance` is left default (not
        // false) so `stage_completed` still advances to "0.5"; on `--resume`,
        // nextStage("0.5") = "1" enters F1 and this never re-fires. (A below-floor tier
        // halts separately above as the BELOW-NOVELTY-FLOOR checkpoint.)
        return {
          stage: "0.5",
          status: "checkpoint",
          message:
            `Stage 0.5 (typed) PASS after ${round} directed-revise round(s) — ` +
            `D0.5.G tier=${gen.tier} ≥ floor=${floor} (target=${target}). ` +
            `CKPT (D0.5→F1 go/no-go): the maximized note cleared the panel AND the novelty floor; ` +
            `decide whether to commit to F1–F5, then \`--resume\` to enter F1.` +
            ` [${foldNote}]` +
            (gen.flagship_potential && gen.flagship_directive
              ? ` Flagship upside (not auto-pursued): ${gen.flagship_directive}`
              : ""),
        };
      }
      // tier < floor → the delivered note does not clear the novelty bar.
      // buildGeneralTierVerdict transcribes it into the revise/reject ReviewResult
      // the D0.5 boundary knows; we log it and halt for the operator carrying the
      // tier + critique + (when salvageable) the directed improvement to re-solve with.
      // Reroute budget. Each grant halts at an operator checkpoint and the next `--resume`
      // pays for a full D0 re-derivation, so the counter must survive the process — an
      // in-process bound would reset every resume and never bind. Counted only when the
      // reroute is actually OFFERED: a not-salvageable halt spends nothing.
      const reroutesUsed = args.state.flags.general_reroute_count ?? 0;
      const { canReroute, capExhausted } = decideGeneralReroute({ gen, reroutesUsed });
      if (canReroute) {
        args.state.flags.general_reroute_count = reroutesUsed + 1;
        await saveState(args.ctx.repoRoot, args.ctx.qid, args.ctx.specialization, args.state);
      }
      const verdict = buildGeneralTierVerdict(gen, target, canReroute, capExhausted);
      await appendReview(args.ctx, "stage_0.5.G", round + 1, verdict).catch(() => {});
      // Record the verdict on BOTH branches. Previously a non-salvageable below-floor
      // result wrote no escalation entry at all, so the referee's critique survived
      // only in a human-readable message and reviews/review_general.json — neither of
      // which D0 reads. If the run is later resumed or rewound, that paid verdict is
      // simply gone. `parseGeneralReview` also fail-safes a malformed response to
      // tier=incremental / salvageable=false, so a PARSE failure lands here too and
      // would vanish the same way.
      await injectD0ReviewDirective({
        ctx: args.ctx,
        state: args.state,
        reason: canReroute
          ? "The cold whole-paper referee placed the current paper below the requested novelty floor and supplied this directed improvement."
          : capExhausted
            ? `The cold whole-paper referee placed the current paper below the requested novelty floor with a directed improvement, but the reroute cap (${GENERAL_REROUTE_CAP}) is exhausted. Recorded for provenance; the topic is NOT refuted — only the automatic budget is spent.`
            : "The cold whole-paper referee placed the current paper below the requested novelty floor and judged it NOT salvageable in scope. Recorded for provenance; do not re-solve on this entry alone.",
        payload: { stage: "D0.5.G", target, floor, general_review: gen },
        targetIds: canReroute ? gen.flagged_conjecture_labels : [],
        // A non-salvageable tier carries no targets by nature; without this it would
        // force-open the whole paper on the next resume.
        provenanceOnly: !canReroute,
      });
      return {
        stage: "0.5",
        status: "checkpoint",
        advance: false,
        message:
          `Stage 0.5 (typed) BELOW NOVELTY FLOOR — D0.5.G tier=${gen.tier} < floor=${floor} ` +
          `(target=${target}). Critique: ${gen.critique}` +
          (canReroute
            ? `\nSalvageable (reroute ${reroutesUsed + 1}/${GENERAL_REROUTE_CAP}) — VET the directive for ` +
              `soundness, then inject it as a D0 directive and re-solve D0 to lift: ` +
              `${gen.improvement_directive}` +
              (gen.flagged_conjecture_labels.length > 0
                ? ` [targets: ${gen.flagged_conjecture_labels.join(", ")}]`
                : "")
            : capExhausted
              ? `\nReroute cap ${GENERAL_REROUTE_CAP} exhausted after ${reroutesUsed} directed re-solve(s) that ` +
                `did not lift the tier. The topic is NOT refuted — only the automatic budget is spent, so do ` +
                `not bank this as a dead object. Escalate: a root change (rewind D-1.2 / a new angle), or ` +
                `clear the cap deliberately via CAUSALSMITH_GENERAL_REROUTE_CAP. Last directive: ` +
                `${gen.improvement_directive}`
              : `\nNot salvageable within scope — bank downgraded, or re-anchor the proposal (rewind D-1.2).`),
      };
    }
    if (review.overall === "fail") {
      // A math `fail` keeps precedence over the triage tier: it halts here regardless, so
      // nothing is saved by pre-empting it, and a load-bearing defect is the more
      // actionable report. The tier rides along instead — this is a re-solve directive,
      // and the operator should not commit to one without knowing the note's ceiling.
      await injectD0ReviewDirective({
        ctx: args.ctx,
        state: args.state,
        reason: "The D0.5 whole-paper/core panel found a load-bearing defect that requires D0 re-derivation.",
        payload: { stage: "D0.5", overall: review.overall, verdicts: review.verdicts },
        targetIds: reviewTargetIds(review),
      });
      return {
        stage: "0.5",
        status: "checkpoint",
        advance: false,
        message:
          `Stage 0.5 (typed) FAIL on round ${round} — the math note has a defect the directed ` +
          `revise cannot fix in place. Findings: ${summarize(review.verdicts)}.` +
          ` Provide guidance via the D0 directive (a new direction / a paper to adapt / a reframing) and re-run, or rewind D0/D-1.2.` +
          triageNote(),
      };
    }
    // Proposal-taxonomy findings compare against state/proto surfaces outside
    // D0.R's core.json capability. Route them after pass/fail precedence but
    // before convergence, triage, cap, or edit charging.
    const proposalRoute = proposalFindingRoute(review);
    if (proposalRoute) {
      await injectD0ReviewDirective({
        ctx: args.ctx,
        state: args.state,
        reason:
          `D0.5 proposal/statement finding is outside D0.R scope: ${proposalRoute.labels.join(", ")}. ` +
          proposalRoute.action,
        payload: { stage: "D0.5", overall: review.overall, verdicts: review.verdicts },
        targetIds: [],
        // A topic/redraft/tier choice must not pre-commit a pending D0 re-solve.
        // Preserve the paid verdict, then let the orchestrator inject an actionable
        // directive only after it adjudicates the category-specific action.
        provenanceOnly: true,
      });
      return {
        stage: "0.5",
        status: "checkpoint",
        advance: false,
        message:
          `Stage 0.5 (typed) finding outside D0.R core-edit scope — ${proposalRoute.labels.join(", ")}. ` +
          `${proposalRoute.action}; no D0.R edit was dispatched or charged.` +
          triageNote(),
      };
    }
    // Loop-level non-convergence escalation (robust early-escalation): if a finding
    // (node+code) SURVIVED the previous round's D0.R edit and is still flagged, the
    // directed editor is not resolving it — escalate NOW rather than churn to the cap.
    // (D0.R self-escalation via `revised.escalate` only fires when D0.R itself reports
    // "failed"; this catches the case where D0.R keeps producing edits that don't land.)
    // `prevKeys` is per-INVOCATION state, initialized empty above, so "is there a previous
    // round to compare against?" is `round > reviseStart`, not `round > 0`. On a resume
    // (reviseStart >= 1) the old test passed the still-empty set as a real previous round,
    // and `curKeys.size >= 0` is vacuously true — so the very first round of every resumed
    // invocation fell straight through to the no-net-progress backstop and halted with
    // "D0.R round N made no net progress (0 → N findings)" before D0.R had run even once.
    const convergence = decideReviseConvergence(round > reviseStart ? prevKeys : null, curKeys);
    {
      if (convergence.kind === "persistent-findings") {
        const persistent = convergence.persistent;
        await injectD0ReviewDirective({
          ctx: args.ctx,
          state: args.state,
          reason: `D0.R did not clear persistent finding(s): ${persistent.join(", ")}. Re-derive them in D0 from the complete review below.`,
          payload: { stage: "D0.5", overall: review.overall, verdicts: review.verdicts },
          targetIds: reviewTargetIds(review),
        });
        return {
          stage: "0.5",
          status: "checkpoint",
          advance: false,
          message:
            `Stage 0.5 (typed) non-converging — finding(s) survived a D0.R edit and are still flagged on ` +
            `round ${round}: ${persistent.slice(0, 8).join(", ")}. The directed revise cannot resolve these ` +
            `in place (likely a genuine open gap needing a new idea). Open findings: ${summarize(review.verdicts)}.` +
            ` Provide guidance via the D0 directive (a new direction / a paper to adapt / a reframing) and re-run, or rewind D0/D-1.2.` +
            triageNote(),
        };
      }
      // No-net-progress backstop — see decideReviseConvergence.
      if (convergence.kind === "no-net-progress") {
        await injectD0ReviewDirective({
          ctx: args.ctx,
          state: args.state,
          reason: `D0.R made no net progress (${prevKeys.size} to ${curKeys.size} findings). Apply the complete review at D0 rather than another in-place edit.`,
          payload: { stage: "D0.5", overall: review.overall, verdicts: review.verdicts },
          targetIds: reviewTargetIds(review),
        });
        return {
          stage: "0.5",
          status: "checkpoint",
          advance: false,
          message:
            `Stage 0.5 (typed) non-converging — D0.R round ${round} made no net progress ` +
            `(${prevKeys.size} → ${curKeys.size} findings; different findings each round = whack-a-mole, ` +
            `typically a class of fixes that needs proto/def changes or new math beyond an in-place core edit). ` +
            `Open findings: ${summarize(review.verdicts)}.` +
            ` Provide guidance via the D0 directive (a new direction / a paper to adapt / a reframing) and re-run, or rewind D0/D-1.2.` +
            triageNote(),
        };
      }
    }
    // D0.5.G TRIAGE KILL — the only authority a triage read has to end the run, and it
    // fires only on `below floor AND no bounded fix` (see decideTriageKill). Reached only
    // on a `revise`: `pass` and `fail` return above, so this cannot pre-empt either. What
    // it stops is the remaining revise budget plus the D0 re-solve that would follow it,
    // on a note whose kernel the referee says cannot reach the bar.
    if (roundTriage && decideTriageKill(roundTriage, target)) {
      // The verdict this writes to reviews.jsonl is `reject`/`novelty`, and the bank
      // decision tree reads a novelty reject as "still mathematically sound → bank
      // downgraded". That does NOT hold here: the panel returned `revise` and its findings
      // are unrepaired, so soundness is simply unknown. Say so in the critique the
      // orchestrator reads, or a defective note gets banked as merely under-novel. It goes on
      // BOTH `verbatim_critique` and `halt_reason`: they are separate fields of the same
      // serialized verdict, so caveating only one leaves the other reading clean.
      const verdict = buildGeneralTierVerdict(roundTriage, target, false);
      const caveat =
        `\n\nHALTED AT TRIAGE: the math panel returned \`revise\` and its findings were never repaired, ` +
        `so this note is NOT established as mathematically sound — do not bank it as downgraded on this ` +
        `verdict alone. Open findings: ${summarize(review.verdicts)}`;
      // `halt_reason` is written by buildGeneralTierVerdict through a cast and is not on the
      // declared union, so reach both fields through one view of the freshly-built local.
      const text = verdict as { verbatim_critique?: string; halt_reason?: string };
      text.verbatim_critique = `${text.verbatim_critique ?? ""}${caveat}`;
      text.halt_reason = `${text.halt_reason ?? ""}${caveat}`;
      // Drop the routing field for the same reason. `tier_genuinely_below` is what
      // bank_entry's `reusableFromGap` maps to `not_reusable` ("not worth retrying with a
      // stronger solver") when the operator gives no explicit --reusable. That is far too
      // strong a conclusion to draw from a mid-repair advisory read — the exact under-tiering
      // this referee is documented to do. Absent, the mapping falls back to `unknown`, which
      // leaves the call with the operator.
      delete (verdict as { proposal_promise_gap?: string }).proposal_promise_gap;
      await appendReview(args.ctx, "stage_0.5.G", round + 1, verdict).catch(() => {});
      await injectD0ReviewDirective({
        ctx: args.ctx,
        state: args.state,
        reason:
          "D0.5.G triage placed the paper below the novelty floor with NO bounded fix in scope, before the " +
          "directed-revise loop spent its budget. Recorded for provenance alongside the still-open panel " +
          "findings; do not re-solve on this entry alone.",
        payload: {
          stage: "D0.5.G.triage",
          target,
          floor,
          general_review: roundTriage,
          overall: review.overall,
          verdicts: review.verdicts,
        },
        // Non-salvageable carries no targets by nature; without this the next resume would
        // force-open the whole paper.
        targetIds: [],
        provenanceOnly: true,
      });
      return {
        stage: "0.5",
        status: "checkpoint",
        advance: false,
        // The referee's critique goes BEHIND the marker (via triageNote), not inline: the
        // playbook classifies on the text before it, and free-text prose containing
        // "non-converging" or "< floor" would otherwise pick the branch.
        message:
          `Stage 0.5 (typed) BELOW NOVELTY FLOOR (triage, round ${round}) — D0.5.G tier=${roundTriage.tier} ` +
          `< floor=${floor} (target=${target}) and NOT salvageable in scope, so the directed-revise loop was ` +
          `stopped before spending its budget on a note that cannot clear the bar.\n` +
          `Panel findings left unrepaired (the tier, not these, is the reason for the halt): ${summarize(review.verdicts)}.\n` +
          `Not salvageable within scope — bank downgraded, or re-anchor the proposal (rewind D-1.2).` +
          triageNote(),
      };
    }
    prevKeys = curKeys;
    // The last allowed D0.R edit has now received its verification panel.  If it
    // still did not pass, fall through to the bounded cap checkpoint below; do
    // not silently grant a fourth repair.
    if (round === D0_REVISE_CAP) break;
    // revise → directed D0.R core-only edit, then re-review. Rendering waits
    // until the complete D0.5 gate accepts the provisional transaction.
    // Persist budget use only when an edit is actually dispatched. Panel reads that
    // pass, fail, hit citation access, or halt below-floor do not consume D0.R edits.
    // Arm the counter before dispatch so a worker crash cannot grant a free reroll.
    args.state.flags.d0_loop_counters = {
      ...d0Counters(args.state),
      revise_rounds: round + 1,
    };
    await saveState(args.ctx.repoRoot, args.ctx.qid, args.ctx.specialization, args.state);
    d0rTouched = true;
    const revised = await runStage0RCore({ ctx: args.ctx, state: args.state, deps: args.deps, review });
    {
      // D0.R edited core.json in place: commit it to main (author d0r). A refusal is
      // a broken edit — restore the file from main and escalate instead of reviewing it.
      const { head, graph } = await headGraph(store);
      const edited = graphFromCore(await readTypedCore(corePath), graph);
      const committed = await commitGraph({
        store, graph: edited, parents: [head], author: "d0r", kind: "direct",
        message: `D0.R round ${round + 1}: directed revise`, expectedHead: head,
      });
      if (!committed.ok) {
        await publishCore(args.ctx, store);
        await injectD0ReviewDirective({
          ctx: args.ctx,
          state: args.state,
          reason: `D0.R produced a core that fails the structural gate; its edit was discarded. Re-derive the reviewed targets in D0.`,
          payload: { stage: "D0.5", overall: review.overall, verdicts: review.verdicts, violations: committed.violations },
          targetIds: reviewTargetIds(review),
        });
        return {
          stage: "0.5", status: "checkpoint", advance: false,
          message: `Stage 0.5 (typed) D0.R round ${round + 1} produced an invalid core (discarded):\n${formatViolations(committed.violations)}`,
        };
      }
      await publishCore(args.ctx, store);
    }
    // D0.R early-escalation: if the directed edit reports the findings are NOT fixable
    // in place (needs real math / re-derivation / substrate), checkpoint NOW — do not
    // burn the rest of the revise cap thrashing on something it cannot solve.
    if (revised.escalate) {
      await injectD0ReviewDirective({
        ctx: args.ctx,
        state: args.state,
        reason: `D0.R escalated: ${revised.escalate.reason}. Re-derive the reviewed targets in D0.`,
        payload: { stage: "D0.5", overall: review.overall, verdicts: review.verdicts },
        targetIds: reviewTargetIds(review),
      });
      return {
        stage: "0.5",
        status: "checkpoint",
        advance: false,
        message:
          `Stage 0.5 (typed) D0.R escalated on round ${round} (before cap) — the directed revise cannot fix ` +
          `the findings in place: ${revised.escalate.reason}\nOpen findings: ${summarize(review.verdicts)}.` +
          ` Provide guidance via the D0 directive (a new direction / a paper to adapt / a reframing) and re-run, or rewind D0/D-1.2.` +
          triageNote(),
      };
    }
  }
  if (lastReview) {
    await injectD0ReviewDirective({
      ctx: args.ctx,
      state: args.state,
      reason: `The D0.R revise cap (${D0_REVISE_CAP}) was exhausted. Re-derive the remaining reviewed targets in D0.`,
      payload: { stage: "D0.5", overall: lastReview.overall, verdicts: lastReview.verdicts },
      targetIds: reviewTargetIds(lastReview),
    });
  }
  args.state.flags.d0_loop_cap_hit = `D0.5 revise cap (${D0_REVISE_CAP} rounds) exhausted`;
  return {
    stage: "0.5",
    status: "checkpoint",
    advance: false,
    message:
      `Stage 0.5 (typed) revise cap exhausted (${D0_REVISE_CAP} rounds, CARRIED across resumes) without PASS — likely a genuine open gap. Provide guidance via the D0 directive (a new direction / a paper to adapt / a reframing) and re-run, or rewind D0/D-1.2.` +
      triageNote(),
  };
  } finally {
    await rollbackUnvettedD0R();
  }
}

/** Split reviewer-supplied target ids by what D0 can actually ENFORCE.
 *
 *  `ReviewFindingSchema.node_id` validates against every core node id — statements,
 *  assumptions AND definitions. But D0's exact-target enforcement
 *  (`stage0_solve`'s `emittedTargets` check) is statement-shaped, so a finding on a
 *  `def:`/`ass:` node used to be filtered out here and delivered as prose only:
 *  structurally unenforceable, and silent about it. Splitting instead of filtering
 *  keeps the enforceable set exact while making the remainder visible in the
 *  directive, so the orchestrator can see a target was raised but not bound. */
/** Pure convergence decision for the D0.5 review↔D0.R loop.
 *
 *  - a finding (node+code key) that SURVIVED the previous round's D0.R edit means
 *    the directed editor is not resolving it — escalate now, don't churn to cap;
 *  - a round that does not strictly REDUCE the finding count is whack-a-mole
 *    (D0.R fixes one nit, the reviewer surfaces another) — also escalate;
 *  - genuine convergence shrinks the count every round. */
export function decideReviseConvergence(
  prevKeys: ReadonlySet<string> | null,
  curKeys: ReadonlySet<string>,
):
  | { kind: "continue" }
  | { kind: "persistent-findings"; persistent: string[] }
  | { kind: "no-net-progress"; before: number; after: number } {
  if (prevKeys === null) return { kind: "continue" };
  const persistent = [...curKeys].filter((k) => prevKeys.has(k));
  if (persistent.length > 0) return { kind: "persistent-findings", persistent };
  if (curKeys.size >= prevKeys.size) return { kind: "no-net-progress", before: prevKeys.size, after: curKeys.size };
  return { kind: "continue" };
}

export function partitionReviewTargets(
  targetIds: string[],
  core: { statements?: Array<{ id?: string }>; assumptions?: Array<{ id?: string }>; definitions?: Array<{ id?: string }> },
): { required: string[]; nonStatement: string[]; unknown: string[] } {
  const statementIds = new Set((core.statements ?? []).map((s) => s.id));
  const otherIds = new Set([...(core.assumptions ?? []), ...(core.definitions ?? [])].map((n) => n.id));
  const allIds = [...statementIds, ...otherIds].filter((id): id is string => typeof id === "string");
  // Referees do not all emit ids the same way — D0.5.G historically emitted bare
  // labels (`foo`) while core nodes are prefixed (`thm:foo`). Resolve a bare label to
  // its core id when that is UNAMBIGUOUS; an ambiguous label (`foo` matching both
  // `thm:foo` and `lem:foo`) stays unknown rather than binding to a guess.
  const resolve = (raw: string): string | null => {
    if (statementIds.has(raw) || otherIds.has(raw)) return raw;
    if (raw.includes(":")) return null;
    const matches = allIds.filter((id) => id.slice(id.indexOf(":") + 1) === raw);
    return matches.length === 1 ? matches[0] : null;
  };
  const required: string[] = [];
  const nonStatement: string[] = [];
  const unknown: string[] = [];
  for (const raw of [...new Set(targetIds)]) {
    const id = resolve(raw);
    if (id !== null && statementIds.has(id)) required.push(id);
    else if (id !== null && otherIds.has(id)) nonStatement.push(id);
    else unknown.push(raw);
  }
  return { required, nonStatement, unknown };
}

/** Normalized discriminator for a finding that anchors to no core node. Without it,
 *  every note-global finding keys to the same `?@?` and N distinct defects collapse
 *  to one — which made a whack-a-mole D0.R round read as convergence to both
 *  backstops below. Normalizing (rather than hashing raw text) keeps a genuinely
 *  PERSISTING finding on the same key across a re-word that changes only spacing
 *  or punctuation. */
function noteGlobalDiscriminator(oneLine: string | undefined): string {
  // Case is KEPT: lowercasing before the strip collapsed every case-paired TeX
  // symbol (`\Sigma` vs `\sigma`, `\Pi` vs `\pi`) — two DIFFERENT defects then
  // shared a key across rounds and the run halted as "non-converging" while
  // D0.R was in fact fixing one defect per round.
  return (oneLine ?? "")
    .replace(/[^A-Za-z0-9\s]/g, "")
    .replace(/\s+/g, " ")
    .trim()
    // Sentence-initial capitalization is a re-word, not a distinction.
    .replace(/^[A-Z]/, (c) => c.toLowerCase())
    .slice(0, 80);
}

/** Stable per-finding keys (node+code) across a review's verdicts — used to detect a
 *  finding that survived a D0.R edit (non-convergence). Node id falls back to `node`
 *  then `node_id` (verdict-shape tolerant); a finding anchored to no node is keyed by
 *  its normalized `one_line` so distinct note-global findings stay distinct. */
export function findingKeys(
  verdicts: Array<{ findings: Array<{ code?: string; node?: string; node_id?: string; one_line?: string }> }>,
): Set<string> {
  const keys = new Set<string>();
  for (const v of verdicts) {
    for (const f of v.findings) {
      const node = f.node ?? f.node_id;
      keys.add(node ? `${f.code ?? "?"}@${node}` : `${f.code ?? "?"}@~${noteGlobalDiscriminator(f.one_line)}`);
    }
  }
  return keys;
}

function summarize(verdicts: Array<{ referee: string; findings: Array<{ code?: string; node?: string; node_id?: string }> }>): string {
  return verdicts
    .flatMap((v) => v.findings.map((f) => `${f.code ?? "?"}@${f.node ?? f.node_id ?? "?"}`))
    .slice(0, 8)
    .join(", ");
}

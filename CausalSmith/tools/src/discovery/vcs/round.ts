// One D0 solve round on the versioned graph.
//
//   main ──render──► frozen core ──units (WCC of open statements)──► solver workers
//        ◄──merge── PR head ◄──applyUnitOutput── unit outputs
//
// A round never edits `main` directly: every solver output becomes a pull request
// (vcs/pr.ts). A PR with nothing to approve merges itself; one with claim /
// definition / assumption changes waits for the adjudicator. Proof reuse is the
// basis rule (vcs/validity.ts): a statement is dispatched iff it is open on main.
import { existsSync } from "node:fs";
import { createHash } from "node:crypto";
import { mkdir, readFile, rm, writeFile } from "node:fs/promises";
import path from "node:path";
import { MODEL_PLAN } from "../../constants.js";
import { discoveryBrief, parseStageOutput, readPrompt, type StageDeps } from "../../pipeline_support.js";
import type { PipelineContext, StateJson } from "../../types.js";
import { dispatchAgent } from "../../framework/agent_dispatch.js";
import { writeJsonAtomic, writeTextAtomic } from "../../shared/json_atomic.js";
import { coreJsonPath } from "../stages/d0_core.js";
import { d05AcceptanceReceiptPath } from "../stages/d0_acceptance.js";
import { proposalRevision } from "../proposal_revision.js";
import { workingPath } from "../legacy_working.js";
import type { Core, CoreStatement } from "../core/schema.js";
import { clusterFor, loadClusterSetupBlock } from "../cluster_setup.js";
import { directivesConsumed, formatDirectiveContext, pendingDirectives, readEscalationLog } from "../escalation_log.js";
import { projectFrozenCore, serializeFrozenCoreSnapshot } from "../solve/context_projection.js";
import type { SolveUnitOutput } from "../solve/schemas.js";
import { companionPathFor } from "../solve/tex_companion.js";
import {
  SolveUnitCarrierError,
  acquireSolvePathLease,
  clearOrphanSolvePathLeases,
  groupToProveByComponent,
  readSolveUnitOutput,
  solveReuseReceiptsDir,
  unitOutPath,
} from "../solve/unit_io.js";
import { headGraph, publishCore } from "./commit.js";
import { carryLegacyLeftovers, initStoreFromRun, recordProposalRevision, reinitializeOnReproposal } from "./convert.js";
import { diffGraphs, loadGraph, nodesOfType, statementBlob, type Graph } from "./graph.js";
import { sha256Hex } from "./node.js";
import { listPrs, mergePr, openPr, prLosses, scopeSubmissionProse, type PrRecord, type UnitSubmission } from "./pr.js";
import { renderCore } from "./render.js";
import { MAIN_REF, VcsStore } from "./store.js";
import { deriveStatus, openStatements, proofVerdict } from "./validity.js";

const METADATA_TARGET_FIELDS: Record<string, string> = {
  "metadata:target-estimand": "target_estimand",
  "metadata:estimand-functional": "estimand_functional",
  "metadata:comparator-promise-table": "comparator_promise_table",
  "metadata:tldr": "tldr",
  "metadata:project-justification": "project_justification",
  "metadata:related-work": "related_work",
  "metadata:interpretation": "interpretation",
  "metadata:honest-scope": "honest_scope",
  "metadata:sampling-model": "sampling_model",
  "metadata:technical-internal-limitation": "technical_internal_limitation",
};

function graphTargetId(graph: Graph, id: string): string | null {
  if (graph.nodes.has(id)) return id;
  if (id === "metadata:reverse-dependencies" || METADATA_TARGET_FIELDS[id] !== undefined) return "meta";
  return null;
}

interface TargetReceipt { fields: Set<string>; removal: boolean; diffFree: boolean }

/** Which fields an exact typed output channel was authorized to change for a
 * required target.  Completion later intersects these with the landed graph
 * diff, so a no-op proof plus an unrelated prose edit cannot satisfy a repair. */
function outputTargetReceipt(output: SolveUnitOutput, id: string): TargetReceipt | null {
  const fields = new Set<string>();
  let removal = false;
  let diffFree = false;
  if (id === "metadata:reverse-dependencies") {
    diffFree = output.proposed_core_edits.some((e) => e.kind === "rebuild-reverse-dependencies");
    return diffFree ? { fields, removal, diffFree } : null;
  }
  if (id.startsWith("metadata:")) {
    const field = METADATA_TARGET_FIELDS[id];
    if (field === undefined) return null;
    const present = field === "target_estimand"
      ? output.proposed_core_edits.some((e) => e.kind === "target-estimand-replace")
      : field === "estimand_functional"
        ? output.proposed_core_edits.some((e) => e.kind === "estimand-functional-replace")
        : field === "comparator_promise_table"
          ? output.proposed_core_edits.some((e) => e.kind === "comparator-promise-table-replace")
          : output.prose_updates?.[field as keyof NonNullable<SolveUnitOutput["prose_updates"]>] !== undefined;
    if (!present) return null;
    fields.add(field);
    if (field === "comparator_promise_table") fields.add("comparator_promises");
    return { fields, removal, diffFree };
  }
  if (id === "meta") {
    for (const alias of Object.keys(METADATA_TARGET_FIELDS)) {
      const receipt = outputTargetReceipt(output, alias);
      if (receipt !== null) for (const field of receipt.fields) fields.add(field);
    }
    return fields.size > 0 ? { fields, removal, diffFree } : null;
  }
  if (/^(?:thm|lem|prop|oeq|conj):/.test(id)) {
    if (output.proofs.some((p) => p.id === id)) for (const f of ["proof_tex", "proof_basis", "obligation"]) fields.add(f);
    if (output.added_lemmas.some((s) => s.id === id)) for (const f of ["proof_tex", "proof_basis", "source", "obligation"]) fields.add(f);
    if (output.resolved_oeqs.some((r) => r.source_id === id)) fields.add("resolved_by");
    if (output.proposed_statement_changes.some((c) => c.id === id)) fields.add("statement");
    for (const e of output.proposed_core_edits) {
      if (!("id" in e) || e.id !== id) continue;
      if (e.kind === "statement-delete") removal = true;
      if (e.kind === "statement-replace") for (const f of Object.keys(e.proposed)) if (f !== "id") fields.add(f);
    }
    if (output.open_obligations.some((o) => o.node_id === id)) fields.add("obligation");
    return fields.size > 0 || removal ? { fields, removal, diffFree } : null;
  }
  if (id.startsWith("def:")) {
    if (output.proposed_definition_changes.some((c) => c.id === id)) fields.add("construction");
    for (const e of output.proposed_core_edits) {
      if (!("id" in e) || e.id !== id) continue;
      if (e.kind === "definition-delete") removal = true;
      if (e.kind === "definition-replace") for (const f of Object.keys(e.proposed)) if (f !== "id") fields.add(f);
    }
  }
  else if (id.startsWith("ass:")) {
    for (const e of output.proposed_core_edits) {
      if (!("id" in e) || e.id !== id) continue;
      if (e.kind === "assumption-delete") removal = true;
      if (e.kind === "assumption-replace") for (const f of Object.keys(e.proposed)) if (f !== "id" && f !== "used_by") fields.add(f);
    }
  }
  else if (id.startsWith("sym:")) {
    for (const e of output.proposed_core_edits) {
      if (!("name" in e) || `sym:${e.name}` !== id) continue;
      if (e.kind === "symbol-delete") removal = true;
      if (e.kind === "symbol-replace") for (const f of Object.keys(e.proposed)) if (f !== "name") fields.add(f);
    }
  }
  else if (id.startsWith("bib:")) {
    if (output.proposed_core_edits.some((e) => e.kind === "bibliography-replace" && `bib:${e.key}` === id)) fields.add("citation");
  }
  return fields.size > 0 || removal ? { fields, removal, diffFree } : null;
}

/** A worker's explicit "the target is not provable" refusal — a mathematical
 * signal that must surface unchanged, never a mechanical-retry candidate. */
export class SolveUnitMathFailure extends Error {}
class SolveUnitMechanicalReadError extends Error {}

export interface RoundOutcome {
  kind: "clean" | "incomplete" | "open-gap" | "pr-open" | "blocked";
  message: string;
  pr?: PrRecord;
  /** Statements still to-prove on main after the round (non-questions). */
  openIds: string[];
  /** Non-question statements the round left with an isolated open step. */
  obligations: Array<{ id: string; what_is_open: string }>;
  /** Directive-required targets the round did not touch. */
  unaddressedTargets: string[];
  dispatched: number;
}

/** Bring a run onto the store if it is not there yet (a resume of a run that
 *  started on the old stores). Idempotent. A D0.5 pass recorded against the old
 *  stores (schema 1, exact core bytes) stays an accepted pass: it is re-recorded
 *  against the main commit and the re-rendered core. */
export async function ensureStore(ctx: PipelineContext, state: StateJson): Promise<VcsStore> {
  const store = VcsStore.at(ctx);
  const legacyPass = await legacyReceiptMatchesCurrentCore(ctx, state);
  if (!store.exists()) {
    const { id, origin } = await initStoreFromRun(ctx);
    // The old cursor's directive position carries over so pending directives stay pending.
    if (state.flags.d0_directives_consumed === undefined) {
      const legacy = await legacyDirectiveCursor(ctx);
      if (legacy !== null) state.flags.d0_directives_consumed = legacy;
    }
    await recordProposalRevision(store, proposalRevision(state));
    await publishCore(ctx, store);
    console.warn(`[D0] initialized the graph store from ${origin} (main ${id.slice(0, 12)})`);
  } else if (legacyPass) {
    await publishCore(ctx, store);
  }
  if (legacyPass) {
    const main = (await store.readRef(MAIN_REF))!;
    const coreSha = createHash("sha256").update(await readFile(coreJsonPath(ctx))).digest("hex");
    await writeJsonAtomic(d05AcceptanceReceiptPath(ctx), {
      schema_version: 2, kind: "accepted-d05-store", proposal_revision: proposalRevision(state), main_commit: main, core_sha256: coreSha,
    });
    console.warn("[D0] converted the D0.5 acceptance receipt to the graph store (the pass stands)");
  }
  // A D-1.2 re-proposal replaces the paper on main.
  const extensionPending = state.flags.d0_cross_boundary_rewind?.intent === "extension" && state.flags.d0_cross_boundary_rewind.status === "pending";
  const reinit = extensionPending ? null : await reinitializeOnReproposal(ctx, state, store);
  if (reinit !== null) {
    await publishCore(ctx, store);
    console.warn(`[D0] proposal revision moved: main re-initialized from the new proto (${reinit.slice(0, 12)})`);
  }
  // What the old cursor parked (sealed questions, un-adjudicated proposals).
  for (const note of await carryLegacyLeftovers(ctx, store)) console.warn(`[D0] legacy carry: ${note}`);
  return store;
}

/** A schema-1 receipt whose recorded core bytes are exactly the current core.json. */
async function legacyReceiptMatchesCurrentCore(ctx: PipelineContext, state: StateJson): Promise<boolean> {
  const receiptPath = d05AcceptanceReceiptPath(ctx);
  const corePath = coreJsonPath(ctx);
  if (!existsSync(receiptPath) || !existsSync(corePath)) return false;
  try {
    const recorded = JSON.parse(await readFile(receiptPath, "utf8")) as { schema_version?: number; proposal_revision?: string; core_sha256?: string };
    if (recorded.schema_version !== 1 || recorded.proposal_revision === undefined || recorded.proposal_revision !== proposalRevision(state)) return false;
    return recorded.core_sha256 === createHash("sha256").update(await readFile(corePath)).digest("hex");
  } catch {
    return false;
  }
}

async function legacyDirectiveCursor(ctx: PipelineContext): Promise<number | null> {
  const p = workingPath(ctx);
  if (!existsSync(p)) return null;
  try {
    const w = JSON.parse(await readFile(p, "utf8")) as { escalation_entries_consumed?: unknown };
    return typeof w.escalation_entries_consumed === "number" ? w.escalation_entries_consumed : null;
  } catch {
    return null;
  }
}

function redoMathWitnessBlock(state: StateJson): string {
  const w = state.flags.redo_math_witness;
  if (!w) return "";
  return [
    "=== F3 REFUTATION — RE-DERIVE THIS NODE (do NOT re-emit the refuted claim) ===",
    `Node \`${w.obj_id}\` was PROVEN-FALSE downstream by a concrete witness; your prior derivation of it`,
    `is WRONG. Re-derive ONLY this node and its dependents [${w.dependents.join(", ") || "none"}]; leave`,
    "every other established proof intact (incremental re-solve, not from scratch). The refuting witness",
    `(type: ${w.type}) is a HARD CONSTRAINT your new statement/proof MUST respect:`,
    w.detail,
    "If the node cannot be salvaged as stated, weaken/correct it (proposed_statement_changes) so the",
    "witness no longer refutes it — never restate the same claim.",
  ].join("\n");
}

async function publishFrozenCoreSnapshot(ctx: PipelineContext, core: Core): Promise<string> {
  const serialized = serializeFrozenCoreSnapshot(core);
  const dir = path.join(path.dirname(unitOutPath(ctx, "snapshot")), "solve_context");
  const snapshotPath = path.join(dir, `core-${serialized.sha256}.json`);
  await mkdir(dir, { recursive: true });
  if (!existsSync(snapshotPath)) await writeTextAtomic(snapshotPath, serialized.bytes);
  return snapshotPath;
}

interface UnitPlan {
  label: string;
  targets: CoreStatement[];
  priorContext: string;
  proseRole: "owner" | "omit";
}

/** Which statements a round dispatches, grouped into units. */
export function planUnits(args: {
  graph: Graph;
  core: Core;
  requiredTargets: Set<string>;
  hasDirective: boolean;
  directiveContext: string;
}): UnitPlan[] {
  const { graph, core, requiredTargets } = args;
  const byId = new Map(core.statements.map((s) => [s.id, s] as const));
  const open = new Map<string, CoreStatement>();
  for (const id of openStatements(graph)) {
    const s = byId.get(id);
    if (s === undefined) continue;
    // A question with a recorded obligation is an acknowledged residual: not paid
    // for again unless a directive names it.
    if (s.kind === "openendedquestion" && s.obligation !== undefined && !requiredTargets.has(id)) continue;
    open.set(id, s);
  }
  // An untargeted directive revalidates the whole paper; a targeted one forces
  // exactly its targets open (even if proved) and pays only for their components.
  const forced = args.hasDirective
    ? (requiredTargets.size > 0 ? [...requiredTargets] : core.statements.map((s) => s.id))
    : [];
  for (const id of forced) {
    const s = byId.get(id);
    if (s === undefined) continue;
    if (s.kind === "openendedquestion" && s.obligation !== undefined && !requiredTargets.has(id)) continue;
    open.set(id, s);
  }
  let groups = groupToProveByComponent([...open.values()]);
  if (args.hasDirective && requiredTargets.size > 0) {
    const scoped = groups.filter((g) => g.targets.some((t) => requiredTargets.has(t.id)));
    if (scoped.length > 0 && scoped.length < groups.length) groups = scoped;
  }
  const plans: UnitPlan[] = groups.map((g, i) => {
    const targetIds = new Set(g.targets.map((t) => t.id));
    const established = [...new Set(g.targets.flatMap((t) => t.depends_on))]
      .filter((id) => !targetIds.has(id) && byId.has(id) && deriveStatus(graph, id) === "proved")
      .map((id) => `- ${id} (proved; cite the frozen statement above)`);
    const priorProofs: string[] = [];
    const partials: string[] = [];
    for (const t of g.targets) {
      const blob = statementBlob(graph, t.id);
      if (blob === undefined) continue;
      const proof = (blob.body.proof_tex ?? "").trim();
      const verdict = proofVerdict(graph, t.id);
      if (proof.length > 0 && verdict.valid) priorProofs.push(`- ${t.id}: ${proof}`);
      else if (proof.length > 0) {
        const why = verdict.reason === "no-basis" ? "a partial argument" : `written against a previous version of ${verdict.stale.join(", ")}`;
        partials.push(`- ${t.id} [${why}; EXTEND or REALIGN it, do not restart]: ${proof}`);
      }
      if (blob.body.obligation?.partial_result) partials.push(`- ${t.id} [recorded partial result]: ${blob.body.obligation.partial_result}`);
      if (blob.body.obligation) partials.push(`- ${t.id} [open step last round]: ${blob.body.obligation.what_is_open} — obstruction: ${blob.body.obligation.obstruction}; tried: ${blob.body.obligation.attempted}`);
    }
    const body = [
      args.directiveContext,
      established.length > 0 ? "=== ALREADY-ESTABLISHED RECEIPTS (still valid — cite for REUSE, do NOT re-derive) ===\n" + established.join("\n") : "",
      priorProofs.length > 0 ? "=== PRIOR PROOF OF A DIRECTED TARGET (revise/replace it; it is NOT established for this round) ===\n" + priorProofs.join("\n\n") : "",
      partials.length > 0 ? "=== PRIOR PARTIAL PROGRESS on your targets (EXTEND this, do NOT restart) ===\n" + partials.join("\n\n") : "",
    ].filter((x) => x.trim().length > 0);
    const priorContext = body.length > 0
      ? ["=== PRIOR-ROUND CONTEXT (reuse only — you still owe a proof or a proposed change for EVERY target) ===", ...body].join("\n\n")
      : "";
    // Paper prose changes only in an explicit directive round. Within such a
    // round one deterministic unit owns it; ordinary solve rounds cannot invent
    // approval-free global framing from a partial component view.
    const proseRole: UnitPlan["proseRole"] = args.hasDirective && i === 0 ? "owner" : "omit";
    return { label: g.label, targets: g.targets, priorContext, proseRole };
  });
  if (plans.length === 0 && args.hasDirective) {
    plans.push({ label: "directive", targets: [], priorContext: args.directiveContext, proseRole: "owner" });
  }
  return plans;
}

async function solveUnit(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
  core: Core;
  plan: UnitPlan;
  clusterSetupBlock: string;
  snapshotPath: string;
}): Promise<SolveUnitOutput> {
  const { ctx, plan } = args;
  const label = plan.label;
  const outPath = unitOutPath(ctx, label);
  await mkdir(path.dirname(outPath), { recursive: true });
  await mkdir(path.dirname(companionPathFor(outPath)), { recursive: true });
  const lease = await acquireSolvePathLease(outPath);
  try {
    const projected = projectFrozenCore(args.core, new Set(plan.targets.map((t) => t.id)));
    const targetReceipts = plan.targets.map((t) => {
      if (t.status === "cited") return t;
      const { statement: _s, depends_on: _d, proof_tex: _p, ...receipt } = t;
      return receipt;
    });
    const prompt = [
      await readPrompt(ctx, "stage0_common_discovery.txt"),
      "",
      args.clusterSetupBlock,
      "",
      await readPrompt(ctx, "stage0_solve.txt"),
      "",
      discoveryBrief(ctx, args.state),
      ...(redoMathWitnessBlock(args.state) ? ["", redoMathWitnessBlock(args.state)] : []),
      "",
      "=== FROZEN CORE TARGET NEIGHBORHOOD (read-only inline context) ===",
      JSON.stringify(projected.inline, null, 2),
      "",
      "=== FROZEN CORE SNAPSHOT + OMISSION MANIFEST ===",
      `CORE_SNAPSHOT_PATH: ${args.snapshotPath}`,
      JSON.stringify(projected.manifest, null, 2),
      "The inline view contains your targets, their transitive statement dependencies, and referenced catalog/symbol closure. The compact manifest names omitted nodes and affected downstream statements. If an omitted id becomes relevant, inspect that id selectively in CORE_SNAPSHOT_PATH (for example with jq or rg); inspect affected downstream nodes before changing a claim or dependency they consume. Do not scan the snapshot by default and NEVER edit it.",
      ...(plan.priorContext.trim().length > 0 ? ["", plan.priorContext] : []),
      ...(plan.proseRole === "owner" ? [
        "",
        "=== PAPER-WIDE PROSE OWNERSHIP ===",
        "You are the ONLY solve unit allowed to emit `prose_updates` this round. Synthesize one canonical",
        "paper-wide update that incorporates the orchestrator directive; inspect only the necessary prose or",
        "result records in CORE_SNAPSHOT_PATH before writing it. In `statement_notes`, name only statements",
        "present in this round's FROZEN CORE or a replacement theorem/helper that YOUR unit emits.",
      ] : plan.proseRole === "omit" ? [
        "",
        "=== PAPER-WIDE PROSE OWNERSHIP ===",
        "Another solve unit owns the single canonical paper-wide prose update. OMIT `prose_updates` entirely;",
        "solve only your mathematical targets.",
      ] : []),
      "",
      `=== TARGET STATEMENT(S) TO SOLVE (unit: ${label}) ===`,
      "Exact claim text and dependencies are in the frozen neighborhood above; these receipts add target-only metadata.",
      JSON.stringify(targetReceipts, null, 2),
      "",
      `SOLVE_OUTPUT_PATH: ${outPath}`,
      `SOLVE_COMPANION_PATH: ${companionPathFor(outPath)}`,
      "Both paths above are already absolute. Write exactly those paths; never prefix them with the cwd or repo name.",
      "D-orchestration validates and mechanically normalizes the artifact after this call; spend this call on the mathematics.",
      'Return only JSON on stdout: {"status":"completed","message":"...","artifacts":["<solve.json>"]}.',
    ].join("\n");
    const promptSha = sha256Hex(prompt);
    const receiptPath = path.join(solveReuseReceiptsDir(ctx), `${path.basename(outPath)}.receipt`);

    const readValidated = (): Promise<SolveUnitOutput> =>
      readSolveUnitOutput(outPath, label, { persistCanonical: true, assertPersistenceLease: lease.assertOwned });
    const companionSha = async (): Promise<string | undefined> => {
      const p = companionPathFor(outPath);
      return existsSync(p) ? sha256Hex(await readFile(p, "utf8")) : undefined;
    };
    const writeReceipt = async (): Promise<void> => {
      await mkdir(path.dirname(receiptPath), { recursive: true });
      await writeFile(receiptPath, `${JSON.stringify({
        format: "v2", unit: label, created: new Date().toISOString(),
        model: MODEL_PLAN.stage0_solve.model, effort: MODEL_PLAN.stage0_solve.effort,
        prompt_sha256: promptSha, output_sha256: sha256Hex(await readFile(outPath, "utf8")),
        companion_sha256: await companionSha(),
      }, null, 2)}\n`, "utf8");
    };
    // Reuse lane: a validated output bound to this exact prompt is not re-paid.
    if (process.env.CAUSALSMITH_D0_REUSE !== "0" && existsSync(receiptPath) && existsSync(outPath)) {
      try {
        const r = JSON.parse(await readFile(receiptPath, "utf8")) as Record<string, unknown>;
        if (r.format === "v2" && r.model === MODEL_PLAN.stage0_solve.model && r.effort === MODEL_PLAN.stage0_solve.effort &&
            r.prompt_sha256 === promptSha && r.output_sha256 === sha256Hex(await readFile(outPath, "utf8")) &&
            (r.companion_sha256 ?? undefined) === (await companionSha())) {
          const reused = (scopeSubmissionProse({
            unit: plan.label, targets: plan.targets.map((target) => target.id), output: await readValidated(),
          }, plan.proseRole)).output;
          console.warn(`[D0-SOLVE] unit ${label}: reusing the persisted validated output (prompt unchanged) — no model call.`);
          await writeReceipt();
          return reused;
        }
      } catch {
        // fall through to a fresh solve
      }
    }
    await rm(receiptPath, { force: true });
    await rm(outPath, { force: true });
    await rm(companionPathFor(outPath), { force: true });

    const attempt = async (retryNote?: string): Promise<SolveUnitOutput> => {
      const out = await dispatchAgent({
        ctx, deps: args.deps, stage: "0",
        label: `D0-SOLVE unit ${label}${retryNote === undefined ? "" : " (model-call recovery)"}`,
        prompt: retryNote === undefined ? prompt : [prompt, "", "=== MODEL-CALL RECOVERY — NO TRUSTWORTHY ARTIFACT WAS WRITTEN ===", retryNote, "Repeat the same mathematical answer and write the required artifact; do not change the solution."].join("\n"),
        promptSources: ["prompts/D0/stage0_solve.txt", `unit:${label}`],
        model: MODEL_PLAN.stage0_solve.model,
        reasoningEffort: MODEL_PLAN.stage0_solve.effort,
        inactivityTimeoutMs: 30 * 60 * 1000,
      });
      const parsed = parseStageOutput(out.stdout);
      if (parsed.status === "failed") {
        throw new SolveUnitMathFailure(`Stage 0-SOLVE failed on unit ${label}: ${parsed.message ?? "(no message)"} — the target is not provable from its declared dependencies; fix the core, do not launder.`);
      }
      try {
        return await readValidated();
      } catch (err) {
        throw new SolveUnitMechanicalReadError(err instanceof Error ? err.message : String(err), { cause: err });
      }
    };
    let output: SolveUnitOutput;
    try {
      output = (scopeSubmissionProse({
        unit: plan.label, targets: plan.targets.map((target) => target.id), output: await attempt(),
      }, plan.proseRole)).output;
    } catch (err) {
      if (!(err instanceof SolveUnitMechanicalReadError)) throw err;
      if (existsSync(outPath) && !(err.cause instanceof SolveUnitCarrierError)) throw err;
      console.warn(`[D0-SOLVE] unit ${label} wrote no trustworthy solve artifact; repeating this unit once: ${err.message}`);
      await rm(outPath, { force: true });
      await rm(companionPathFor(outPath), { force: true });
      output = (scopeSubmissionProse({
        unit: plan.label, targets: plan.targets.map((target) => target.id), output: await attempt(err.message),
      }, plan.proseRole)).output;
    }
    await writeReceipt();
    return output;
  } finally {
    await lease.release();
  }
}

/** Run one round. Returns without dispatching when a PR is already awaiting a verdict. */
export async function runVcsSolveRound(args: { ctx: PipelineContext; state: StateJson; deps: StageDeps; round: number }): Promise<RoundOutcome> {
  const { ctx, state } = args;
  const store = await ensureStore(ctx, state);
  await clearOrphanSolvePathLeases(ctx);
  const openPrs = await listPrs(store, "open");
  if (openPrs.length > 0) {
    const pr = openPrs[openPrs.length - 1];
    return {
      kind: "blocked",
      message: `D0 refuses to dispatch while PR ${pr.id.slice(0, 12)} (round ${pr.round}) awaits a verdict: ` +
        `${pr.approval.length} item(s) need approval. Review it with \`d0_vc.ts ${ctx.qid} ${ctx.specialization} pr show ${pr.id.slice(0, 12)}\`, ` +
        "then `pr merge` (accept/reject per node) or `pr close`, and --resume.",
      pr, openIds: [], obligations: [], unaddressedTargets: [], dispatched: 0,
    };
  }
  const { head, graph } = await headGraph(store);
  const core = renderCore(graph);
  const journal = await readEscalationLog(ctx);
  const consumed = directivesConsumed(state);
  const pending = pendingDirectives(journal, consumed);
  const declared = pending.flatMap((e) => e.required_core_targets ?? []);
  const resolvedTargets = declared.map((id) => [id, graphTargetId(graph, id)] as const);
  const unresolved = resolvedTargets.filter(([, graphId]) => graphId === null).map(([id]) => id);
  // A malformed target makes the directive unexecutable as a whole: nothing is
  // dispatched, and the directive is CONSUMED so the operator re-issues a corrected
  // one instead of every later resume blocking on the typo (there is no withdraw
  // command). A whole-paper round is never the silent fallback for a typo.
  if (unresolved.length > 0) {
    state.flags.d0_directives_consumed = journal.length;
    return {
      kind: "blocked",
      message: `directive target(s) not in the graph: ${unresolved.join(", ")}; nothing dispatched and ALL pending directives were consumed. Re-issue every directive you still want, with existing statement ids (see core.json) or without targets for a whole-paper round.`,
      openIds: [], obligations: [], unaddressedTargets: unresolved, dispatched: 0,
    };
  }
  const requiredTargets = new Set(resolvedTargets.flatMap(([, graphId]) => graphId === null ? [] : [graphId]));
  const directiveContext = formatDirectiveContext(journal, consumed);
  const plans = planUnits({ graph, core, requiredTargets, hasDirective: pending.length > 0, directiveContext });
  if (plans.length === 0) {
    return { kind: "clean", message: "nothing open on main; no directive pending", openIds: [], obligations: [], unaddressedTargets: [], dispatched: 0 };
  }
  const clusterSetupBlock = await loadClusterSetupBlock(ctx, clusterFor(ctx, state));
  const snapshotPath = await publishFrozenCoreSnapshot(ctx, core);
  console.warn(`[D0-SOLVE] round ${args.round}: dispatching ${plans.length} unit(s): ${plans.map((p) => `${p.label} [${p.targets.map((t) => t.id).join(", ")}]`).join("; ")}`);
  // Every unit that returned is kept even when a sibling failed: its output becomes
  // part of this round's PR, and the failure is reported alongside.
  const settled = await Promise.allSettled(plans.map(async (plan) => ({
    plan,
    output: await solveUnit({ ctx, state, deps: args.deps, core, plan, clusterSetupBlock, snapshotPath }),
  })));
  const outputs = settled.flatMap((r) => (r.status === "fulfilled" ? [r.value] : []));
  const failures = settled.flatMap((r, i) => (r.status === "rejected" ? [`${plans[i].label}: ${r.reason instanceof Error ? r.reason.message : String(r.reason)}`] : []));
  if (pending.length > 0 && failures.length > 0) {
    return {
      kind: "incomplete",
      message: `directive round ${args.round} is atomic; no PR opened because unit failure(s) left the directive incomplete: ${failures.join("; ")}`,
      openIds: [...openStatements(graph)], obligations: [], unaddressedTargets: [...requiredTargets], dispatched: plans.length,
    };
  }
  if (outputs.length === 0) throw settled.find((r) => r.status === "rejected") ? (settled.find((r) => r.status === "rejected") as PromiseRejectedResult).reason : new Error("no unit returned");
  const submissions: UnitSubmission[] = outputs.map(({ plan, output }) => ({
    unit: plan.label, targets: plan.targets.map((t) => t.id), proseRole: plan.proseRole, output,
  }));
  const { pr, head: prHead } = await openPr({ store, base: head, round: args.round, submissions, journalLength: journal.length });
  // Directives are consumed when the round's PR merges (below, or `d0_vc pr merge`);
  // a closed PR leaves them pending so the next round sees them again.
  const baseGraph = await loadGraph(store, head);
  const roundDiff = diffGraphs(baseGraph, prHead);
  // A directive can require deleting an obsolete node.  Deletion is a completed
  // edit to that target, not an omission merely because the id is absent from the
  // resulting graph.
  const touched = new Set([...roundDiff.changed.map((c) => c.id), ...roundDiff.added, ...roundDiff.removed]);
  const changedFields = new Map(roundDiff.changed.map((c) => [c.id, new Set(c.fields)] as const));
  const blockedOutputIds = new Set([
    ...pr.dropped.map((d) => d.id),
    ...pr.units.flatMap((u) => u.rejected.map((r) => r.id)),
  ]);
  const unaddressedTargets = resolvedTargets.flatMap(([declaredId, graphId]) => {
    if (graphId === null || blockedOutputIds.has(graphId) || blockedOutputIds.has(declaredId)) return [declaredId];
    const receipts = submissions.flatMap((s) => {
      const receipt = outputTargetReceipt(s.output, declaredId);
      return receipt === null ? [] : [receipt];
    });
    if (receipts.length === 0) return [declaredId];
    // Reverse dependencies are a verified derived view; their typed rebuild edit
    // is intentionally diff-free.  Every other target must have landed bytes,
    // and metadata aliases must change their own field rather than a sibling.
    if (receipts.some((receipt) => receipt.diffFree)) return [];
    if (receipts.some((receipt) => receipt.removal) && roundDiff.removed.includes(graphId)) return [];
    const landedFields = changedFields.get(graphId);
    const landed = landedFields !== undefined && receipts.some((receipt) => [...receipt.fields].some((field) => landedFields.has(field)));
    return landed ? [] : [declaredId];
  });
  const rejectedNote = pr.units.flatMap((u) => u.rejected.map((r) => `${u.unit}: ${r.channel} ${r.id} — ${r.reason}`));
  const droppedNote = pr.dropped.map((d) => `${d.id} — ${d.reason}`);
  const notes = [
    ...(failures.length > 0 ? [`UNIT FAILURE(s) (their outputs are absent from this PR): ${failures.join("; ")}`] : []),
    ...(rejectedNote.length > 0 ? [`rejected items: ${rejectedNote.join("; ")}`] : []),
    ...(droppedNote.length > 0 ? [`dropped nodes: ${droppedNote.join("; ")}`] : []),
    ...(unaddressedTargets.length > 0 ? [`directive targets NOT addressed: ${unaddressedTargets.join(", ")}`] : []),
  ];
  const losses = prLosses(pr);
  if (pr.approval.length > 0 || losses.length > 0 || failures.length > 0 || unaddressedTargets.length > 0) {
    return {
      kind: "pr-open",
      message: `round ${args.round}: PR ${pr.id.slice(0, 12)} opened` +
        (pr.approval.length > 0 ? ` with ${pr.approval.length} item(s) needing approval (${pr.approval.map((a) => `${a.id} ${a.change}`).join(", ")})` : "") +
        (losses.length > 0 ? `; ${losses.length} solver item(s) DID NOT LAND and need the orchestrator to merge them by hand or close the PR (${losses.map((l) => l.id).join(", ")}; raw outputs: ${pr.inputs})` : "") + ". " +
        (unaddressedTargets.length > 0 ? `Required directive target(s) were not addressed (${unaddressedTargets.join(", ")}); do not merge or consume this directive. ` : "") +
        `Review: \`d0_vc.ts ${ctx.qid} ${ctx.specialization} pr show ${pr.id.slice(0, 12)}\`; then \`pr merge <id> --accept all|<ids> [--reject <ids>] --note "…"\` or \`pr close\`, and --resume.` +
        (notes.length > 0 ? `\n${notes.join("\n")}` : ""),
      pr, openIds: [], obligations: [], unaddressedTargets, dispatched: plans.length,
    };
  }
  const merged = await mergePr({
    store, ctx, pr,
    verdict: { accept: "all", note: `round ${args.round} auto-merge (nothing to approve)`, by: "pipeline" },
  });
  if (!merged.ok) {
    return {
      kind: "pr-open",
      message: `round ${args.round}: PR ${pr.id.slice(0, 12)} could not merge automatically: ` +
        (merged.unresolved.length > 0 ? merged.unresolved.map((u) => `${u.id} (${u.reason})`).join("; ") : merged.violations.map((v) => `${v.code}@${v.where}: ${v.message}`).join("; ")) +
        `. Resolve with \`d0_vc.ts ${ctx.qid} ${ctx.specialization} pr merge ${pr.id.slice(0, 12)} --accept all --keep-main <ids> --keep-pr <ids> --note "…"\` or a hand merge of core.json.`,
      pr, openIds: [], obligations: [], unaddressedTargets, dispatched: plans.length,
    };
  }
  state.flags.d0_directives_consumed = Math.max(consumed, journal.length);
  await rm(solveReuseReceiptsDir(ctx), { recursive: true, force: true });
  const after = merged.graph;
  const openIds = openStatements(after).filter((id) => statementBlob(after, id)?.body.kind !== "openendedquestion");
  const obligations = nodesOfType(after, "statement")
    .filter(({ id, blob }) => blob.body.resolved_by === undefined && blob.body.obligation !== undefined && blob.body.kind !== "openendedquestion" && touched.has(id))
    .map(({ id, blob }) => ({ id, what_is_open: blob.body.obligation!.what_is_open }));
  const summary = `round ${args.round}: PR ${pr.id.slice(0, 12)} merged as ${merged.commit.slice(0, 12)} ` +
    `(+${pr.summary.added.length} −${pr.summary.removed.length} ~${pr.summary.changed.length}` +
    `${merged.conflicts.length > 0 ? `, ${merged.conflicts.length} conflict(s) dropped` : ""})` +
    (notes.length > 0 ? `\n${notes.join("\n")}` : "");
  if (obligations.length > 0) {
    return { kind: "open-gap", message: `${summary}\nOPEN OBLIGATION(s): ${obligations.map((o) => `${o.id} — ${o.what_is_open}`).join("; ")}`, pr, openIds, obligations, unaddressedTargets, dispatched: plans.length };
  }
  if (openIds.length > 0) {
    return { kind: "incomplete", message: `${summary}\nstill open: ${openIds.join(", ")}`, pr, openIds, obligations, unaddressedTargets, dispatched: plans.length };
  }
  delete state.flags.redo_math_witness;
  return { kind: "clean", message: `${summary}\nevery statement is proved, cited, or an acknowledged open question`, pr, openIds, obligations, unaddressedTargets, dispatched: plans.length };
}

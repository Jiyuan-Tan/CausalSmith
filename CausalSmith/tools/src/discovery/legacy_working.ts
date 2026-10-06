// READ-ONLY view of the retired `d0_working.json` cursor.
//
// The versioned graph store (vcs/) replaced the proto + working stores on
// 2026-09-06. This module keeps the cursor's shape and a tolerant loader so an
// existing run can be converted (vcs/convert.ts renders it through `assembleCore`
// into the store's initial commit). Nothing writes this file any more.
import { existsSync } from "node:fs";
import { readFile } from "node:fs/promises";
import { artifactPath } from "../paths.js";
import type { PipelineContext } from "../types.js";
import type { CoreStatement } from "./core/schema.js";
import { repairLatexStringsDeep } from "./core/latex_serialization.js";
import type { ProseOverlay } from "./core/assemble.js";

/** The content a member statement was last solved against — change ⟹ invalidate. */
export interface MemberSnapshot {
  stmt: string; // the member's own statement text
  /** Edge set at solve time. PROVENANCE ONLY — no longer part of validity: a proof's
   *  soundness rests on its statement plus the CONTENT it was solved against (`defs`/
   *  `assumptions` below, which are captured post-auto-wiring and therefore cover every
   *  def/ass the proof text cites), not on the edge list. Comparing the edge set made a
   *  pure dependency rewire re-derive a byte-identical theorem (observed ≥3× on one
   *  flagship: "dep change alone triggers re-derivation via snapshot invalidation").
   *  Upstream STATEMENT changes are handled separately by `computeValidNodes`'s
   *  staleness propagation over the CURRENT edges. */
  depends_on?: string[];
  defs: Record<string, string>; // referenced def id → construction
  assumptions: Record<string, string>; // referenced assumption id → condition
}

/** One proved node carried across rounds. Spec statements store just proof+snapshot;
 *  agent-added lemmas additionally store their `node` (they are not in the proto) and
 *  the `owner` group label that authored them. Frozen overlays may also carry an
 *  owner when a directed repair assigns a durable semantic owner to a published
 *  node that is not itself a later dispatch root. */
// A record's `node` is not an optional extra — it is the KIND distinction, and reading
// it without establishing which kind you hold is a live source of wrong answers. A
// frozen proto member's statement is defined in `proto_core.json`, so its record carries
// no `node`; an agent-authored statement is defined NOWHERE ELSE, so its record must.
// Written as an optional field, `rec.node.status` compiled fine and silently returned
// `undefined` for every frozen member — which counted six PROVED nodes as unproved and
// sent a real run down the wrong diagnosis (PIPELINE_NOTES 2026-07-19). As a union, that
// read is a compile error and the guard is forced.
interface ProtoMemberProof {
  proof_tex: string;
  snapshot: MemberSnapshot;
  node?: undefined;
  owner?: string;
  partial?: boolean;
  /** Never set on a frozen member: its render comes from the proto text, so there
   *  is nothing to shelve. Typed `undefined` so a union read is legal. */
  shelved?: undefined;
}
interface AgentNodeProof {
  proof_tex: string;
  snapshot: MemberSnapshot;
  node: CoreStatement;
  owner?: string;
  /** True when proof_tex is only a PARTIAL result (the node has an open obligation).
   *  A partial is carried forward as "extend, don't restart" context but is NOT a valid
   *  proof for reuse/discharge — the node stays open until fully proved. */
  partial?: boolean;
  /** A partial carried as debt that is deliberately NOT part of the published paper
   *  this round (e.g. a stale helper lemma that no live result consumes yet — the
   *  frontier logic re-opens it only when a root pulls it back in). `assembleCore`
   *  skips shelved records; a published partial (`shelved` absent/false) renders as
   *  an open `to-prove` target with its best-partial bytes. Meaningful only with
   *  `partial: true`. */
  shelved?: boolean;
}
export type SolvedMember = ProtoMemberProof | AgentNodeProof;

/** Durable D0-boundary replacement of a frozen OEQ by its answer theorem. */
export interface ResolvedOeq {
  theorem_id: string;
  /** Frozen OEQ claim/prose/dependency fingerprint at the moment it was answered. */
  source_fingerprint: string;
}

/** Persistent incremental state, parallel to the assembled core.json. */
export interface WorkingState {
  round: number;
  /** Number of parsed escalation-log entries delivered to a solver round.
   *  A newly appended standalone directive must invalidate reuse once so it
   *  reaches a real dispatch; after that, ordinary incremental reuse resumes. */
  escalation_entries_consumed?: number;
  /**
   * D-1.2 proposal revision that authored the frozen proto used for these
   * proofs.  Ordinary D0 corrections keep this key and use member-level
   * invalidation; a source rewind increments it and must rebuild from scratch
   * so removed source claims cannot survive as carried agent-added nodes.
   */
  proposal_revision?: string;
  /**
   * GLOBAL symbol basis these proofs were solved against: symbol name → hex
   * fingerprint of the symbol's SEMANTIC fields (`type`/`space`/`sig`/`def`/`role`/`ref`;
   * only `refs` is excluded — see `symbolBasis` for why each field is in or out).
   * Symbols are not `depends_on` edges (`sym` is absent
   * from `NODE_KINDS`) and appear in NO `MemberSnapshot` field, so an APPLIED symbol
   * re-definition (e.g. narrowing a space from ℝ to [0,1]) changed what every
   * statement quoting it CLAIMS while every statement's text stayed byte-identical —
   * `computeValidNodes` saw nothing and published proofs of materially different
   * claims as current. The pre-store solve merge already treated a PROPOSED symbol edit as
   * globally proof-invalidating; this was the applied-case counterpart. Values are hex hashes
   * so `repairLatexStringsDeep` (applied to the whole cursor on load) cannot mutate
   * them out from under the comparison.
   *
   * The basis is global; the INVALIDATION it triggers is scoped per node by the
   * declared `free_symbols` closure (`declaredSymbolScope`), so a symbol edit reopens
   * the statements that declare it and their dependents rather than the whole paper.
   * A node with no declaration still reopens on any change.
   */
  symbol_basis?: Record<string, string>;
  /** Every proved node (spec statements + agent-added lemmas), keyed by id. */
  solved: Record<string, SolvedMember>;
  /** Orchestrator-authorized proof reopen receipts. Kept in the working cursor so
   *  the audit record and the `partial` mutations land in the same atomic write. */
  proof_reopens?: Array<{
    node_id: string;
    statement_revision: string;
    proposal_revision: string;
    round: number;
    reason: string;
    reopened_ids: string[];
    recorded_at: string;
  }>;
  /**
   * This round's proposal payload, adjudicated as a unit.
   *
   * Previously five sibling `proposed_*.json` files with no tie between them, so each
   * consumer read its own subset and the subsets disagreed (apply never read the
   * proofs; the D0.5 reviewers read none of it). The payload has exactly this state's
   * lifecycle — per round, cleared on apply, invalidated when D-1.2 advances the
   * proposal revision — so it lives here, and the closure invariant
   * `ids(core) ⊆ ids(proto) ∪ ids(working)` becomes structural.
   *
   * Read only by `vcs/convert.ts`, which re-parses it with the solve payload schema and
   * carries it into the store as a legacy PR at migration. Typed structurally here so this
   * module does not import those schemas.
   */
  proposals?: {
    /** Exact assembled-core revision persisted with this adjudication packet. */
    basis_revision?: string;
    statements: unknown[];
    definitions: unknown[];
    assumptions: unknown[];
    coreEdits: unknown[];
    /** `argues_proposed`: the proof argues the same-round PROPOSED statement text for
     *  this id (see solve/proposals.ts `ProvisionalProof`); apply promotes it when that
     *  basis materializes. Kept structural here to avoid an // import cycle. */
    proofs: Array<{ id: string; proof_tex: string; argues_proposed?: boolean }>;
    /** Speculative complete records for every changed or newly introduced id.
     * The durable `solved` catalog keeps its byte-faithful pre-merge image until
     * apply; this reviewed carrier supplies the postimage needed for promotion. */
    recordPostimages?: Record<string, SolvedMember>;
    /** Speculative resolved-OEQ relation changes paired with recordPostimages. */
    resolvedOeqPostimages?: Record<string, ResolvedOeq | string | null>;
    /** Exact cited-source receipts reviewed with this same atomic postimage. */
    citationRevalidations?: CoreStatement[];
  };
  /** Independently adjudicated exact edits remain authoritative across any number
   * of solve regenerations and are cleared only by a successful atomic apply or an
   * explicit, content-addressed cancellation journal event. */
  required_core_edit_mandates?: unknown[];
  /**
   * Solved OEQs are not ordinary added theorems: their source `oeq:` node still
   * lives in the frozen proto used to rebuild later D0 rounds. This map makes
   * the D0-boundary replacement durable; the answer theorem itself is in `solved`.
   */
  /** String values from the first implementation are recognized and safely re-solved. */
  resolved_oeqs?: Record<string, ResolvedOeq | string>;
  /** OEQs deliberately retained as residual questions. Values fingerprint the
   * exact mathematical question; a claim/dependency edit or exact-target directive
   * unlocks it, while ordinary D replay does not pay a solver to answer it again. */
  sealed_open_oeqs?: Record<string, string>;
  /**
   * Cumulative directive-authorized prose overlay (Phase 1 of the 2026-07-30
   * store consolidation). `prose_updates` used to be applied to BOTH core.json
   * and the frozen proto mid-round (`applyProseUpdates` — the only
   * non-transactional proto writer); now the round merges them here and
   * `assembleCore` applies the overlay at render time. Absent on pre-migration
   * cursors (their prose is already baked into the proto by the old dual write).
   */
  prose_overlay?: ProseOverlay;
  /**
   * Proto-resident lemmas removed from the published paper by the maximality-
   * checkpoint orphan prune. The proto still defines them (only an orchestrator
   * proto edit deletes them there), so the pure render needs this durable filter
   * — without it every re-assembly would resurrect the pruned node. An entry
   * whose id later leaves the proto (the orchestrator applied the edit) is inert.
   */
  pruned_proto_orphans?: string[];
  /**
   * Store-format generation. `2` = written by post-consolidation code (core.json
   * is a pure render of (proto, working)); absent = pre-migration writer. The
   * replay harness keys its assemble-equivalence severity on this: divergence is
   * report-only on legacy cursors, a hard failure on format ≥ 2 (unless a D0.R
   * in-place edit is on record for the run).
   */
  store_format?: number;
}


export function workingPath(ctx: PipelineContext): string {
  return artifactPath(ctx.repoRoot, ctx.qid, "discovery", "d0_working.json", [`${ctx.qid}_d0_working.json`]);
}

export async function loadWorkingState(ctx: PipelineContext): Promise<WorkingState | null> {
  const p = workingPath(ctx);
  if (!existsSync(p)) return null;
  try {
    const working = JSON.parse(await readFile(p, "utf8")) as WorkingState;
    repairLatexStringsDeep(working, new Set(["source_fingerprint", "required_core_edit_mandates"]));
    return working;
  } catch (err) {
    throw new Error(`D0 working cursor is corrupt at ${p}: ${err instanceof Error ? err.message : String(err)}`);
  }
}

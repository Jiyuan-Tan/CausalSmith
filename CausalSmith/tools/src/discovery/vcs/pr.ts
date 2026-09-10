// The versioned theorem graph: a solver round as a pull request.
//
//   base ──(unit A output)──► head_A ─┐
//   base ──(unit B output)──► head_B ─┼─ fold (node-level 3-way, conflicts dropped) ─► head
//                                      │
//   approval items = diff(base, head) restricted to what needs an adjudicator
//   merge: head' = head − rejected items; 3-way onto main; commit [main, head']
//
// `applyUnitOutput` is the ONLY place solver JSON becomes graph state. It never
// asks the solver to echo what it was shown: the branch's parent is the basis. An
// item that cannot be applied is rejected with a reason and the rest still lands.
// Whatever lands, a proof is stored with the basis it was written against, so a
// rejected or conflicting claim change simply leaves its proof stale (to-prove).
import { existsSync } from "node:fs";
import { readFile, readdir, rm } from "node:fs/promises";
import path from "node:path";
import { isDeepStrictEqual } from "node:util";
import { writeJsonAtomic } from "../../shared/json_atomic.js";
import { canonicalClaimText, truncateTexSafe } from "../../shared/tex_text.js";
import { extractNodeRefs } from "../core/node_ids.js";
import { normalizeSymbol } from "../core/symbol_names.js";
import { retargetDeletedDependency } from "../core/oeq_edges.js";
import type { CoreStatement } from "../core/schema.js";
import type { SolveUnitOutput } from "../solve/schemas.js";
import { checkGraph, type Violation } from "./checks.js";
import { commitGraph, publishCore } from "./commit.js";
import { diffGraphs, isEmptyDiff, loadGraph, nodesOfType, statementBlob, type Graph, type GraphDiff } from "./graph.js";
import {
  META_ID,
  bibNodeId,
  blobId,
  contentKey,
  nodeTypeOf,
  symbolNodeId,
  type NodeBlob,
  type NodeId,
  type StatementBody,
} from "./node.js";
import { normalizeGraph, renderCore } from "./render.js";
import { MAIN_REF, VcsStore, type Tree } from "./store.js";
import { computeBasis, deriveStatus, proofCoversCurrentClosure } from "./validity.js";
import { narrowingWarnings } from "../narrowing_heuristics.js";
import type { PipelineContext } from "../../types.js";

// -- types ---------------------------------------------------------------------------

export interface UnitSubmission {
  unit: string;
  /** Statement ids this unit was dispatched to solve. */
  targets: string[];
  /** Statement ids other units of the same round were dispatched to solve: this
   *  unit may cite them but never change, prove, delete or annotate them. */
  siblingTargets?: string[];
  /** Deterministic paper-prose lease. Legacy multi-unit inputs default to omit. */
  proseRole?: "owner" | "omit";
  output: SolveUnitOutput;
}

/** Central prose-lease enforcement used by both live rounds and stored PR replay. */
export function scopeSubmissionProse(submission: UnitSubmission, proseRole: "owner" | "omit"): UnitSubmission {
  const output = submission.output;
  if (output.prose_updates === undefined) return { ...submission, proseRole };
  if (proseRole === "omit") return { ...submission, proseRole, output: { ...output, prose_updates: undefined } };
  const owned = new Set(submission.targets);
  for (const statement of output.added_lemmas) owned.add(statement.id);
  for (const resolved of output.resolved_oeqs) owned.add(resolved.theorem.id);
  return {
    ...submission,
    proseRole,
    output: {
      ...output,
      prose_updates: {
        ...output.prose_updates,
        statement_notes: output.prose_updates.statement_notes.filter((note) => owned.has(note.id)),
      },
    },
  };
}

export interface RejectedItem {
  unit: string;
  channel: string;
  id: string;
  reason: string;
}

/** What an accepted OEQ resolution rewired, recorded when it is applied: the symbols
 *  the unit retargeted from the question to the answer, and the consumers whose
 *  `depends_on` normalization remapped the same way. Lets a later repair undo exactly
 *  those edges if the answer stops standing, without refolding the round. */
export interface UnitResolution {
  sourceId: NodeId;
  answerId: NodeId;
  rewiredConsumers: NodeId[];
  rewiredSymbols: NodeId[];
}

export interface UnitHead {
  unit: string;
  targets: string[];
  graph: Graph;
  rejected: RejectedItem[];
  /** Solver-stated reasons per node, for the review packet. */
  reasons: Record<NodeId, string[]>;
  resolutions: UnitResolution[];
}

export interface ApprovalItem {
  id: NodeId;
  change: "added" | "removed" | "changed";
  fields: string[];
  content: boolean;
  reasons: string[];
}

export interface PrRecord {
  /** The head commit id (pre-adjudication). Also the PR's name. */
  id: string;
  base: string;
  round: number;
  created: string;
  units: Array<{ unit: string; targets: string[]; head: string; rejected: RejectedItem[] }>;
  /** Nodes whose change was dropped at fold or check time (conflict / violation). */
  dropped: Array<{ unit?: string; id: NodeId; reason: string }>;
  /** Items an adjudicator must accept or reject. Empty ⇒ auto-merged. */
  approval: ApprovalItem[];
  /** Diff summary for humans. */
  summary: { added: NodeId[]; removed: NodeId[]; changed: NodeId[] };
  status: "open" | "merged" | "closed";
  verdict?: { accepted: NodeId[]; rejected: NodeId[]; note: string; at: string; by: string };
  merge_commit?: string;
  closed_note?: string;
  /** Escalation-journal length the round was shown; a merge advances the cursor to it. */
  journal_length?: number;
  /** Every unit's raw validated output, kept beside the record so the round can be
   *  replayed against a repaired main (`pr reapply`) and a dropped or rejected item
   *  merged by hand from the bytes the solver actually wrote. */
  inputs?: string;
  /** Set when this PR is a replay of an earlier PR's raw inputs. */
  reapplied_from?: string;
  /** The PR carries paper-wide prose authored against exactly `base`. */
  has_leased_prose?: boolean;
  /** OEQ resolutions on the head and what they rewired, so a merge that stales an
   *  answer can restore the question's edges without replaying the round. */
  resolutions?: ResolutionProvenance[];
}

/** Items the solver produced that did not land on the PR head: fold conflicts,
 *  check-driven reverts, and converter rejections. Never merged without the orchestrator deciding. */
export function prLosses(pr: PrRecord): Array<{ id: string; reason: string }> {
  return [
    ...pr.dropped.map((d) => ({ id: d.id, reason: `${d.unit ? `[${d.unit}] ` : ""}dropped: ${d.reason}` })),
    ...pr.units.flatMap((u) => u.rejected.map((r) => ({ id: r.id, reason: `[${u.unit}] ${r.channel} rejected: ${r.reason}` }))),
  ];
}

/** Parse a solver's freeform `standard_or_novel` tag into a gate-valid assumption tag
 *  (exactly one of {standard, novel}, G6). Defaults to `novel` when no bibliography KEY
 *  is recognized — safe, since `novel` needs no cite resolution; reclassified at review. */
export function parseAssumptionTag(
  s: string | undefined,
  bibKeys: string[],
): { standard: { name: string; cite: string } } | { novel: { flag: true; justification: string } } {
  const text = (s ?? "").trim();
  if (/^standard/i.test(text)) {
    const key = bibKeys.find((k) =>
      new RegExp(`(?<![A-Za-z0-9])${k.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}(?![A-Za-z0-9])`).test(text),
    );
    if (key) {
      const name = truncateTexSafe(text.replace(/^standard:?\s*/i, ""), 80);
      return { standard: { name: name || "standard condition", cite: key } };
    }
  }
  return { novel: { flag: true, justification: text || "solver-proposed (pending approval)" } };
}

// -- graph editing helpers -----------------------------------------------------------

class Draft {
  nodes: Map<NodeId, NodeBlob>;
  tree: Tree;
  constructor(base: Graph) {
    this.nodes = new Map(base.nodes);
    this.tree = { ...base.tree };
  }
  graph(): Graph {
    return { tree: this.tree, nodes: this.nodes };
  }
  get(id: NodeId): NodeBlob | undefined {
    return this.nodes.get(id);
  }
  live(id: NodeId): Extract<NodeBlob, { node_type: "statement" }> | undefined {
    const blob = this.nodes.get(id);
    return blob?.node_type === "statement" && blob.body.resolved_by === undefined ? blob : undefined;
  }
  set(id: NodeId, blob: NodeBlob): void {
    const pos = this.tree[id]?.pos ?? this.nextPos(blob.node_type);
    this.nodes.set(id, blob);
    this.tree[id] = { blob: blobId(blob), pos };
  }
  delete(id: NodeId): void {
    this.nodes.delete(id);
    delete this.tree[id];
  }
  private nextPos(type: NodeBlob["node_type"]): number {
    let max = -1;
    for (const [id, blob] of this.nodes) if (blob.node_type === type) max = Math.max(max, this.tree[id]?.pos ?? -1);
    return max + 1;
  }
}

const sameClaim = (a: string, b: string): boolean => canonicalClaimText(a) === canonicalClaimText(b);

function statementBodyFromInput(input: CoreStatement): StatementBody {
  const { status: _status, ...rest } = input;
  const body: StatementBody = { ...rest };
  if ((body.proof_tex ?? "").trim().length === 0) delete body.proof_tex;
  return body;
}

// -- solver output → unit head ---------------------------------------------------------

export function applyUnitOutput(base: Graph, sub: UnitSubmission): UnitHead {
  const d = new Draft(base);
  const rejected: RejectedItem[] = [];
  const reasons: Record<NodeId, string[]> = {};
  const reject = (channel: string, id: string, reason: string): void => { rejected.push({ unit: sub.unit, channel, id, reason }); };
  const note = (id: NodeId, reason: string | undefined): void => {
    if (reason === undefined || reason.trim().length === 0) return;
    (reasons[id] ??= []).push(reason.trim());
  };
  const targets = new Set(sub.targets);
  const siblings = new Set((sub.siblingTargets ?? []).filter((id) => !targets.has(id)));
  const ownedStatement = (id: NodeId): boolean => !siblings.has(id);
  const o = sub.output;
  const provedThisRound = new Set<NodeId>();
  const addedThisUnit = new Set<NodeId>();
  const resolutionAnswers = new Map<NodeId, NodeBlob>();
  const resolutions: UnitResolution[] = [];

  const setProof = (id: NodeId, proofTex: string, channel: string): void => {
    const blob = d.live(id);
    if (blob === undefined) { reject(channel, id, "no live statement with this id"); return; }
    if (!targets.has(id) && !addedThisUnit.has(id)) { reject(channel, id, "not a target of this unit"); return; }
    if (proofTex.trim().length === 0) { reject(channel, id, "empty proof"); return; }
    const { obligation: _o, proof_basis: _b, ...body } = blob.body;
    d.set(id, { node_type: "statement", body: { ...body, proof_tex: proofTex } });
    provedThisRound.add(id);
  };

  // 1. Answered questions: the answer is a new theorem; the question keeps a tombstone.
  for (const r of o.resolved_oeqs) {
    const q = d.live(r.source_id);
    if (q === undefined || q.body.kind !== "openendedquestion" || q.body.resolved_by !== undefined) { reject("resolved_oeqs", r.source_id, "not a live open question"); continue; }
    if (!targets.has(r.source_id)) { reject("resolved_oeqs", r.source_id, "not a target of this unit"); continue; }
    if (d.get(r.theorem.id) !== undefined) { reject("resolved_oeqs", r.source_id, `answer id '${r.theorem.id}' already exists`); continue; }
    const body = statementBodyFromInput(r.theorem);
    d.set(r.theorem.id, { node_type: "statement", body });
    resolutionAnswers.set(r.theorem.id, { node_type: "statement", body });
    addedThisUnit.add(r.theorem.id);
    if (body.proof_tex !== undefined) provedThisRound.add(r.theorem.id);
    d.set(r.source_id, { node_type: "statement", body: { ...q.body, resolved_by: r.theorem.id } });
    // Retargeting a symbol is a proposed content change, not a normalization side
    // effect: an adjudicator can therefore accept or reject it authoritatively.
    const rewiredSymbols: NodeId[] = [];
    for (const { id, blob } of nodesOfType(d.graph(), "symbol")) {
      if (blob.body.ref !== r.source_id) continue;
      d.set(id, { node_type: "symbol", body: { ...blob.body, ref: r.theorem.id } });
      rewiredSymbols.push(id);
    }
    resolutions.push({ sourceId: r.source_id, answerId: r.theorem.id, rewiredConsumers: [], rewiredSymbols });
  }

  // 2. Added statements (new nodes; a re-emitted existing node is a proof / revalidation).
  for (const s of o.added_lemmas) {
    const existing = d.get(s.id);
    if (existing === undefined) {
      const body = statementBodyFromInput(s);
      if (body.source !== undefined) delete body.proof_tex;
      d.set(s.id, { node_type: "statement", body });
      addedThisUnit.add(s.id);
      if (body.proof_tex !== undefined) provedThisRound.add(s.id);
      continue;
    }
    if (existing.node_type !== "statement") { reject("added_lemmas", s.id, "id belongs to a non-statement node"); continue; }
    if (existing.body.resolved_by !== undefined) { reject("added_lemmas", s.id, "id is a resolved question"); continue; }
    if (!ownedStatement(s.id)) { reject("added_lemmas", s.id, "a sibling unit's target: cite it, do not re-emit it"); continue; }
    if (!targets.has(s.id)) { reject("added_lemmas", s.id, "existing statement is not a target of this unit"); continue; }
    if (!sameClaim(existing.body.statement, s.statement)) {
      reject("added_lemmas", s.id, "id exists with a different claim (claims change only through proposed_statement_changes)");
      continue;
    }
    if (s.source !== undefined) {
      const { proof_basis: _b, obligation: _o, ...body } = existing.body;
      d.set(s.id, { node_type: "statement", body: { ...body, source: s.source } });
    } else if ((s.proof_tex ?? "").trim().length > 0) {
      setProof(s.id, s.proof_tex!, "added_lemmas");
    } else reject("added_lemmas", s.id, "re-emitted existing node without proof or source");
  }

  // 3. Proposed assumptions.
  const bibKeys = (): string[] => nodesOfType(d.graph(), "bib").map((b) => b.blob.body.key);
  for (const a of o.proposed_assumptions) {
    if (d.get(a.id) !== undefined) { reject("proposed_assumptions", a.id, "id already exists"); continue; }
    const tag = parseAssumptionTag(a.standard_or_novel, bibKeys());
    d.set(a.id, { node_type: "assumption", body: { id: a.id, condition: a.condition, free_symbols: a.free_symbols ?? [], ...tag } });
    note(a.id, `${a.reason} (not crux: ${a.not_crux})`);
  }

  // 4. Typed core edits.
  for (const e of o.proposed_core_edits) {
    switch (e.kind) {
      case "assumption-replace": {
        if (d.get(e.id)?.node_type !== "assumption") { reject(e.kind, e.id, "no such assumption"); break; }
        const { used_by: _u, ...body } = e.proposed;
        d.set(e.id, { node_type: "assumption", body: { ...body, id: e.id } });
        note(e.id, e.reason);
        break;
      }
      case "assumption-delete":
      case "definition-delete": {
        const type = e.kind === "assumption-delete" ? "assumption" : "definition";
        if (d.get(e.id)?.node_type !== type) { reject(e.kind, e.id, `no such ${type}`); break; }
        d.delete(e.id);
        note(e.id, e.reason);
        break;
      }
      case "definition-add": {
        if (d.get(e.id) !== undefined) { reject(e.kind, e.id, "id already exists"); break; }
        d.set(e.id, { node_type: "definition", body: { ...e.proposed, id: e.id } });
        note(e.id, e.reason);
        break;
      }
      case "definition-replace": {
        if (d.get(e.id)?.node_type !== "definition") { reject(e.kind, e.id, "no such definition"); break; }
        d.set(e.id, { node_type: "definition", body: { ...e.proposed, id: e.id } });
        note(e.id, e.reason);
        break;
      }
      case "statement-replace": {
        const existing = d.live(e.id);
        if (existing === undefined) { reject(e.kind, e.id, "no live statement with this id"); break; }
        if (!ownedStatement(e.id)) { reject(e.kind, e.id, "a sibling unit's target"); break; }
        if (!targets.has(e.id)) { reject(e.kind, e.id, "not a target of this unit"); break; }
        const { partial_result: _pr, ...proposed } = e.proposed as CoreStatement & { partial_result?: string };
        const incoming = statementBodyFromInput(proposed);
        delete incoming.proof_tex;
        const paired = o.proposed_statement_changes.find((c) => c.id === e.id);
        const claimTarget = paired?.proposed ?? existing.body.statement;
        if (!sameClaim(incoming.statement, claimTarget)) {
          reject(e.kind, e.id, paired
            ? "statement text differs from the paired proposed_statement_changes item"
            : "claim text changes only through proposed_statement_changes");
          break;
        }
        const body: StatementBody = { ...incoming, statement: existing.body.statement };
        if (existing.body.proof_tex !== undefined) body.proof_tex = existing.body.proof_tex;
        if (existing.body.proof_basis !== undefined) body.proof_basis = existing.body.proof_basis;
        if (existing.body.obligation !== undefined) body.obligation = existing.body.obligation;
        // Prose is exclusively governed by the round's explicit prose lease.
        // Typed mathematical replacement cannot smuggle snapshot-derived framing.
        for (const field of ["justification", "gap", "consumer"] as const) {
          if (existing.body[field] !== undefined) body[field] = existing.body[field];
          else delete body[field];
        }
        d.set(e.id, { node_type: "statement", body });
        note(e.id, e.reason);
        break;
      }
      case "statement-delete": {
        if (d.live(e.id) === undefined) { reject(e.kind, e.id, "no live statement with this id"); break; }
        if (!ownedStatement(e.id)) { reject(e.kind, e.id, "a sibling unit's target"); break; }
        if (!targets.has(e.id)) { reject(e.kind, e.id, "not a target of this unit"); break; }
        if (e.replacement_id !== undefined && d.live(e.replacement_id) === undefined) { reject(e.kind, e.id, `replacement '${e.replacement_id}' is not a live statement`); break; }
        d.delete(e.id);
        for (const { id, blob } of nodesOfType(d.graph(), "statement")) {
          const deps = retargetDeletedDependency(id, blob.body.depends_on ?? [], e.id, e.replacement_id);
          if (JSON.stringify(deps) !== JSON.stringify(blob.body.depends_on ?? [])) {
            d.set(id, { node_type: "statement", body: { ...blob.body, depends_on: deps } });
          }
        }
        note(e.id, e.reason);
        break;
      }
      case "bibliography-replace": {
        d.set(bibNodeId(e.key), { node_type: "bib", body: { ...e.proposed, key: e.key } });
        note(bibNodeId(e.key), e.reason);
        break;
      }
      case "target-estimand-replace":
      case "estimand-functional-replace":
      case "comparator-promise-table-replace": {
        const meta = d.get(META_ID);
        if (meta?.node_type !== "meta") { reject(e.kind, e.id, "no meta node"); break; }
        const body = { ...meta.body };
        if (e.kind === "target-estimand-replace") body.target_estimand = e.proposed;
        else if (e.kind === "estimand-functional-replace") body.estimand_functional = e.proposed;
        else {
          const field = body.comparator_promise_table === undefined && body.comparator_promises !== undefined
            ? "comparator_promises" : "comparator_promise_table";
          body[field] = e.proposed;
        }
        d.set(META_ID, { node_type: "meta", body });
        note(META_ID, `${e.kind}: ${e.reason}`);
        break;
      }
      case "symbol-add": {
        const id = symbolNodeId(e.name);
        if (d.get(id) !== undefined) { reject(e.kind, id, "symbol already exists"); break; }
        if (e.proposed.name !== e.name) { reject(e.kind, id, "proposed.name differs from name"); break; }
        d.set(id, { node_type: "symbol", body: e.proposed });
        note(id, e.reason);
        break;
      }
      case "symbol-replace": {
        const id = symbolNodeId(e.name);
        if (d.get(id)?.node_type !== "symbol") { reject(e.kind, id, "no such symbol"); break; }
        if (e.proposed.name !== e.name) { reject(e.kind, id, "a symbol cannot be renamed in place (delete + add)"); break; }
        d.set(id, { node_type: "symbol", body: e.proposed });
        note(id, e.reason);
        break;
      }
      case "symbol-delete": {
        const id = symbolNodeId(e.name);
        if (d.get(id)?.node_type !== "symbol") { reject(e.kind, id, "no such symbol"); break; }
        d.delete(id);
        note(id, e.reason);
        break;
      }
      case "rebuild-reverse-dependencies":
        break; // derived at render; nothing to do
    }
  }

  // 5. Definition corrections (construction only). A same-round definition-replace
  //    already applied must agree; otherwise the correction is the conflicting item.
  for (const c of o.proposed_definition_changes) {
    const def = d.get(c.id);
    if (def?.node_type !== "definition") { reject("proposed_definition_changes", c.id, "no such definition"); continue; }
    const baseDef = base.nodes.get(c.id);
    const baseConstruction = baseDef?.node_type === "definition" ? baseDef.body.construction : undefined;
    if (def.body.construction !== baseConstruction && !sameClaim(def.body.construction, c.proposed)) {
      reject("proposed_definition_changes", c.id, "a definition-replace in the same bundle carries a different construction");
      continue;
    }
    d.set(c.id, { node_type: "definition", body: { ...def.body, construction: c.proposed } });
    note(c.id, `${c.direction}: ${c.reason}`);
  }

  // 6. Claim changes.
  for (const c of o.proposed_statement_changes) {
    const existing = d.live(c.id);
    if (existing === undefined) { reject("proposed_statement_changes", c.id, "no live statement with this id"); continue; }
    if (!ownedStatement(c.id)) { reject("proposed_statement_changes", c.id, "a sibling unit's target"); continue; }
    if (!targets.has(c.id)) { reject("proposed_statement_changes", c.id, "not a target of this unit"); continue; }
    d.set(c.id, { node_type: "statement", body: { ...existing.body, statement: c.proposed } });
    note(c.id, `${c.direction}: ${c.reason}`);
  }

  // 7. Open obligations (before proofs: a proof of the same node clears it).
  for (const ob of o.open_obligations) {
    const existing = d.live(ob.node_id);
    if (existing === undefined) { reject("open_obligations", ob.node_id, "no live statement with this id"); continue; }
    if (!targets.has(ob.node_id) && !addedThisUnit.has(ob.node_id)) { reject("open_obligations", ob.node_id, "not a target of this unit"); continue; }
    const obligation = {
      what_is_open: ob.what_is_open, obstruction: ob.obstruction, attempted: ob.attempted,
      ...(ob.partial_result !== undefined && ob.partial_result.length > 0 ? { partial_result: ob.partial_result } : {}),
    };
    d.set(ob.node_id, { node_type: "statement", body: { ...existing.body, obligation } });
  }

  // 8. Proofs.
  for (const p of o.proofs) setProof(p.id, p.proof_tex, "proofs");

  // 9. Prose.
  if (o.prose_updates !== undefined) {
    const meta = d.get(META_ID);
    if (meta?.node_type === "meta") {
      const body = { ...meta.body };
      const u = o.prose_updates;
      for (const f of ["tldr", "related_work", "interpretation", "technical_internal_limitation", "honest_scope"] as const) {
        if (u[f] !== undefined) body[f] = u[f];
      }
      if (u.project_justification !== undefined) {
        body.project_justification = { ...((body.project_justification as Record<string, unknown> | undefined) ?? {}), ...u.project_justification };
      }
      if (u.sampling_model !== undefined) {
        body.sampling_model = { ...((body.sampling_model as Record<string, unknown> | undefined) ?? {}), ...u.sampling_model };
      }
      d.set(META_ID, { node_type: "meta", body });
    }
    for (const n of o.prose_updates.statement_notes ?? []) {
      const existing = d.live(n.id);
      if (existing === undefined) { reject("prose_updates", n.id, "no live statement with this id"); continue; }
      if (!ownedStatement(n.id)) { reject("prose_updates", n.id, "a sibling unit's target"); continue; }
      if (!targets.has(n.id) && !addedThisUnit.has(n.id)) {
        reject("prose_updates", n.id, "not a target or statement created by this unit");
        continue;
      }
      const body = { ...existing.body };
      for (const f of ["justification", "gap", "consumer"] as const) if (n[f] !== undefined) body[f] = n[f];
      d.set(n.id, { node_type: "statement", body });
    }
  }

  // A resolution answer is one atomic payload. Other channels in the same worker
  // output cannot silently overwrite its proof, dependencies, obligation or prose.
  for (const [id, answer] of resolutionAnswers) {
    const current = d.get(id);
    if (current !== undefined && blobId(current) === blobId(answer)) continue;
    reject("resolved_oeqs", id, "resolution answer was also changed by another output channel; kept the embedded answer payload");
    d.set(id, answer);
  }

  // 10. Normalize, then stamp a basis on every proof written this round.
  const unnormalized = d.graph();
  let graph = normalizeGraph(unnormalized);
  // Consumers normalization remapped from a resolved question to its answer.
  for (const resolution of resolutions) {
    if (statementBlob(graph, resolution.sourceId)?.body.resolved_by !== resolution.answerId) continue;
    resolution.rewiredConsumers = nodesOfType(graph, "statement")
      .filter(({ id, blob }) => id !== resolution.answerId &&
        (blob.body.depends_on ?? []).includes(resolution.answerId) &&
        (statementBlob(unnormalized, id)?.body.depends_on ?? []).includes(resolution.sourceId))
      .map(({ id }) => id);
  }
  if (provedThisRound.size > 0) {
    const nodes = new Map(graph.nodes);
    const tree = { ...graph.tree };
    for (const id of provedThisRound) {
      const blob = statementBlob(graph, id);
      if (blob === undefined || blob.body.proof_tex === undefined) continue;
      const stamped: NodeBlob = { node_type: "statement", body: { ...blob.body, proof_basis: computeBasis(graph, id) } };
      nodes.set(id, stamped);
      tree[id] = { ...tree[id], blob: blobId(stamped) };
    }
    graph = { tree, nodes };
  }
  return {
    unit: sub.unit, targets: sub.targets, graph, rejected, reasons,
    resolutions: resolutions.filter((r) => statementBlob(graph, r.sourceId)?.body.resolved_by === r.answerId),
  };
}

// -- fold unit heads onto the base --------------------------------------------------------

export interface FoldResult {
  graph: Graph;
  conflicts: Array<{ unit: string; id: NodeId; reason: string }>;
}

/** Node-level three-way merge of each unit head onto the running result, in order.
 *  A node two units changed differently is a conflict: the later unit's change is
 *  dropped (its dependents go stale through their bases). */
export function foldUnitHeads(base: Graph, heads: UnitHead[]): FoldResult {
  const nodes = new Map(base.nodes);
  const tree: Tree = { ...base.tree };
  const conflicts: FoldResult["conflicts"] = [];
  const added: Array<{ id: NodeId; unit: number; pos: number }> = [];
  let unitIndex = 0;
  for (const head of heads) {
    const ids = new Set([...Object.keys(base.tree), ...Object.keys(head.graph.tree)]);
    for (const id of ids) {
      const b = base.tree[id]?.blob;
      const h = head.graph.tree[id]?.blob;
      if (b === h) continue; // unit did not touch it
      const cur = tree[id]?.blob;
      if (cur === h) continue; // identical change already present
      if (cur !== b) { conflicts.push({ unit: head.unit, id, reason: "another unit changed the same node" }); continue; }
      if (h === undefined) { nodes.delete(id); delete tree[id]; }
      else {
        nodes.set(id, head.graph.nodes.get(id)!);
        tree[id] = head.graph.tree[id];
        if (base.tree[id] === undefined) added.push({ id, unit: unitIndex, pos: head.graph.tree[id].pos });
      }
    }
    unitIndex++;
  }
  // Every unit numbered its additions from the same base, so their positions collide;
  // place additions after the base's last node of each type, unit by unit.
  const nextPos = new Map<NodeBlob["node_type"], number>();
  for (const [id, blob] of base.nodes) nextPos.set(blob.node_type, Math.max(nextPos.get(blob.node_type) ?? -1, base.tree[id].pos));
  for (const a of added.sort((x, y) => x.unit - y.unit || x.pos - y.pos || x.id.localeCompare(y.id))) {
    const type = nodes.get(a.id)!.node_type;
    const pos = (nextPos.get(type) ?? -1) + 1;
    nextPos.set(type, pos);
    tree[a.id] = { ...tree[a.id], pos };
  }
  return { graph: normalizeGraph({ tree, nodes }), conflicts };
}

/** Revert the changed nodes a check implicates until the graph passes.
 *
 *  Attribution is VERIFIED, never trusted: a touched node is the culprit of a
 *  violation only if reverting that node alone (or the culprits already found this
 *  round) makes the violation disappear. Nominees are tried first — the touched nodes
 *  a violation names by id or display name (a symbol as the gate prints it, a
 *  definition's name, a bib key), the node it was reported on, the `symbol:<name>` /
 *  zod path it denotes — then every other touched node. Among candidates a reverted
 *  DELETION comes first (it restores bytes main already had, so nothing the solver
 *  wrote is lost), a change next, an addition last. A violation no single revert
 *  removes reverts every touched node (the candidate collapses to the base) with the
 *  violation as the reason. This function never throws on a bad candidate. */
export function reconcileToBase(base: Graph, candidate: Graph, maxRounds = 25): { graph: Graph; dropped: Array<{ id: NodeId; reason: string }> } {
  // A later accepted edit can stale the theorem that used to answer an older
  // question. The tombstone is then no longer true: reopen the question before
  // attributing ordinary check failures. This is derivable from the candidate
  // tree itself and therefore does not require the old resolution's journal.
  const reopenStaleResolutions = (g: Graph): Graph => {
    const nodes = new Map(g.nodes);
    const tree = { ...g.tree };
    let changed = false;
    for (const { id, blob } of nodesOfType(g, "statement")) {
      if (blob.body.resolved_by === undefined) continue;
      const answer = g.nodes.get(blob.body.resolved_by);
      if (answer?.node_type === "statement" && deriveStatus(g, blob.body.resolved_by) === "proved" && proofCoversCurrentClosure(g, blob.body.resolved_by)) continue;
      const { resolved_by: _resolved, ...body } = blob.body;
      const reopened: NodeBlob = { node_type: "statement", body };
      nodes.set(id, reopened);
      tree[id] = { ...tree[id], blob: blobId(reopened) };
      changed = true;
    }
    return changed ? normalizeGraph({ tree, nodes }) : g;
  };
  let graph = reopenStaleResolutions(candidate);
  const dropped: Array<{ id: NodeId; reason: string }> = [];
  const reverted = (g: Graph, ids: Iterable<NodeId>): Graph => {
    const nodes = new Map(g.nodes);
    const tree = { ...g.tree };
    for (const id of new Set(ids)) {
      if (base.tree[id] === undefined) { nodes.delete(id); delete tree[id]; }
      else { nodes.set(id, base.nodes.get(id)!); tree[id] = base.tree[id]; }
    }
    return normalizeGraph({ tree, nodes });
  };
  const revert = (ids: Iterable<NodeId>, reason: (id: NodeId) => string): void => {
    const set = new Set(ids);
    for (const id of set) dropped.push({ id, reason: reason(id) });
    graph = reverted(graph, set);
  };
  const same = (a: Violation, b: Violation): boolean => a.code === b.code && a.where === b.where && a.message === b.message;
  const gone = (g: Graph, v: Violation): boolean => !checkGraph(g).violations.some((w) => same(w, v));
  for (let i = 0; i < maxRounds; i++) {
    const check = checkGraph(graph);
    if (check.ok) return { graph, dropped };
    const touched = new Set(changedIds(base, graph));
    if (touched.size === 0) break;
    // deletion (revert restores main's bytes) < change < addition
    const rank = (id: NodeId): number => (base.tree[id] === undefined ? 2 : graph.tree[id] === undefined ? 0 : 1);
    const byDisplayName = new Map<string, NodeId[]>();
    const name = (key: string, id: NodeId): void => { (byDisplayName.get(key) ?? byDisplayName.set(key, []).get(key)!).push(id); };
    for (const id of touched) {
      name(id, id);
      for (const g of [graph, base]) {
        const blob = g.nodes.get(id);
        if (blob === undefined) continue;
        if (blob.node_type === "symbol") { name(blob.body.name, id); name(normalizeSymbol(blob.body.name), id); }
        else if (blob.node_type === "definition") name(blob.body.name, id);
        else if (blob.node_type === "bib") name(blob.body.key, id);
      }
    }
    const rendered = check.core ?? renderCore(graph);
    const culprits = new Map<NodeId, string[]>();
    let unattributable: Violation | undefined;
    for (const v of check.violations) {
      const label = `[${v.code}] ${v.message}`;
      // Already explained by this round's culprits?
      if (culprits.size > 0 && gone(reverted(graph, culprits.keys()), v)) continue;
      const nominees: NodeId[] = [];
      for (const q of [...v.message.matchAll(/'([^']+)'/g)].map((m) => m[1])) {
        nominees.push(...(byDisplayName.get(q) ?? []), ...(byDisplayName.get(normalizeSymbol(q)) ?? []));
      }
      nominees.push(v.where);
      if (v.where.startsWith("symbol:")) nominees.push(symbolNodeId(v.where.slice("symbol:".length)));
      const zod = /^(statements|definitions|assumptions|symbols|bibliography)\.(\d+)/.exec(v.where);
      if (zod) {
        const list = rendered[zod[1] as "statements" | "definitions" | "assumptions" | "symbols" | "bibliography"] as Array<{ id?: string; name?: string; key?: string }>;
        const item = list[Number(zod[2])];
        const id = item?.id ?? (item?.name !== undefined ? symbolNodeId(item.name) : item?.key !== undefined ? bibNodeId(item.key) : undefined);
        if (id !== undefined) nominees.push(id);
      }
      for (const id of touched) if (v.message.includes(id)) nominees.push(id);
      const stable = (ids: NodeId[]): NodeId[] => ids.map((id, i) => ({ id, i })).sort((x, y) => rank(x.id) - rank(y.id) || x.i - y.i).map((x) => x.id);
      const ordered = [...new Set([...stable(nominees.filter((id) => touched.has(id))), ...stable([...touched].sort())])];
      const culprit = ordered.find((id) => gone(reverted(graph, [id]), v));
      if (culprit === undefined) { unattributable = v; break; }
      (culprits.get(culprit) ?? culprits.set(culprit, []).get(culprit)!).push(label);
    }
    if (unattributable !== undefined) {
      const v = unattributable;
      revert(touched, () => `unattributable violation ${v.where}: [${v.code}] ${v.message}`);
      break;
    }
    revert(culprits.keys(), (id) => culprits.get(id)!.join("; "));
  }
  const check = checkGraph(graph);
  if (check.ok) return { graph, dropped };
  revert(changedIds(base, graph), () => `graph still fails checks after ${maxRounds} rounds`);
  return { graph, dropped };
}

function changedIds(base: Graph, g: Graph): NodeId[] {
  const d = diffGraphs(base, g);
  return [...d.added, ...d.removed, ...d.changed.map((c) => c.id)];
}

// -- approval ---------------------------------------------------------------------------

/** Statement fields a solver may change without an adjudicator: proof, wiring,
 *  declared symbols, obligations, prose, provenance of another run's result. */
const STATEMENT_FREE_FIELDS = new Set([
  "proof_tex", "proof_basis", "depends_on", "free_symbols", "obligation", "justification", "gap", "consumer",
  "external_refs", "route", "resolved_by",
]);
const META_FREE_FIELDS = new Set([
  "tldr", "project_justification", "sampling_model", "related_work", "interpretation", "technical_internal_limitation", "honest_scope",
]);

export function approvalItems(base: Graph, head: Graph, reasons: Record<NodeId, string[]> = {}): ApprovalItem[] {
  const diff = diffGraphs(base, head);
  const items: ApprovalItem[] = [];
  for (const id of diff.removed) items.push({ id, change: "removed", fields: [], content: true, reasons: reasons[id] ?? [] });
  for (const id of diff.added) {
    const type = nodeTypeOf(id);
    const addedStatement = type === "statement" ? head.nodes.get(id) : undefined;
    if (type === "assumption" || type === "definition" || type === "symbol" ||
        (addedStatement?.node_type === "statement" && addedStatement.body.kind === "theorem")) {
      items.push({ id, change: "added", fields: [], content: true, reasons: reasons[id] ?? [] });
    }
  }
  for (const c of diff.changed) {
    const type = nodeTypeOf(c.id);
    const free = type === "statement" ? STATEMENT_FREE_FIELDS : type === "meta" ? META_FREE_FIELDS : type === "bib" ? new Set(c.fields) : new Set<string>();
    const gated = c.fields.filter((f) => !free.has(f));
    const before = base.nodes.get(c.id);
    const after = head.nodes.get(c.id);
    // Dropping an assumption/definition edge from a statement with a proof narrows what
    // the proof rests on without touching its basis: an adjudicator decides.
    if (before?.node_type === "statement" && after?.node_type === "statement" && c.fields.includes("depends_on") &&
        (before.body.proof_tex ?? "").trim().length > 0) {
      const kept = new Set(after.body.depends_on ?? []);
      const removed = (before.body.depends_on ?? []).filter((d) => !kept.has(d) && /^(ass|def):/.test(d));
      if (removed.length > 0) gated.push(`depends_on −${removed.join(",")}`);
    }
    if (gated.length === 0) continue;
    const warnings: string[] = [];
    if (before?.node_type === "statement" && after?.node_type === "statement" && gated.includes("statement")) {
      warnings.push(...narrowingWarnings(before.body.statement, after.body.statement));
    }
    items.push({ id: c.id, change: "changed", fields: gated, content: c.content, reasons: [...(reasons[c.id] ?? []), ...warnings] });
  }
  return items;
}

// -- PR records ---------------------------------------------------------------------------

function prDir(store: VcsStore): string {
  return path.join(store.dir, "prs");
}
function prPath(store: VcsStore, id: string): string {
  return path.join(prDir(store), `${id}.json`);
}

export async function readPr(store: VcsStore, id: string): Promise<PrRecord> {
  const resolved = await store.resolve(id);
  const p = prPath(store, resolved);
  if (!existsSync(p)) throw new Error(`vcs: no PR with head ${resolved}`);
  return JSON.parse(await readFile(p, "utf8")) as PrRecord;
}

export async function writePr(store: VcsStore, pr: PrRecord): Promise<void> {
  await writeJsonAtomic(prPath(store, pr.id), pr);
}

export async function listPrs(store: VcsStore, status?: PrRecord["status"]): Promise<PrRecord[]> {
  const dir = prDir(store);
  if (!existsSync(dir)) return [];
  const out: PrRecord[] = [];
  for (const name of await readdir(dir)) {
    if (!name.endsWith(".json")) continue;
    const pr = JSON.parse(await readFile(path.join(dir, name), "utf8")) as PrRecord;
    if (status === undefined || pr.status === status) out.push(pr);
  }
  return out.sort((a, b) => a.created.localeCompare(b.created));
}

// -- open a PR from a round's unit outputs --------------------------------------------------

export interface OpenPrArgs {
  store: VcsStore;
  base: string;
  round: number;
  submissions: UnitSubmission[];
  /** Escalation-journal length shown to this round; consumed when the PR is merged. */
  journalLength?: number;
}

function hasExistingProseDelta(base: Graph, head: Graph): boolean {
  const baseMeta = base.nodes.get(META_ID);
  const headMeta = head.nodes.get(META_ID);
  if (!isDeepStrictEqual(baseMeta, headMeta)) {
    const prose = ["tldr", "project_justification", "sampling_model", "related_work", "interpretation", "technical_internal_limitation", "honest_scope"] as const;
    if (baseMeta?.node_type === "meta" && headMeta?.node_type === "meta" &&
        prose.some((field) => !isDeepStrictEqual(baseMeta.body[field], headMeta.body[field]))) return true;
  }
  for (const [id, blob] of base.nodes) {
    const next = head.nodes.get(id);
    if (blob.node_type !== "statement" || next?.node_type !== "statement") continue;
    for (const field of ["justification", "gap", "consumer"] as const) {
      if (!isDeepStrictEqual(blob.body[field], next.body[field])) return true;
    }
  }
  return false;
}

function reserveOeqResolutions(base: Graph, submissions: UnitSubmission[]): { submissions: UnitSubmission[]; rejected: RejectedItem[][] } {
  const sources = new Set<NodeId>();
  const newStatementIds = new Set<NodeId>();
  const rejected = submissions.map(() => [] as RejectedItem[]);
  return {
    submissions: submissions.map((submission, index) => {
      const kept = submission.output.resolved_oeqs.filter((resolution) => {
        const source = base.nodes.get(resolution.source_id);
        let invalid: string | undefined;
        if (source?.node_type !== "statement" || source.body.kind !== "openendedquestion" || source.body.resolved_by !== undefined) invalid = "not a live open question";
        else if (!submission.targets.includes(resolution.source_id)) invalid = "not a target of this unit";
        else if (base.nodes.has(resolution.theorem.id)) invalid = `answer id '${resolution.theorem.id}' already exists`;
        if (invalid !== undefined) {
          rejected[index].push({ unit: submission.unit, channel: "resolved_oeqs", id: resolution.source_id, reason: invalid });
          return false;
        }
        const reason = sources.has(resolution.source_id)
          ? "open question already has an answer reserved earlier in this round"
          : newStatementIds.has(resolution.theorem.id)
            ? "answer id already reserved by an earlier statement in this round"
            : undefined;
        if (reason !== undefined) {
          rejected[index].push({ unit: submission.unit, channel: "resolved_oeqs", id: resolution.source_id, reason });
          return false;
        }
        sources.add(resolution.source_id);
        newStatementIds.add(resolution.theorem.id);
        return true;
      });
      const lemmas = submission.output.added_lemmas.filter((lemma) => {
        if (base.nodes.has(lemma.id)) return true;
        if (!newStatementIds.has(lemma.id)) {
          newStatementIds.add(lemma.id);
          return true;
        }
        rejected[index].push({ unit: submission.unit, channel: "added_lemmas", id: lemma.id, reason: "statement id already reserved earlier in this round" });
        return false;
      });
      return { ...submission, output: { ...submission.output, resolved_oeqs: kept, added_lemmas: lemmas } };
    }),
    rejected,
  };
}

export interface ResolutionProvenance extends UnitResolution {
  answerIdentity: string;
  sourceIdentity: string;
}

function answerIdentity(blob: NodeBlob | undefined): string | undefined {
  return blob?.node_type === "statement" ? blobId(blob) : undefined;
}

function resolutionProvenance(heads: UnitHead[], composed: Graph): ResolutionProvenance[] {
  return heads.flatMap((head) => head.resolutions.flatMap((resolution) => {
    const identity = answerIdentity(composed.nodes.get(resolution.answerId));
    const source = composed.nodes.get(resolution.sourceId);
    if (identity === undefined || source?.node_type !== "statement" || source.body.resolved_by !== resolution.answerId) return [];
    return [{ ...resolution, answerIdentity: identity, sourceIdentity: blobId(source) }];
  }));
}

/** `dropped` receives every answer node this repair deletes, so a lost solver result is
 * always visible on the PR (`prLosses`) rather than vanishing between two reconciles. */
function restoreBrokenResolutions(base: Graph, graph: Graph, provenance: ResolutionProvenance[], dropInvalidAnswers: boolean, dropped: Array<{ id: NodeId; reason: string }> = [], remaining = provenance.length): Graph {
  const nodes = new Map(graph.nodes);
  const tree = { ...graph.tree };
  for (const resolution of provenance) {
    const source = nodes.get(resolution.sourceId);
    const answer = nodes.get(resolution.answerId);
    const exactAnswer = answerIdentity(answer) === resolution.answerIdentity;
    const exactSource = source !== undefined && blobId(source) === resolution.sourceIdentity;
    const answerValid = answer?.node_type === "statement" &&
      deriveStatus({ tree, nodes }, resolution.answerId) === "proved" &&
      proofCoversCurrentClosure({ tree, nodes }, resolution.answerId);
    const sourceStillReferenced = [...nodes.values()].some((blob) => {
      if (blob.node_type === "symbol") return blob.body.ref === resolution.sourceId;
      if (blob.node_type === "statement") return blob.body.resolved_by === undefined && (blob.body.depends_on ?? []).includes(resolution.sourceId);
      if (blob.node_type === "definition") return (blob.body.inputs ?? []).some((input) => input === resolution.sourceId || extractNodeRefs(input).includes(resolution.sourceId)) ||
        (blob.body.by_member_properties ?? []).includes(resolution.sourceId) || extractNodeRefs(blob.body.construction).includes(resolution.sourceId);
      if (blob.node_type === "assumption") return extractNodeRefs(blob.body.condition).includes(resolution.sourceId);
      return false;
    });
    if (source?.node_type === "statement" && source.body.resolved_by === resolution.answerId && exactSource && exactAnswer && answerValid && !sourceStillReferenced) continue;

    if (source?.node_type === "statement" && source.body.resolved_by === resolution.answerId) {
      const { resolved_by: _resolved, ...body } = source.body;
      const restored: NodeBlob = { node_type: "statement", body };
      nodes.set(resolution.sourceId, restored);
      tree[resolution.sourceId] = { ...tree[resolution.sourceId], blob: blobId(restored) };
    }
    for (const [id, blob] of nodes) {
      const original = base.nodes.get(id);
      const baseSymbolRewire = original?.node_type === "symbol" && original.body.ref === resolution.sourceId;
      if (blob.node_type === "symbol" && (resolution.rewiredSymbols.includes(id) || baseSymbolRewire) && blob.body.ref === resolution.answerId) {
        const restored: NodeBlob = { node_type: "symbol", body: { ...blob.body, ref: resolution.sourceId } };
        nodes.set(id, restored);
        tree[id] = { ...tree[id], blob: blobId(restored) };
      }
      const baseConsumerRewire = original?.node_type === "statement" && (original.body.depends_on ?? []).includes(resolution.sourceId);
      if (blob.node_type !== "statement" || (!resolution.rewiredConsumers.includes(id) && !baseConsumerRewire) ||
          !(blob.body.depends_on ?? []).includes(resolution.answerId)) continue;
      const dependencies = (blob.body.depends_on ?? []).map((dependency) => dependency === resolution.answerId ? resolution.sourceId : dependency);
      const restored: NodeBlob = { node_type: "statement", body: { ...blob.body, depends_on: dependencies } };
      nodes.set(id, restored);
      tree[id] = { ...tree[id], blob: blobId(restored) };
    }
    if (!exactAnswer) continue;
    if (dropInvalidAnswers && base.nodes.get(resolution.answerId) === undefined) {
      nodes.delete(resolution.answerId);
      delete tree[resolution.answerId];
      dropped.push({ id: resolution.answerId, reason: `answer to ${resolution.sourceId} no longer stands (basis stale or question still referenced); question reopened` });
      continue;
    }
    const statement = nodes.get(resolution.answerId);
    if (statement?.node_type !== "statement") continue;
    const dependencies = (statement.body.depends_on ?? []).filter((dependency) => dependency !== resolution.sourceId);
    const proofBasis = statement.body.proof_basis === undefined ? undefined : { ...statement.body.proof_basis };
    if (proofBasis !== undefined) delete proofBasis[resolution.sourceId];
    const body = { ...statement.body, depends_on: dependencies, proof_basis: proofBasis };
    if (proofBasis === undefined) delete body.proof_basis;
    const detached: NodeBlob = { node_type: "statement", body };
    nodes.set(resolution.answerId, detached);
    tree[resolution.answerId] = { ...tree[resolution.answerId], blob: blobId(detached) };
  }
  const normalized = normalizeGraph({ tree, nodes });
  if (remaining > 0 && !isEmptyDiff(diffGraphs(graph, normalized))) {
    return restoreBrokenResolutions(base, normalized, provenance, dropInvalidAnswers, dropped, remaining - 1);
  }
  return normalized;
}

export async function openPr(args: OpenPrArgs): Promise<{ pr: PrRecord; head: Graph }> {
  const base = await loadGraph(args.store, args.base);
  let ownerAssigned = false;
  const submissions = args.submissions.map((submission) => {
    const requested = submission.proseRole ?? "omit";
    const role = requested === "owner" && !ownerAssigned ? "owner" : "omit";
    if (role === "owner") ownerAssigned = true;
    return scopeSubmissionProse(submission, role);
  });
  const reserved = reserveOeqResolutions(base, submissions);
  const heads = reserved.submissions.map((s, index) => {
    const head = applyUnitOutput(base, {
      ...s,
      siblingTargets: reserved.submissions.filter((o) => o !== s).flatMap((o) => o.targets),
    });
    head.rejected.push(...reserved.rejected[index]);
    return head;
  });
  const fold = foldUnitHeads(base, heads);
  const firstReconcile = reconcileToBase(base, fold.graph);
  const repairDropped: Array<{ id: NodeId; reason: string }> = [];
  const provenance = resolutionProvenance(heads, fold.graph);
  const repaired = restoreBrokenResolutions(base, firstReconcile.graph, provenance, true, repairDropped);
  const reconciled = reconcileToBase(base, repaired);
  reconciled.dropped.unshift(...firstReconcile.dropped, ...repairDropped);
  const reasons: Record<NodeId, string[]> = {};
  for (const h of heads) for (const [id, rs] of Object.entries(h.reasons)) (reasons[id] ??= []).push(...rs);
  const unitRecords: PrRecord["units"] = [];
  for (const h of heads) {
    const commit = await commitGraph({
      store: args.store, graph: h.graph, parents: [args.base], author: `solver:${h.unit}`, kind: "pr",
      message: `round ${args.round} unit ${h.unit}`, expectedHead: null, detached: true,
      meta: { round: args.round, unit: h.unit, targets: h.targets },
    });
    // A unit head that fails the checks is still recorded by its (unchecked) tree hash
    // for provenance; the fold + reconcile above already dropped the offending nodes.
    unitRecords.push({ unit: h.unit, targets: h.targets, head: commit.ok ? commit.id : "unchecked", rejected: h.rejected });
  }
  const head = await commitGraph({
    store: args.store, graph: reconciled.graph, parents: [args.base], author: "solver", kind: "pr",
    message: `round ${args.round}: ${reserved.submissions.map((s) => s.unit).join(", ")}`, expectedHead: null, detached: true,
    meta: { round: args.round, units: reserved.submissions.map((s) => s.unit) },
  });
  if (!head.ok) throw new Error(`vcs: reconciled round head fails checks: ${head.violations.map((v) => `${v.code}@${v.where}`).join(", ")}`);
  const diff = diffGraphs(base, head.graph);
  const inputsPath = path.join(prDir(args.store), `${head.id}.inputs.json`);
  // Persist exactly what the caller supplied; prose scoping and resolution
  // reservation are deterministic transforms replayed by openPr on reapply.
  await writeJsonAtomic(inputsPath, { units: args.submissions });
  const pr: PrRecord = {
    id: head.id,
    inputs: inputsPath,
    base: args.base,
    round: args.round,
    created: new Date().toISOString(),
    units: unitRecords,
    dropped: [
      ...fold.conflicts.map((c) => ({ unit: c.unit, id: c.id, reason: c.reason })),
      ...reconciled.dropped,
    ],
    approval: approvalItems(base, head.graph, reasons),
    summary: { added: diff.added, removed: diff.removed, changed: diff.changed.map((c) => c.id) },
    status: "open",
    ...(args.journalLength !== undefined ? { journal_length: args.journalLength } : {}),
    ...(hasExistingProseDelta(base, head.graph)
      ? { has_leased_prose: true }
      : {}),
    ...(provenance.length > 0 ? { resolutions: provenance } : {}),
  };
  await writePr(args.store, pr);
  return { pr, head: head.graph };
}

/** Replay a PR's raw unit outputs against `base` (normally the current main) as a new
 *  PR, closing the original as superseded. This is the recovery path after the
 *  orchestrator repairs on main whatever a DID NOT LAND reason named: nothing the
 *  solver wrote has to be retyped, and the ordinary fold / check / approval apply. */
export async function reapplyPr(store: VcsStore, pr: PrRecord, args: { base: string; note?: string }): Promise<{ pr: PrRecord; head: Graph }> {
  if (pr.inputs === undefined) throw new Error(`vcs: PR ${pr.id.slice(0, 12)} has no raw inputs to replay`);
  const inputs = JSON.parse(await readFile(pr.inputs, "utf8")) as { units: UnitSubmission[] };
  if (pr.status === "open") await closePr(store, pr, `superseded by a reapply${args.note ? `: ${args.note}` : ""}`);
  const submissions = args.base === pr.base
    ? inputs.units
    : inputs.units.map((unit) => ({ ...unit, proseRole: "omit" as const }));
  const opened = await openPr({
    store, base: args.base, round: pr.round, submissions, journalLength: pr.journal_length,
  });
  const record: PrRecord = { ...opened.pr, reapplied_from: pr.id };
  await writePr(store, record);
  return { pr: record, head: opened.head };
}

// -- merge -------------------------------------------------------------------------------

export interface MergeVerdict {
  accept: NodeId[] | "all";
  reject?: NodeId[];
  /** For each node main changed after the PR's base: which side lands. A conflict
   *  without a decision refuses the merge — nothing is ever dropped silently. */
  conflicts?: Record<NodeId, "main" | "pr">;
  note: string;
  by: string;
}

export interface UnresolvedConflict {
  id: NodeId;
  /** `conflict`: main changed the node after the base — decide with `--keep-main` /
   *  `--keep-pr`. `check`: the chosen sides do not stand together — hand-merge on main
   *  (edit core.json, commit), then merge with `--keep-main`. */
  kind: "conflict" | "check";
  reason: string;
  main?: NodeBlob;
  pr?: NodeBlob;
}

export type MergeResult =
  | { ok: true; commit: string; graph: Graph; conflicts: Array<{ id: NodeId; reason: string }> }
  | { ok: false; violations: Violation[]; unresolved: UnresolvedConflict[] };

/** An accepted answer must not silently retarget a symbol change the verdict rejected.
 * In that case the answer remains as a diagnostic theorem, while its source question
 * remains live and the synthetic answer/question link is removed. */
function detachAnswersBlockedByRejectedSymbols(
  base: Graph,
  head: Graph,
  nodes: Map<NodeId, NodeBlob>,
  tree: Tree,
  acceptedIds: Set<NodeId>,
  rejectedIds: Set<NodeId>,
): void {
  for (const id of rejectedIds) {
    const before = base.nodes.get(id);
    if (before?.node_type !== "symbol" || base.tree[id]?.blob === head.tree[id]?.blob) continue;
    const sourceId = before.body.ref;
    if (sourceId === undefined) continue;
    const source = nodes.get(sourceId);
    if (source?.node_type !== "statement" || source.body.resolved_by === undefined) continue;
    const answerId = source.body.resolved_by;
    if (!acceptedIds.has(answerId)) continue;

    const { resolved_by: _resolved, ...sourceBody } = source.body;
    const liveSource: NodeBlob = { node_type: "statement", body: sourceBody };
    nodes.set(sourceId, liveSource);
    tree[sourceId] = { ...tree[sourceId], blob: blobId(liveSource) };

    const answer = nodes.get(answerId);
    if (answer?.node_type !== "statement") continue;
    const dependencies = (answer.body.depends_on ?? []).filter((dependency) => dependency !== sourceId);
    const proofBasis = answer.body.proof_basis === undefined ? undefined : { ...answer.body.proof_basis };
    if (proofBasis !== undefined) delete proofBasis[sourceId];
    const detachedBody = { ...answer.body, depends_on: dependencies, proof_basis: proofBasis };
    if (proofBasis === undefined) delete detachedBody.proof_basis;
    const detached: NodeBlob = { node_type: "statement", body: detachedBody };
    nodes.set(answerId, detached);
    tree[answerId] = { ...tree[answerId], blob: blobId(detached) };

    for (const [consumerId, consumer] of nodes) {
      if (consumerId === answerId || consumer.node_type !== "statement") continue;
      const original = base.nodes.get(consumerId);
      if (original?.node_type !== "statement" || !(original.body.depends_on ?? []).includes(sourceId)) continue;
      if ((original.body.depends_on ?? []).includes(answerId) || !(consumer.body.depends_on ?? []).includes(answerId)) continue;
      const restoredDependencies = (consumer.body.depends_on ?? []).map((dependency) => dependency === answerId ? sourceId : dependency);
      const restored: NodeBlob = { node_type: "statement", body: { ...consumer.body, depends_on: restoredDependencies } };
      nodes.set(consumerId, restored);
      tree[consumerId] = { ...tree[consumerId], blob: blobId(restored) };
    }
  }
}

/** Apply the verdict, three-way merge onto main, commit. Refuses, writing nothing, on
 *  an undecided conflict; dependents of a rejected item are dropped with it and
 *  recorded on the PR. */
export async function mergePr(args: { store: VcsStore; ctx?: PipelineContext; pr: PrRecord; verdict: MergeVerdict }): Promise<MergeResult> {
  const { store, pr, verdict } = args;
  if (pr.status !== "open") throw new Error(`vcs: PR ${pr.id.slice(0, 12)} is ${pr.status}`);
  const base = await loadGraph(store, pr.base);
  const head = await loadGraph(store, pr.id);
  const approvalIds = new Set(pr.approval.map((a) => a.id));
  const rejectedIds = new Set(verdict.reject ?? []);
  const acceptedIds = verdict.accept === "all"
    ? new Set([...approvalIds].filter((id) => !rejectedIds.has(id)))
    : new Set(verdict.accept);
  // An unknown id in either list is a typo, never a silent rejection.
  for (const id of [...acceptedIds, ...rejectedIds]) {
    if (!approvalIds.has(id)) throw new Error(`vcs: '${id}' is not an approval item of this PR (items: ${[...approvalIds].join(", ")})`);
  }
  for (const id of approvalIds) if (!acceptedIds.has(id) && !rejectedIds.has(id)) rejectedIds.add(id);

  // head' = head with the rejected items reverted to base. A rejected STATEMENT change
  // reverts only the gated fields (claim, kind, source): the solver's proof, obligation,
  // wiring and prose stay, and the basis rule decides whether that proof still holds —
  // a proof of the rejected claim simply comes back to-prove.
  const nodes = new Map(head.nodes);
  const tree: Tree = { ...head.tree };
  for (const id of rejectedIds) {
    const b = base.nodes.get(id);
    const h = head.nodes.get(id);
    if (b === undefined) { nodes.delete(id); delete tree[id]; continue; }
    if (b.node_type === "statement" && h?.node_type === "statement" && h.body.resolved_by === undefined) {
      const kept: NodeBlob = { node_type: "statement", body: { ...h.body, statement: b.body.statement, kind: b.body.kind, source: b.body.source } };
      if (b.body.source === undefined) delete kept.body.source;
      nodes.set(id, kept);
      tree[id] = { ...tree[id], blob: blobId(kept) };
      continue;
    }
    nodes.set(id, b);
    tree[id] = base.tree[id];
  }
  detachAnswersBlockedByRejectedSymbols(base, head, nodes, tree, acceptedIds, rejectedIds);
  // Dependents of a rejected item that cannot stand without it are dropped too,
  // with the violation as their reason (the same rule the fold applies).
  const settled = reconcileToBase(base, normalizeGraph({ tree, nodes }));
  let headPrime = settled.graph;
  const cascaded = [...settled.dropped];

  // Three-way onto main.
  const mainId = await store.readRef(MAIN_REF);
  if (mainId === null) throw new Error("vcs: no main");
  if (mainId !== pr.base && hasExistingProseDelta(base, head)) {
    return {
      ok: false, violations: [],
      unresolved: [{ id: META_ID, kind: "conflict", reason: "leased paper prose was authored against an older base; reapply or rerun before merge" }],
    };
  }
  const main = await loadGraph(store, mainId);
  const provenance = pr.resolutions ?? [];
  const repairedHeadPrime = restoreBrokenResolutions(base, headPrime, provenance, false);
  const headPrimeReconciled = reconcileToBase(base, repairedHeadPrime);
  headPrime = headPrimeReconciled.graph;
  cascaded.push(...headPrimeReconciled.dropped);
  const merged = new Map(main.nodes);
  const mergedTree: Tree = { ...main.tree };
  const conflicts: Array<{ id: NodeId; reason: string }> = [];
  const unresolved: UnresolvedConflict[] = [];
  const decisions = verdict.conflicts ?? {};
  const ids = new Set([...Object.keys(base.tree), ...Object.keys(headPrime.tree)]);
  for (const id of ids) {
    const b = base.tree[id]?.blob;
    const h = headPrime.tree[id]?.blob;
    if (b === h) continue;
    const m = main.tree[id]?.blob;
    if (m === h) continue;
    if (m !== b) {
      const decision = decisions[id];
      if (decision === undefined) {
        unresolved.push({ id, kind: "conflict", reason: "main changed this node after the PR's base", main: main.nodes.get(id), pr: headPrime.nodes.get(id) });
        continue;
      }
      if (decision === "main") { conflicts.push({ id, reason: "conflict resolved: kept main's version" }); continue; }
      conflicts.push({ id, reason: "conflict resolved: took the PR's version" });
    }
    if (h === undefined) { merged.delete(id); delete mergedTree[id]; }
    else { merged.set(id, headPrime.nodes.get(id)!); mergedTree[id] = headPrime.tree[id]; }
  }
  if (unresolved.length > 0) return { ok: false, violations: [], unresolved };
  const repairedMerge = restoreBrokenResolutions(main, normalizeGraph({ tree: mergedTree, nodes: merged }), provenance, false);
  const reconciled = reconcileToBase(main, repairedMerge);
  if (reconciled.dropped.length > 0) {
    // The chosen sides do not stand together on main (a dangling reference across the
    // two versions): nothing lands until the orchestrator commits a hand merge on main.
    return {
      ok: false, violations: [],
      unresolved: reconciled.dropped.map((d) => ({ id: d.id, kind: "check" as const, reason: `the merged tree fails a check on this node: ${d.reason}` })),
    };
  }
  for (const d of cascaded) conflicts.push({ id: d.id, reason: `dropped with a rejected item: ${d.reason}` });

  const headPrimeCommit = await commitGraph({
    store, graph: headPrime, parents: [pr.base], author: "adjudicator", kind: "pr",
    message: `round ${pr.round} accepted head`, expectedHead: null, detached: true,
    meta: { pr: pr.id, accepted: [...acceptedIds], rejected: [...rejectedIds] },
  });
  if (!headPrimeCommit.ok) throw new Error("vcs: accepted head failed a check it just passed");
  const merge = await commitGraph({
    store, graph: reconciled.graph, parents: [mainId, headPrimeCommit.id], author: verdict.by, kind: "merge",
    message: `merge round ${pr.round}: ${verdict.note}`, expectedHead: mainId,
    meta: { pr: pr.id, accepted: [...acceptedIds], rejected: [...rejectedIds], conflicts },
  });
  if (!merge.ok) return { ok: false, violations: merge.violations, unresolved: [] };
  await clearSolveReceipts(store);
  // Dependents dropped with a rejected item are recorded where every other loss is.
  for (const d of cascaded) pr.dropped.push({ id: d.id, reason: `dropped with a rejected item at merge: ${d.reason}` });
  pr.status = "merged";
  pr.verdict = { accepted: [...acceptedIds], rejected: [...rejectedIds], note: verdict.note, at: new Date().toISOString(), by: verdict.by };
  pr.merge_commit = merge.id;
  await writePr(store, pr);
  if (args.ctx !== undefined) await publishCore(args.ctx, store);
  return { ok: true, commit: merge.id, graph: merge.graph, conflicts };
}

export async function closePr(store: VcsStore, pr: PrRecord, note: string): Promise<void> {
  if (pr.status !== "open") throw new Error(`vcs: PR ${pr.id.slice(0, 12)} is ${pr.status}`);
  pr.status = "closed";
  pr.closed_note = note;
  await writePr(store, pr);
  await clearSolveReceipts(store);
}

/** Any disposition of a PR retires the round's reuse receipts: the next dispatch of
 *  the same targets must be a fresh solve, not a replay of the output just judged. */
async function clearSolveReceipts(store: VcsStore): Promise<void> {
  await rm(path.join(path.dirname(store.dir), "solve_receipts"), { recursive: true, force: true });
}

// -- rendering for the adjudicator ------------------------------------------------------------

export function describePr(pr: PrRecord, base: Graph, head: Graph): string {
  const lines: string[] = [];
  lines.push(`PR ${pr.id.slice(0, 12)}  round ${pr.round}  base ${pr.base.slice(0, 12)}  status ${pr.status}`);
  lines.push(`units: ${pr.units.map((u) => `${u.unit} [${u.targets.join(", ")}]`).join("; ")}`);
  const diff: GraphDiff = diffGraphs(base, head);
  lines.push(`diff: +${diff.added.length} −${diff.removed.length} ~${diff.changed.length}`);
  for (const id of diff.added) lines.push(`  + ${id}${summarize(head.nodes.get(id))}`);
  for (const id of diff.removed) lines.push(`  - ${id}`);
  for (const c of diff.changed) lines.push(`  ~ ${c.id}${c.content ? " [content]" : ""} (${c.fields.join(", ")})`);
  if (pr.approval.length === 0) lines.push("needs approval: nothing (auto-merge)");
  else {
    lines.push("NEEDS APPROVAL:");
    for (const a of pr.approval) {
      lines.push(`  ${a.id}  ${a.change}${a.fields.length > 0 ? ` (${a.fields.join(", ")})` : ""}`);
      const before = base.nodes.get(a.id);
      const after = head.nodes.get(a.id);
      if (before !== undefined && a.change !== "added") lines.push(`      before: ${summarize(before)}`);
      if (after !== undefined && a.change !== "removed") lines.push(`      after:  ${summarize(after)}`);
      for (const r of a.reasons) lines.push(`      reason: ${r}`);
    }
  }
  const losses = prLosses(pr);
  if (losses.length > 0) {
    lines.push(`DID NOT LAND (${losses.length}) — each reason names what on main blocked it. Fix that on main (edit core.json, d0_vc commit) and replay the round with \`pr reapply ${pr.id.slice(0, 12)}\`; or merge by hand from ${pr.inputs ?? "the unit outputs"}; or accept the loss by merging:`);
    for (const l of losses) lines.push(`  ${l.id}: ${l.reason}`);
  }
  if (pr.verdict !== undefined) lines.push(`verdict: accepted ${pr.verdict.accepted.length}, rejected ${pr.verdict.rejected.length} — ${pr.verdict.note}`);
  return lines.join("\n");
}

function summarize(blob: NodeBlob | undefined): string {
  if (blob === undefined) return "";
  const cut = (s: string | undefined, n = 160): string => (s ?? "").replace(/\s+/g, " ").slice(0, n);
  switch (blob.node_type) {
    case "statement": return `  ${cut(blob.body.statement)}`;
    case "definition": return `  ${blob.body.name}: ${cut(blob.body.construction)}`;
    case "assumption": return `  ${cut(blob.body.condition)}`;
    case "symbol": return `  ${blob.body.name} : ${cut(blob.body.type, 60)}`;
    case "bib": return `  ${cut(blob.body.citation, 80)}`;
    case "meta": return `  ${cut(JSON.stringify(blob.body), 200)}`;
  }
}

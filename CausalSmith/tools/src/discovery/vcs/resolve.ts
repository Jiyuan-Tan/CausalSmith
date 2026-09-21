// Deterministic OEQ resolution to a theorem that already exists on main.
//
// A bare Q -> T assertion is not enough: an OEQ is natural-language mathematics,
// so graph shape alone cannot establish that T answers it.  The certificate here
// reuses an adjudicated solver PR whose proved answer W was positively accepted.
// W must be derivable from T and only the context already carried by Q.
import { extractNodeRefs } from "../core/node_ids.js";
import { checkGraph, formatViolations } from "./checks.js";
import { type Graph, statementBlob, nodesOfType } from "./graph.js";
import { blobId, contentKey, sha256Hex, type NodeBlob, type NodeId } from "./node.js";
import type { PrRecord, UnitSubmission } from "./pr.js";
import { normalizeGraph } from "./render.js";
import type { Commit } from "./store.js";
import { contentClosure, deriveStatus, proofCoversCurrentClosure } from "./validity.js";

export interface ExistingOeqResolutionArgs {
  current: Graph;
  currentId: string;
  prBase: Graph;
  prHead: Graph;
  acceptedHead: Graph;
  pr: PrRecord;
  mergeCommit: Commit;
  acceptedHeadCommit: Commit;
  sourceId: NodeId;
  theoremId: NodeId;
}

function fail(message: string): never {
  throw new Error(`vcs: cannot resolve OEQ: ${message}`);
}

/** A proof may typeset a node id as `\mathrm{thm{:}foo\mbox{-}bar}`.  Collapse
 * those presentation-only wrappers before using the shared node-ref extractor;
 * this does not infer a citation from depends_on or proof_basis. */
function proofNodeRefs(proof: string): string[] {
  const citationView = proof
    .replace(/\\(?:text|mbox)\{([:-])\}/g, "$1")
    .replace(/\{:\}/g, ":")
    .replace(/\\(?:mathrm|texttt|operatorname)\{([^{}]+)\}/g, "$1");
  return extractNodeRefs(citationView);
}

/** Construct the deterministic alias submission that must pass ordinary PR review
 * before an existing theorem can resolve an OEQ. Pure: opening/merging is external. */
export function prepareOeqResolutionToExisting(
  graph: Graph,
  sourceId: NodeId,
  theoremId: NodeId,
): { witnessId: NodeId; expectedApprovalIds: NodeId[]; submission: UnitSubmission } {
  const source = statementBlob(graph, sourceId);
  if (source?.body.kind !== "openendedquestion" || source.body.resolved_by !== undefined) {
    fail(`'${sourceId}' is not a live open-ended question`);
  }
  if (source.body.proof_tex !== undefined || source.body.proof_basis !== undefined || source.body.source !== undefined) {
    fail(`'${sourceId}' is not an ordinary to-prove open-ended question (proof/source fields must be absent)`);
  }
  const theorem = statementBlob(graph, theoremId);
  if (theorem?.body.kind !== "theorem" || theorem.body.resolved_by !== undefined ||
      deriveStatus(graph, theoremId) !== "proved" || !proofCoversCurrentClosure(graph, theoremId)) {
    fail(`'${theoremId}' is not a live proved theorem with a complete current basis`);
  }
  // Match the resolution fold's rewritable surface before claiming that a review
  // PR can be opened. Definitions and assumptions are not silently retargeted when
  // Q becomes W. Proof bases are derived identity records rather than authored
  // references; live statement dependency edges and symbol refs are explicitly
  // rewired by the resolution path.
  for (const [id, blob] of graph.nodes) {
    if (id === sourceId) continue;
    const body = structuredClone(blob.body) as unknown as Record<string, unknown>;
    delete body.id;
    if (blob.node_type === "statement" && blob.body.resolved_by === undefined) {
      delete body.depends_on;
      delete body.proof_basis;
    } else if (blob.node_type === "symbol") {
      delete body.ref;
    }
    if (proofNodeRefs(JSON.stringify(body)).includes(sourceId)) {
      fail(`non-rewritable field of '${id}' references question '${sourceId}'`);
    }
  }
  const witnessId = `thm:resolve-${sha256Hex(`${sourceId}\0${theoremId}\0${contentKey(theorem)}`).slice(0, 20)}`;
  if (graph.nodes.has(witnessId)) fail(`deterministic witness id '${witnessId}' already exists`);
  const rewiredSymbols = nodesOfType(graph, "symbol")
    .filter(({ blob }) => blob.body.ref === sourceId)
    .map(({ id }) => id)
    .sort();
  const { proof_basis: _basis, resolved_by: _resolved, proof_tex: _proof, depends_on: _deps, id: _id, ...claim } = theorem.body;
  const witness = {
    ...claim,
    id: witnessId,
    kind: "theorem" as const,
    status: "proved" as const,
    depends_on: [sourceId, theoremId],
    proof_tex: `This is exactly the claim of ${theoremId}; apply ${theoremId}.`,
  };
  return {
    witnessId,
    expectedApprovalIds: [witnessId, ...rewiredSymbols].sort(),
    submission: {
      unit: sourceId,
      targets: [sourceId],
      proseRole: "omit",
      output: {
        proofs: [],
        resolved_oeqs: [{ source_id: sourceId, theorem: witness }],
        added_lemmas: [],
        proposed_statement_changes: [],
        proposed_definition_changes: [],
        proposed_assumptions: [],
        proposed_core_edits: [],
        open_obligations: [],
      },
    },
  };
}

/** Ensure openPr realized exactly the deterministic preparation and did not drop
 * any part of it. Pure; callers decide whether and how to proceed with review. */
export function assertPreparedOeqResolutionPr(
  pr: PrRecord,
  sourceId: NodeId,
  prepared: ReturnType<typeof prepareOeqResolutionToExisting>,
): void {
  const resolutions = pr.resolutions ?? [];
  const actualApproval = pr.approval.map((item) => item.id).sort();
  const rejected = pr.units.flatMap((unit) => unit.rejected);
  if (resolutions.length !== 1 || resolutions[0].sourceId !== sourceId ||
      resolutions[0].answerId !== prepared.witnessId ||
      JSON.stringify(actualApproval) !== JSON.stringify(prepared.expectedApprovalIds) ||
      pr.dropped.length !== 0 || rejected.length !== 0) {
    fail(`opened PR ${pr.id} does not contain exactly the expected resolution and approvals (${prepared.expectedApprovalIds.join(", ")})`);
  }
}

/** Check a reviewed resolution witness and return the normalized resolved graph.
 * Inputs are immutable; this function performs no store writes. */
export function resolveOeqToExisting(args: ExistingOeqResolutionArgs): Graph {
  const { current, currentId, prBase, prHead, acceptedHead, pr, mergeCommit, acceptedHeadCommit, sourceId, theoremId } = args;
  const resolutions = (pr.resolutions ?? []).filter((r) => r.sourceId === sourceId);
  if (resolutions.length !== 1) fail(`PR ${pr.id.slice(0, 12)} must contain exactly one resolution for '${sourceId}'`);
  const witnessId = resolutions[0].answerId;
  if (pr.status !== "merged" || pr.verdict === undefined || !pr.verdict.accepted.includes(witnessId)) {
    fail(`PR ${pr.id.slice(0, 12)} did not positively adjudicate its answer '${witnessId}'`);
  }
  if (pr.merge_commit === undefined || mergeCommit.id !== pr.merge_commit || currentId !== mergeCommit.id) {
    fail(`main is not the immutable merge commit recorded for PR ${pr.id.slice(0, 12)}`);
  }
  const sameIds = (actual: unknown, expected: string[]): boolean =>
    Array.isArray(actual) && JSON.stringify([...actual].sort()) === JSON.stringify([...expected].sort());
  if (mergeCommit.kind !== "merge" || mergeCommit.author !== pr.verdict.by || mergeCommit.meta?.pr !== pr.id ||
      !sameIds(mergeCommit.meta?.accepted, pr.verdict.accepted) || !sameIds(mergeCommit.meta?.rejected, pr.verdict.rejected) ||
      mergeCommit.parents[0] !== pr.base || mergeCommit.parents[1] !== acceptedHeadCommit.id) {
    fail("immutable merge metadata disagrees with the PR verdict");
  }
  if (acceptedHeadCommit.kind !== "pr" || acceptedHeadCommit.parents.length !== 1 || acceptedHeadCommit.parents[0] !== pr.base ||
      acceptedHeadCommit.meta?.pr !== pr.id || !sameIds(acceptedHeadCommit.meta?.accepted, pr.verdict.accepted) ||
      !sameIds(acceptedHeadCommit.meta?.rejected, pr.verdict.rejected)) {
    fail("immutable accepted-head lineage disagrees with the PR verdict");
  }

  // Only statement dependency edges and symbol refs have principled rewrites below.
  // Refuse to delete W if any other field names it: silently retaining such prose or
  // structural data would leave a semantically dangling reference even when V6 does
  // not happen to model that field.
  for (const [id, blob] of current.nodes) {
    if (id === witnessId) continue;
    const body = structuredClone(blob.body) as unknown as Record<string, unknown>;
    delete body.id;
    if (blob.node_type === "statement") {
      // Only live consumer edges are retargeted below.  Q's own resolution fields
      // are replaced; the same fields on any other tombstone are not rewritable.
      if (blob.body.resolved_by === undefined) delete body.depends_on;
      if (id === sourceId) {
        delete body.resolved_by;
        delete body.proof_basis;
      }
    } else if (blob.node_type === "symbol") {
      delete body.ref;
    }
    if (proofNodeRefs(JSON.stringify(body)).includes(witnessId)) {
      fail(`non-rewritable field of '${id}' references accepted answer '${witnessId}'`);
    }
  }

  const baseSource = statementBlob(prBase, sourceId);
  const source = statementBlob(current, sourceId);
  if (baseSource?.body.kind !== "openendedquestion" || baseSource.body.resolved_by !== undefined) {
    fail(`'${sourceId}' was not a live open-ended question on the evidence PR base`);
  }
  if (source?.body.kind !== "openendedquestion" || source.body.resolved_by !== witnessId) {
    fail(`'${sourceId}' is not resolved by the accepted answer '${witnessId}' on main`);
  }
  const { resolved_by: _currentResolution, proof_basis: _currentResolutionBasis, ...currentSourceBody } = source.body;
  if (blobId({ node_type: "statement", body: currentSourceBody }) !== blobId(baseSource)) {
    fail(`'${sourceId}' changed since the evidence PR`);
  }

  const baseTheorem = statementBlob(prBase, theoremId);
  const theorem = statementBlob(current, theoremId);
  if (baseTheorem?.body.kind !== "theorem" || baseTheorem.body.resolved_by !== undefined) {
    fail(`'${theoremId}' was not an existing live theorem on the evidence PR base`);
  }
  if (theorem?.body.kind !== "theorem" || theorem.body.resolved_by !== undefined) {
    fail(`'${theoremId}' is not a live theorem on main`);
  }
  if (contentKey(theorem) !== contentKey(baseTheorem)) fail(`the claim of '${theoremId}' changed since the evidence PR`);
  const headTheorem = statementBlob(prHead, theoremId);
  if (headTheorem === undefined || contentKey(headTheorem) !== contentKey(baseTheorem)) {
    fail(`the claim of '${theoremId}' changed on the evidence PR head`);
  }
  if (deriveStatus(current, theoremId) !== "proved" || !proofCoversCurrentClosure(current, theoremId)) {
    fail(`'${theoremId}' is not a proved theorem with a complete current basis`);
  }

  const witness = statementBlob(prHead, witnessId);
  if (witness?.body.kind !== "theorem" || witness.body.resolved_by !== undefined) {
    fail(`evidence answer '${witnessId}' is not a live theorem on the PR head`);
  }
  if (contentKey(witness) !== contentKey(headTheorem)) {
    fail(`evidence answer '${witnessId}' does not have the exact mathematical content of '${theoremId}'`);
  }
  const headSource = statementBlob(prHead, sourceId);
  if (blobId(witness) !== resolutions[0].answerIdentity || headSource === undefined ||
      blobId(headSource) !== resolutions[0].sourceIdentity || headSource.body.resolved_by !== witnessId) {
    fail(`PR ${pr.id.slice(0, 12)} does not carry its recorded '${sourceId}' to '${witnessId}' resolution`);
  }
  const { resolved_by: _resolved, proof_basis: _headResolutionBasis, ...unresolvedHeadBody } = headSource.body;
  if (blobId({ node_type: "statement", body: unresolvedHeadBody }) !== blobId(baseSource)) {
    fail(`'${sourceId}' changed within the evidence PR`);
  }
  if (deriveStatus(prHead, witnessId) !== "proved" || !proofCoversCurrentClosure(prHead, witnessId)) {
    fail(`evidence answer '${witnessId}' is not proved with a complete basis`);
  }
  const acceptedWitness = statementBlob(acceptedHead, witnessId);
  const acceptedSource = statementBlob(acceptedHead, sourceId);
  const acceptedTheorem = statementBlob(acceptedHead, theoremId);
  if (acceptedWitness === undefined || acceptedSource?.body.resolved_by !== witnessId ||
      acceptedTheorem === undefined || contentKey(acceptedTheorem) !== contentKey(baseTheorem) ||
      contentKey(acceptedWitness) !== contentKey(witness) || deriveStatus(acceptedHead, witnessId) !== "proved" ||
      !proofCoversCurrentClosure(acceptedHead, witnessId)) {
    fail(`the immutable accepted head does not contain the reviewed '${sourceId}' to '${witnessId}' resolution`);
  }
  const currentWitness = statementBlob(current, witnessId);
  if (currentWitness === undefined || contentKey(currentWitness) !== contentKey(witness) ||
      deriveStatus(current, witnessId) !== "proved" || !proofCoversCurrentClosure(current, witnessId)) {
    fail(`accepted answer '${witnessId}' is not current and proved on main`);
  }
  if (!(witness.body.depends_on ?? []).includes(theoremId) || witness.body.proof_basis?.[theoremId] === undefined) {
    fail(`evidence answer '${witnessId}' does not use '${theoremId}'`);
  }
  const proofRefs = proofNodeRefs(witness.body.proof_tex ?? "");
  if (!proofRefs.includes(theoremId)) {
    fail(`evidence answer '${witnessId}' does not cite '${theoremId}' in its proof`);
  }

  const targetClosure = contentClosure(prHead, theoremId);
  const allowed = contentClosure(prHead, sourceId);
  for (const id of targetClosure) allowed.add(id);
  const witnessClosure = contentClosure(prHead, witnessId, [witness.body.proof_tex ?? ""]);
  const actualRefs = proofNodeRefs(`${witness.body.statement}\n${witness.body.proof_tex ?? ""}`);
  const actualOutsideTarget = actualRefs.filter((id) =>
    id !== witnessId && id !== sourceId && !targetClosure.has(id));
  if (actualOutsideTarget.length > 0) {
    fail(`evidence answer '${witnessId}' cites nodes outside '${theoremId}' closure: ${actualOutsideTarget.join(", ")}`);
  }
  // Q and W are workflow nodes. Every mathematical node actually named by the
  // bridge must already belong to T's closure; broader unused dependency metadata
  // is checked separately against Q ∪ T below.
  const extra = [...witnessClosure].filter((id) => id !== witnessId && !allowed.has(id));
  if (extra.length > 0) {
    fail(`evidence answer '${witnessId}' needs context outside the question and theorem: ${extra.join(", ")}`);
  }

  const nodes = new Map(current.nodes);
  const tree = { ...current.tree };
  const { proof_basis: _oldResolutionBasis, ...sourceWithoutBasis } = source.body;
  const resolvedSource: NodeBlob = {
    node_type: "statement",
    body: { ...sourceWithoutBasis, resolved_by: theoremId },
  };
  nodes.set(sourceId, resolvedSource);
  tree[sourceId] = { ...tree[sourceId], blob: blobId(resolvedSource) };

  // Match the existing solver-resolution semantics: statement edges are derived
  // by normalization, while a symbol's semantic `ref` is changed explicitly.
  for (const { id, blob } of nodesOfType(current, "symbol")) {
    if (blob.body.ref !== sourceId && blob.body.ref !== witnessId) continue;
    const rewired: NodeBlob = { node_type: "symbol", body: { ...blob.body, ref: theoremId } };
    nodes.set(id, rewired);
    tree[id] = { ...tree[id], blob: blobId(rewired) };
  }

  // The accepted wrapper has served as the positive semantic witness. Remove its
  // duplicate node and retarget any later statement consumer to the existing theorem.
  nodes.delete(witnessId);
  delete tree[witnessId];
  for (const { id, blob } of nodesOfType({ tree, nodes }, "statement")) {
    if (id === sourceId || blob.body.resolved_by !== undefined || !(blob.body.depends_on ?? []).includes(witnessId)) continue;
    const dependencies = (blob.body.depends_on ?? []).map((dep) => dep === witnessId ? theoremId : dep)
      .filter((dep, index, all) => dep !== id && all.indexOf(dep) === index);
    const rewired: NodeBlob = { node_type: "statement", body: { ...blob.body, depends_on: dependencies } };
    nodes.set(id, rewired);
    tree[id] = { ...tree[id], blob: blobId(rewired) };
  }

  const candidate = normalizeGraph({ tree, nodes });
  const checked = checkGraph(candidate);
  if (!checked.ok) fail(`resolved graph fails checks:\n${formatViolations(checked.violations)}`);
  return candidate;
}

// The versioned theorem graph: render (graph → core.json) and its inverse
// (core.json → graph), plus the one normalization every commit passes through.
//
// `renderCore` is pure and total: statuses and `used_by` are derived, resolved
// questions are omitted, layout follows `pos`. It is the ONLY producer of
// `core.json`; the file is a view of `main` (and the orchestrator's working copy),
// never a store.
//
// `graphFromCore` inverts it for the two writers that hand the pipeline a whole
// core: the converter (an existing run's assembled core) and the orchestrator's
// direct commit (an edited `core.json`). Proof bases are carried from the previous
// graph when the proof bytes are unchanged and recomputed against the NEW graph
// when they changed — a hand-edited proof is an explicit claim that it argues the
// current tree.
//
// `normalizeGraph` runs before every commit: literal citations are wired into
// `depends_on` (existing ids only, never closing a cycle) and edges to resolved
// questions denote their answers. Render assumes a normalized graph; the checks
// refuse an unnormalized one, so no consumer needs its own copy of either rule.
import { normalizeSymbol } from "../core/symbol_names.js";
import { CoreSchema, type Core, type CoreStatement } from "../core/schema.js";
import { wireStatementProofDependencies, rebuildAssumptionUsedBy } from "../core/dependencies.js";
import { repairCoreLatexSerialization } from "../core/latex_serialization.js";
import { remapResolvedDependencies } from "../core/oeq_edges.js";
import {
  META_ID,
  bibNodeId,
  blobId,
  symbolNodeId,
  type MetaBody,
  type NodeBlob,
  type NodeId,
  type StatementBody,
} from "./node.js";
import { nodesOfType, statementBlob, type Graph } from "./graph.js";
import { computeBasis, deriveStatus } from "./validity.js";
import type { Tree } from "./store.js";

const META_FIELDS = [
  "qid", "specialization", "cluster", "target_estimand", "estimand_functional", "sampling_model",
  "comparator_promise_table", "comparator_promises", "tldr", "project_justification", "related_work",
  "interpretation", "technical_internal_limitation", "honest_scope",
] as const;

// -- graph → core -----------------------------------------------------------------

export function renderCore(g: Graph): Core {
  const meta = g.nodes.get(META_ID);
  if (meta?.node_type !== "meta") throw new Error("vcs: graph has no meta node");
  const core: Record<string, unknown> = { ...meta.body };
  core.symbols = nodesOfType(g, "symbol").map(({ blob }) => structuredClone(blob.body));
  core.assumptions = nodesOfType(g, "assumption").map(({ blob }) => structuredClone(blob.body));
  core.definitions = nodesOfType(g, "definition").map(({ blob }) => structuredClone(blob.body));
  core.statements = nodesOfType(g, "statement")
    .filter(({ blob }) => blob.body.resolved_by === undefined)
    .map(({ id, blob }) => {
      const { proof_basis: _basis, resolved_by: _resolved, ...body } = structuredClone(blob.body);
      const status = deriveStatus(g, id);
      // A cited node may carry a source transcription in `proof_tex` (legacy attested
      // fallback); it is provenance, not a proof, and renders unchanged.
      const stmt: CoreStatement = { ...(body as Omit<CoreStatement, "status">), status };
      return stmt;
    });
  core.bibliography = nodesOfType(g, "bib").map(({ blob }) => structuredClone(blob.body));
  const typed = core as unknown as Core;
  rebuildAssumptionUsedBy(typed);
  return typed;
}

// -- core → graph -----------------------------------------------------------------

/** Build an (unnormalized) graph from a core. `previous` supplies proof bases for
 *  unchanged proofs and the tombstones of resolved questions, which a core cannot
 *  carry. Every proved statement whose proof is new or changed gets a fresh basis
 *  computed against the normalized result. Returns the NORMALIZED graph. */
export function graphFromCore(coreInput: Core, previous?: Graph): Graph {
  const core = CoreSchema.parse(structuredClone(coreInput));
  repairCoreLatexSerialization(core);
  const nodes = new Map<NodeId, NodeBlob>();
  const tree: Tree = {};
  const put = (id: NodeId, blob: NodeBlob, pos: number): void => {
    if (nodes.has(id)) throw new Error(`vcs: duplicate node id '${id}' in core`);
    nodes.set(id, blob);
    tree[id] = { blob: blobId(blob), pos };
  };

  const meta: MetaBody = {};
  for (const field of META_FIELDS) if (core[field] !== undefined) meta[field] = core[field];
  put(META_ID, { node_type: "meta", body: meta }, 0);
  core.symbols.forEach((s, i) => put(symbolNodeId(s.name), { node_type: "symbol", body: s }, i));
  core.assumptions.forEach((a, i) => {
    const { used_by: _u, ...body } = a;
    put(a.id, { node_type: "assumption", body }, i);
  });
  core.definitions.forEach((d, i) => put(d.id, { node_type: "definition", body: d }, i));
  const freshBasis: NodeId[] = [];
  core.statements.forEach((s, i) => {
    const { status, ...rest } = s;
    const body: StatementBody = { ...rest };
    const prev = previous ? statementBlob(previous, s.id) : undefined;
    const proof = (s.proof_tex ?? "").trim();
    if (status === "cited") {
      delete body.proof_basis;
    } else if (proof.length === 0) {
      delete body.proof_tex;
      delete body.proof_basis;
    } else if (prev !== undefined && (prev.body.proof_tex ?? "").trim() === proof) {
      // Unchanged proof bytes keep whatever basis they had; a status flip in the
      // working copy cannot mint one (status is derived, never read back).
      if (prev.body.proof_basis !== undefined) body.proof_basis = prev.body.proof_basis;
      else delete body.proof_basis;
    } else if (previous !== undefined || status === "proved") {
      // New or changed proof bytes against a known tree: the writer asserts a proof of
      // the current claim (a hand-edited proof, a solver's proof). Status is never read
      // back; only a core with no previous graph (conversion) uses the published status
      // to tell a proof from a partial.
      freshBasis.push(s.id);
    } else {
      delete body.proof_basis; // conversion of a to-prove node with partial bytes
    }
    put(s.id, { node_type: "statement", body }, i);
  });
  // Tombstones of answered questions persist across renders.
  if (previous) {
    for (const { id, blob, pos } of nodesOfType(previous, "statement")) {
      if (blob.body.resolved_by !== undefined && !nodes.has(id)) put(id, blob, pos);
    }
  }
  core.bibliography.forEach((b, i) => put(bibNodeId(b.key), { node_type: "bib", body: b }, i));

  const normalized = normalizeGraph({ tree, nodes });
  if (freshBasis.length === 0) return normalized;
  const withBases = new Map(normalized.nodes);
  const withTree: Tree = { ...normalized.tree };
  for (const id of freshBasis) {
    const blob = statementBlob(normalized, id)!;
    const stamped: NodeBlob = { node_type: "statement", body: { ...blob.body, proof_basis: computeBasis(normalized, id) } };
    withBases.set(id, stamped);
    withTree[id] = { ...withTree[id], blob: blobId(stamped) };
  }
  return { tree: withTree, nodes: withBases };
}

// -- normalization ----------------------------------------------------------------

/** Wire literal citations into `depends_on` and remap edges to resolved questions.
 *  Idempotent; returns a new graph (inputs untouched). */
export function normalizeGraph(g: Graph): Graph {
  const resolved = new Map<NodeId, NodeId>();
  const questionDeps = new Map<NodeId, string[]>();
  for (const { id, blob } of nodesOfType(g, "statement")) {
    if (blob.body.resolved_by !== undefined) resolved.set(id, blob.body.resolved_by);
    questionDeps.set(id, blob.body.depends_on ?? []);
  }
  // Wiring reuses the core-level pass over a rendering of the live statements.
  const view: Core = renderCore(g);
  wireStatementProofDependencies(view);
  const wired = new Map(view.statements.map((s) => [s.id, s.depends_on] as const));

  const nodes = new Map(g.nodes);
  const tree: Tree = { ...g.tree };
  for (const { id, blob } of nodesOfType(g, "statement")) {
    if (blob.body.resolved_by !== undefined) continue;
    let deps = wired.get(id) ?? blob.body.depends_on ?? [];
    if (resolved.size > 0) deps = remapResolvedDependencies(id, deps, resolved, (q) => questionDeps.get(q));
    if (JSON.stringify(deps) === JSON.stringify(blob.body.depends_on ?? [])) continue;
    const next: NodeBlob = { node_type: "statement", body: { ...blob.body, depends_on: deps } };
    nodes.set(id, next);
    tree[id] = { ...tree[id], blob: blobId(next) };
  }
  // Layout is derived, never a reason to fail a check: a symbol is placed after every
  // symbol its definition references (G1's order rule), in the order it had otherwise.
  // Two units numbering their additions from the same base, or a replaced symbol that
  // now references a new one, therefore never produce an order violation — only a
  // genuine reference cycle can, and that is a content defect.
  const symbols = nodesOfType({ tree, nodes }, "symbol");
  const symIds = new Map<string, NodeId>();
  for (const { id, blob } of symbols) { symIds.set(blob.body.name, id); symIds.set(normalizeSymbol(blob.body.name), id); }
  const refsOf = (blob: Extract<NodeBlob, { node_type: "symbol" }>, self: NodeId): NodeId[] =>
    (blob.body.refs ?? []).map((r) => symIds.get(r) ?? symIds.get(normalizeSymbol(r))).filter((x): x is NodeId => x !== undefined && x !== self);
  const placed = new Set<NodeId>();
  const order: NodeId[] = [];
  let pending = symbols.map(({ id, blob }) => ({ id, deps: refsOf(blob, id) }));
  while (pending.length > 0) {
    const next = pending.find((p) => p.deps.every((d) => placed.has(d) || !pending.some((q) => q.id === d)));
    const chosen = next ?? pending[0]; // a cycle: keep the original order, G1 reports it
    placed.add(chosen.id);
    order.push(chosen.id);
    pending = pending.filter((p) => p !== chosen);
  }
  order.forEach((id, pos) => { if (tree[id].pos !== pos) tree[id] = { ...tree[id], pos }; });

  return { tree, nodes };
}

// The versioned theorem graph: the ONE validity rule.
//
// A proof is stored with its BASIS — the content key of every node in the content
// closure it was written against (its own claim, every definition / assumption /
// statement reachable through `depends_on` and literal citations, and the symbols
// those texts use). A proof is valid at a graph iff every basis node still exists
// with that content key. Nothing else is consulted: not statuses, not snapshots,
// not the edge set (a node wired in after the proof was written is not in the
// basis and does not invalidate it — a pure rewire keeps the proof).
//
// Status is derived from this rule and never stored:
//   source present            → cited
//   proof present and valid   → proved
//   otherwise                 → to-prove   (stale proof bytes stay as prior progress)
import { extractNodeRefs } from "../core/node_ids.js";
import { normalizeSymbol } from "../core/symbol_names.js";
import { contentKey, type NodeId } from "./node.js";
import { nodesOfType, statementBlob, type Graph } from "./graph.js";

export type DerivedStatus = "to-prove" | "proved" | "cited";

/** The content closure of a node: the node itself and everything its meaning rests on. */
export function contentClosure(g: Graph, rootId: NodeId, extraText: string[] = []): Set<NodeId> {
  const closure = new Set<NodeId>();
  const openQuestionIds = new Set(nodesOfType(g, "statement")
    .filter(({ blob }) => blob.body.kind === "openendedquestion")
    .map(({ id }) => id));
  const allSymbols = nodesOfType(g, "symbol").map((s) => s.id);
  // Declared names are compared the way the gate compares them (`normalizeSymbol`):
  // `$I_n$`, `\(I_n\)` and `I_n` all declare the symbol `I_n`.
  const symbolByName = new Map<string, NodeId>();
  for (const id of allSymbols) {
    const name = id.slice("sym:".length);
    symbolByName.set(name, id);
    symbolByName.set(normalizeSymbol(name), id);
  }
  const lookupSymbol = (name: string): NodeId | undefined => symbolByName.get(name) ?? symbolByName.get(normalizeSymbol(name));
  const stack: NodeId[] = [rootId];
  const pushText = (text: string | undefined): void => {
    for (const ref of extractNodeRefs(text ?? "")) if (g.nodes.has(ref) && !openQuestionIds.has(ref)) stack.push(ref);
  };
  const pushSymbols = (declared: string[] | undefined): void => {
    // Undeclared = "may use any symbol": every symbol enters the closure (conservative,
    // the same reading `declaredSymbolScope` gave a missing `free_symbols`).
    if (declared === undefined) for (const id of allSymbols) stack.push(id);
    else for (const name of declared) {
      const id = lookupSymbol(name);
      if (id !== undefined) stack.push(id);
    }
  };
  for (const text of extraText) pushText(text);
  while (stack.length > 0) {
    const id = stack.pop()!;
    if (closure.has(id)) continue;
    const blob = g.nodes.get(id);
    if (blob === undefined) continue;
    closure.add(id);
    switch (blob.node_type) {
      case "statement":
        for (const dep of blob.body.depends_on ?? []) stack.push(dep);
        pushText(blob.body.statement);
        pushText(blob.body.source?.verbatim_statement);
        pushSymbols(blob.body.free_symbols);
        break;
      case "definition":
        for (const dep of blob.body.inputs ?? []) stack.push(dep);
        for (const dep of blob.body.by_member_properties ?? []) stack.push(dep);
        for (const input of blob.body.inputs ?? []) pushText(input);
        pushText(blob.body.construction);
        pushSymbols(blob.body.free_symbols);
        break;
      case "assumption":
        pushText(blob.body.condition);
        pushSymbols(blob.body.free_symbols);
        break;
      case "symbol":
        for (const ref of blob.body.refs ?? []) {
          const sid = lookupSymbol(ref);
          if (sid !== undefined) stack.push(sid);
        }
        if (blob.body.ref !== undefined && g.nodes.has(blob.body.ref)) stack.push(blob.body.ref);
        break;
      default:
        break;
    }
  }
  return closure;
}

/** The basis a proof of `stmtId` written against `g` carries: content keys over the
 *  closure of the statement and of the proof text's own citations. */
export function computeBasis(g: Graph, stmtId: NodeId, proofText?: string): Record<NodeId, string> {
  const stmt = statementBlob(g, stmtId);
  if (stmt === undefined) throw new Error(`vcs: no statement '${stmtId}' to compute a basis for`);
  const closure = contentClosure(g, stmtId, [proofText ?? stmt.body.proof_tex ?? ""]);
  const basis: Record<NodeId, string> = {};
  for (const id of [...closure].sort()) basis[id] = contentKey(g.nodes.get(id)!);
  return basis;
}

export interface ProofVerdict {
  valid: boolean;
  /** Why not: nodes of the basis that are gone or whose content moved. Empty when valid. */
  stale: NodeId[];
  /** No proof, or a proof without a basis (partial / prior progress only). */
  reason?: "no-proof" | "no-basis";
}

export function proofVerdict(g: Graph, stmtId: NodeId): ProofVerdict {
  const stmt = statementBlob(g, stmtId);
  if (stmt === undefined || (stmt.body.proof_tex ?? "").trim().length === 0) return { valid: false, stale: [], reason: "no-proof" };
  const basis = stmt.body.proof_basis;
  if (basis === undefined) return { valid: false, stale: [], reason: "no-basis" };
  const stale: NodeId[] = [];
  for (const [id, key] of Object.entries(basis)) {
    const blob = g.nodes.get(id);
    if (blob === undefined || contentKey(blob) !== key) stale.push(id);
  }
  return { valid: stale.length === 0, stale };
}

/** Stronger than ordinary proof validity: every node in the proof's current
 * structural/textual closure is represented by its current content key. Used for
 * resolution answers, whose tombstone must never outlive an untracked rewire. */
export function proofCoversCurrentClosure(g: Graph, stmtId: NodeId): boolean {
  const stmt = statementBlob(g, stmtId);
  if (stmt === undefined || !proofVerdict(g, stmtId).valid || stmt.body.proof_basis === undefined) return false;
  const closure = contentClosure(g, stmtId, [stmt.body.proof_tex ?? ""]);
  return [...closure].every((id) => {
    const blob = g.nodes.get(id);
    return blob !== undefined && stmt.body.proof_basis?.[id] === contentKey(blob);
  });
}

export function proofValid(g: Graph, stmtId: NodeId): boolean {
  return proofVerdict(g, stmtId).valid;
}

export function deriveStatus(g: Graph, stmtId: NodeId): DerivedStatus {
  const stmt = statementBlob(g, stmtId);
  if (stmt === undefined) throw new Error(`vcs: no statement '${stmtId}'`);
  if (stmt.body.source !== undefined) return "cited";
  return proofValid(g, stmtId) ? "proved" : "to-prove";
}

/** Every live statement whose proof is present but no longer valid, with the reason. */
export function staleProofs(g: Graph): Array<{ id: NodeId; stale: NodeId[] }> {
  const out: Array<{ id: NodeId; stale: NodeId[] }> = [];
  for (const { id, blob } of nodesOfType(g, "statement")) {
    if (blob.body.resolved_by !== undefined || blob.body.source !== undefined) continue;
    const verdict = proofVerdict(g, id);
    if (!verdict.valid && verdict.reason === undefined) out.push({ id, stale: verdict.stale });
  }
  return out;
}

/** Live statements that are not settled: to-prove, whether never proved or stale. */
export function openStatements(g: Graph): NodeId[] {
  return nodesOfType(g, "statement")
    .filter(({ id, blob }) => blob.body.resolved_by === undefined && deriveStatus(g, id) === "to-prove")
    .map(({ id }) => id);
}

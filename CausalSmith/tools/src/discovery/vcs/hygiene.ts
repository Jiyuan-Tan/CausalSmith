// Graph hygiene at the D0 discharge point: orphan lemmas and dangling citations.
// Both are pure functions of a graph; the stage decides what to do about them
// (a pipeline commit that deletes the orphans; a targeted re-solve directive for
// the citers).
import { extractCitationRefs, extractNodeRefs } from "../core/node_ids.js";
import { nodesOfType, type Graph } from "./graph.js";
import type { NodeId } from "./node.js";
import { deriveStatus } from "./validity.js";

/** Live lemmas no non-lemma claim reaches through `depends_on` or a literal citation
 *  in its statement/proof. Cited lemmas are roots (literature deliverables audited by
 *  D0.5; they often appear only in related-work prose). */
export function orphanLemmas(g: Graph): NodeId[] {
  const live = nodesOfType(g, "statement").filter(({ blob }) => blob.body.resolved_by === undefined);
  const byId = new Map(live.map((s) => [s.id, s.blob.body] as const));
  const reachable = new Set<NodeId>();
  const stack: NodeId[] = [];
  for (const { id, blob } of live) {
    if (blob.body.kind !== "lemma" || deriveStatus(g, id) === "cited") {
      reachable.add(id);
      stack.push(id);
    }
  }
  while (stack.length > 0) {
    const body = byId.get(stack.pop()!);
    if (body === undefined) continue;
    const refs = new Set<string>(body.depends_on ?? []);
    for (const r of extractNodeRefs(`${body.proof_tex ?? ""} ${body.statement}`)) refs.add(r);
    for (const dep of refs) {
      if (byId.has(dep) && !reachable.has(dep)) {
        reachable.add(dep);
        stack.push(dep);
      }
    }
  }
  return live.filter(({ id, blob }) => blob.body.kind === "lemma" && !reachable.has(id)).map(({ id }) => id);
}

/** "Cite-without-emit": a non-cited statement whose statement/proof names a node id
 *  that exists nowhere in the graph (resolved questions keep their tombstone, so an
 *  answer's citation of the question it settles is not dangling). */
export function danglingCitations(g: Graph): Array<{ node: NodeId; ref: string }> {
  const known = new Set([...g.nodes.keys()].map((id) => id.toLowerCase()));
  const out: Array<{ node: NodeId; ref: string }> = [];
  const seen = new Set<string>();
  for (const { id, blob } of nodesOfType(g, "statement")) {
    if (blob.body.resolved_by !== undefined || deriveStatus(g, id) === "cited") continue;
    const declaredExternal = new Set((blob.body.external_refs ?? []).map((r) => r.slice(r.indexOf("/") + 1).toLowerCase()));
    for (const ref of extractCitationRefs(`${blob.body.proof_tex ?? ""} ${blob.body.statement}`)) {
      if (ref === id.toLowerCase() || known.has(ref) || declaredExternal.has(ref)) continue;
      const key = `${id}|${ref}`;
      if (seen.has(key)) continue;
      seen.add(key);
      out.push({ node: id, ref });
    }
  }
  return out;
}

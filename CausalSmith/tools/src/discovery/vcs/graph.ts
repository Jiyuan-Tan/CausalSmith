// The versioned theorem graph: a materialized tree and the diff between two trees.
//
// A `Graph` is a tree plus every blob it names, loaded once and treated as
// immutable. Every derived question (render, validity, checks) is a pure function
// of a Graph, so "which version is current" is answered by which Graph you hold.
import { blobMatchesId, contentKey, type NodeBlob, type NodeId } from "./node.js";
import type { Tree, VcsStore } from "./store.js";

export interface Graph {
  tree: Tree;
  nodes: Map<NodeId, NodeBlob>;
}

export async function loadGraph(store: VcsStore, commitRef: string): Promise<Graph> {
  const id = await store.resolve(commitRef);
  const commit = await store.readCommit(id);
  return loadTree(store, commit.tree);
}

export async function loadTree(store: VcsStore, tree: Tree): Promise<Graph> {
  const nodes = new Map<NodeId, NodeBlob>();
  for (const [nodeId, entry] of Object.entries(tree)) {
    const blob = await store.readBlob(entry.blob);
    if (!blobMatchesId(nodeId, blob)) {
      throw new Error(`vcs: tree files ${entry.blob} under '${nodeId}' but the blob describes a different node`);
    }
    nodes.set(nodeId, blob);
  }
  return { tree, nodes };
}

export function nodesOfType<T extends NodeBlob["node_type"]>(
  g: Graph,
  type: T,
): Array<{ id: NodeId; blob: Extract<NodeBlob, { node_type: T }>; pos: number }> {
  const out: Array<{ id: NodeId; blob: Extract<NodeBlob, { node_type: T }>; pos: number }> = [];
  for (const [id, blob] of g.nodes) {
    if (blob.node_type === type) out.push({ id, blob: blob as Extract<NodeBlob, { node_type: T }>, pos: g.tree[id].pos });
  }
  return out.sort((a, b) => a.pos - b.pos || a.id.localeCompare(b.id));
}

export function statementBlob(g: Graph, id: NodeId): Extract<NodeBlob, { node_type: "statement" }> | undefined {
  const blob = g.nodes.get(id);
  return blob?.node_type === "statement" ? blob : undefined;
}

export interface NodeChange {
  id: NodeId;
  /** Which top-level body fields differ (key-order-insensitive). */
  fields: string[];
  /** The mathematical content changed (see `contentKey`): a claim, construction,
   *  condition or symbol meaning, as opposed to prose, edges, proof or provenance. */
  content: boolean;
}

export interface GraphDiff {
  added: NodeId[];
  removed: NodeId[];
  changed: NodeChange[];
  /** Same blob, different layout position. */
  moved: NodeId[];
}

export function diffGraphs(before: Graph, after: Graph): GraphDiff {
  const diff: GraphDiff = { added: [], removed: [], changed: [], moved: [] };
  // Layout is an ORDER, not a number: a re-rendered core numbers positions 0..n-1 while
  // main may carry gaps from deletions. Compare each node's rank among the nodes both
  // trees hold, so a pure renumbering is not a move.
  const rank = (g: Graph, shared: Set<NodeId>): Map<NodeId, number> => {
    const byType = new Map<string, NodeId[]>();
    for (const id of shared) {
      const type = g.nodes.get(id)!.node_type;
      (byType.get(type) ?? byType.set(type, []).get(type)!).push(id);
    }
    const out = new Map<NodeId, number>();
    for (const ids of byType.values()) {
      ids.sort((x, y) => g.tree[x].pos - g.tree[y].pos || x.localeCompare(y));
      ids.forEach((id, i) => out.set(id, i));
    }
    return out;
  };
  const shared = new Set(Object.keys(before.tree).filter((id) => after.tree[id] !== undefined));
  const rankBefore = rank(before, shared);
  const rankAfter = rank(after, shared);
  const ids = new Set([...Object.keys(before.tree), ...Object.keys(after.tree)]).values();
  for (const id of [...ids].sort()) {
    const a = before.tree[id];
    const b = after.tree[id];
    if (a === undefined) diff.added.push(id);
    else if (b === undefined) diff.removed.push(id);
    else if (a.blob !== b.blob) {
      const x = before.nodes.get(id)!;
      const y = after.nodes.get(id)!;
      diff.changed.push({ id, fields: changedFields(x, y), content: contentKey(x) !== contentKey(y) });
    } else if (rankBefore.get(id) !== rankAfter.get(id)) diff.moved.push(id);
  }
  return diff;
}

export function isEmptyDiff(d: GraphDiff): boolean {
  return d.added.length + d.removed.length + d.changed.length + d.moved.length === 0;
}

function changedFields(a: NodeBlob, b: NodeBlob): string[] {
  const x = a.body as Record<string, unknown>;
  const y = b.body as Record<string, unknown>;
  const keys = new Set([...Object.keys(x), ...Object.keys(y)]);
  const out: string[] = [];
  for (const key of [...keys].sort()) {
    if (JSON.stringify(sortKeys(x[key])) !== JSON.stringify(sortKeys(y[key]))) out.push(key);
  }
  return out;
}

function sortKeys(value: unknown): unknown {
  if (Array.isArray(value)) return value.map(sortKeys);
  if (value !== null && typeof value === "object") {
    const o = value as Record<string, unknown>;
    return Object.fromEntries(Object.keys(o).filter((k) => o[k] !== undefined).sort().map((k) => [k, sortKeys(o[k])]));
  }
  return value;
}

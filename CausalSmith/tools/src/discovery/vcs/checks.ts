// The versioned theorem graph: what a tree must satisfy to become a commit.
//
// One function, run on every candidate tree whatever produced it (converter,
// solver PR, orchestrator edit, merge). The rendered core must pass the existing
// structural gate (schema + G1–G7); the rest is what only the graph can see.
import { runStructuralGate } from "../core/gate.js";
import { extractNodeRefs } from "../core/node_ids.js";
import type { Core } from "../core/schema.js";
import { blobMatchesId, META_ID, nodeTypeOf, type NodeId } from "./node.js";
import { nodesOfType, type Graph } from "./graph.js";
import { deriveStatus, proofCoversCurrentClosure } from "./validity.js";
import { renderCore, normalizeGraph } from "./render.js";
import { stableJson } from "../../shared/stable_json.js";

export interface Violation {
  code: string;
  where: string;
  message: string;
}

export interface CheckResult {
  ok: boolean;
  violations: Violation[];
  /** The rendered core when it could be rendered (also returned on failure for diagnosis). */
  core?: Core;
}

export function checkGraph(g: Graph): CheckResult {
  const violations: Violation[] = [];
  const v = (code: string, where: string, message: string): void => { violations.push({ code, where, message }); };

  // V1: every tree entry is a blob of the type its id says.
  if (!g.nodes.has(META_ID)) v("V1", META_ID, "graph has no meta node");
  for (const [id, blob] of g.nodes) {
    if (nodeTypeOf(id) === null) v("V1", id, "id is outside the node grammar");
    else if (!blobMatchesId(id, blob)) v("V1", id, `blob describes a different node (${blob.node_type})`);
    if (g.tree[id] === undefined) v("V1", id, "node loaded without a tree entry");
  }
  for (const id of Object.keys(g.tree)) if (!g.nodes.has(id)) v("V1", id, "tree entry without a loaded node");

  // V2: resolved questions point at live theorems; nothing live depends on a resolved question.
  const resolved = new Set<NodeId>();
  for (const { id, blob } of nodesOfType(g, "statement")) {
    if (blob.body.resolved_by === undefined) continue;
    resolved.add(id);
    const answer = g.nodes.get(blob.body.resolved_by);
    if (answer?.node_type !== "statement") v("V2", id, `resolved_by '${blob.body.resolved_by}' is not a statement`);
    else if (answer.body.resolved_by !== undefined) v("V2", id, `resolved_by '${blob.body.resolved_by}' is itself resolved`);
    else if (answer.body.kind !== "theorem" || deriveStatus(g, blob.body.resolved_by) !== "proved" || !proofCoversCurrentClosure(g, blob.body.resolved_by)) v("V2", id, `resolved_by '${blob.body.resolved_by}' is not a proved theorem with a complete current basis`);
  }
  for (const { id, blob } of nodesOfType(g, "statement")) {
    if (blob.body.resolved_by !== undefined) continue;
    for (const dep of blob.body.depends_on ?? []) {
      if (resolved.has(dep)) v("V2", id, `depends_on '${dep}', a resolved question (edges must denote the answer)`);
    }
  }
  for (const { id, blob } of nodesOfType(g, "symbol")) {
    if (blob.body.ref !== undefined && resolved.has(blob.body.ref)) v("V2", id, `ref '${blob.body.ref}', a resolved question`);
  }
  for (const { id, blob } of nodesOfType(g, "definition")) {
    for (const ref of blob.body.by_member_properties ?? []) if (resolved.has(ref)) v("V2", id, `by_member_properties '${ref}', a resolved question`);
    for (const input of blob.body.inputs ?? []) for (const ref of extractNodeRefs(input)) if (resolved.has(ref)) v("V2", id, `input '${ref}', a resolved question`);
    for (const ref of extractNodeRefs(blob.body.construction)) if (resolved.has(ref)) v("V2", id, `construction references '${ref}', a resolved question`);
  }
  for (const { id, blob } of nodesOfType(g, "assumption")) {
    for (const ref of extractNodeRefs(blob.body.condition)) if (resolved.has(ref)) v("V2", id, `condition references '${ref}', a resolved question`);
  }

  // V3: the graph is normalized (wiring / remap is a fixed point). Comparing trees
  // is exact: normalization is deterministic and idempotent.
  if (violations.length === 0) {
    const normalized = normalizeGraph(g);
    const drift = Object.keys(normalized.tree).filter((id) => normalized.tree[id].blob !== g.tree[id]?.blob);
    for (const id of drift) v("V3", id, "not normalized: literal citations or resolved-question edges are not reflected in depends_on");
  }

  // V4: proof bases are well-formed.
  for (const { id, blob } of nodesOfType(g, "statement")) {
    const basis = blob.body.proof_basis;
    if (basis === undefined) continue;
    if ((blob.body.proof_tex ?? "").trim().length === 0) v("V4", id, "proof_basis without a proof");
    if (blob.body.source !== undefined) v("V4", id, "a cited statement carries a proof_basis");
    for (const [node, key] of Object.entries(basis)) {
      if (!/^[a-f0-9]{64}$/.test(key)) v("V4", id, `proof_basis['${node}'] is not a content key`);
    }
    if (basis[id] === undefined) v("V4", id, "proof_basis does not cover the statement's own claim");
  }

  // V6: every structural reference resolves (the gate covers statement `depends_on`;
  // definitions, assumptions and symbols also point at nodes).
  for (const { id, blob } of nodesOfType(g, "definition")) {
    for (const ref of blob.body.by_member_properties ?? []) if (!g.nodes.has(ref)) v("V6", id, `by_member_properties '${ref}' does not exist`);
    for (const input of blob.body.inputs ?? []) for (const ref of extractNodeRefs(input)) if (!g.nodes.has(ref)) v("V6", id, `input '${ref}' does not exist`);
  }
  for (const { id, blob } of nodesOfType(g, "symbol")) {
    if (blob.body.ref !== undefined && nodeTypeOf(blob.body.ref) !== null && !g.nodes.has(blob.body.ref)) v("V6", id, `ref '${blob.body.ref}' does not exist`);
  }
  for (const { id, blob } of nodesOfType(g, "statement")) {
    if (blob.body.resolved_by !== undefined) continue;
    for (const dep of blob.body.depends_on ?? []) if (!g.nodes.has(dep)) v("V6", id, `depends_on '${dep}' does not exist`);
  }

  if (violations.length > 0) return { ok: false, violations };

  // G1–G7 + schema on the rendered core.
  let core: Core;
  try {
    core = renderCore(g);
  } catch (err) {
    v("render", "<graph>", err instanceof Error ? err.message : String(err));
    return { ok: false, violations };
  }
  const gate = runStructuralGate(core);
  for (const gv of gate.violations) v(gv.code, gv.where, gv.message);
  return { ok: violations.length === 0, violations, core };
}

export function formatViolations(violations: Violation[]): string {
  return violations.map((x) => `  [${x.code}] ${x.where}: ${x.message}`).join("\n");
}

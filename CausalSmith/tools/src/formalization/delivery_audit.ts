import { STAGE_ORDER } from "../constants.js";
import type { Core } from "../discovery/core/schema.js";
import { statementHash } from "../graph/hash.js";
import { parseAnnotatedDecls, type ExtractedDecl } from "../graph/extractor.js";
import { isUndeliveredNode, type FormalizationGraph } from "../graph/types.js";
import type { CitedReviewReceipt, DeliveryReviewReceipt } from "../types.js";
import { runPlanGate } from "./plan/plan_gate.js";
import type { Plan } from "./plan/schema.js";

const DEP_KINDS = new Set(["statement-uses", "proof-uses"]);

export interface DeliveryAuditFinding {
  code: "plan" | "plan-graph" | "dependency" | "lean-anchor" | "stage" | "review" | "cited-review" | "convergence-review";
  node_id?: string;
  message: string;
}

/** Hash the exact frozen-core/plan/graph/Lean interface a cited peer receipt certifies. */
export function citedEvidenceHash(
  core: Core,
  plan: Plan,
  graph: FormalizationGraph,
  nodeId: string,
  leanEvidence: string,
): string {
  const planNode = plan.nodes[nodeId];
  const citation = plan.citations.find((candidate) => candidate.id === planNode?.source);
  const graphNode = graph.nodes.find((candidate) => candidate.id === nodeId);
  const coreStatement = core.statements.find((candidate) => candidate.id === nodeId);
  return statementHash(JSON.stringify({
    node_id: nodeId,
    core_statement: coreStatement ?? null,
    plan_node: planNode ? {
      lean_name: planNode.lean_name,
      lean_kind: planNode.lean_kind,
      gate_class: planNode.gate_class ?? null,
      source: planNode.source ?? null,
      delivery_status: planNode.delivery_status,
    } : null,
    citation: citation ?? null,
    graph_node: graphNode ? {
      nl_statement: graphNode.nl.statement,
      lean: graphNode.lean,
      gate: graphNode.gate ?? null,
      review_hash: graphNode.review.passed_hash,
      delivery: graphNode.delivery ?? null,
    } : null,
    lean_evidence: leanEvidence,
  }));
}

/**
 * Bind a cited review to the current tagged declaration and its direct source body. The direct
 * source starts at the declaration header, so F5 may add a preceding docstring without
 * invalidating F4, while a later type/body/proof edit still forces a fresh review.
 */
export async function citedLeanEvidence(
  leanDir: string,
  plan: Plan,
  graph: FormalizationGraph,
): Promise<Record<string, string>> {
  const evidence: Record<string, string> = {};
  const decls = await parseAnnotatedDecls(leanDir);
  for (const [nodeId, node] of Object.entries(plan.nodes)) {
    if ((node.gate_class !== "cited" && node.citation_discharged !== true) || node.delivery_status === "undelivered") continue;
    const owned = decls.filter((decl) => decl.nodeId === nodeId);
    evidence[nodeId] = statementHash(JSON.stringify(owned.map((decl) => ({
      file: decl.file,
      declKind: decl.declKind,
      declName: decl.declName,
      statement: decl.statement,
      hasSorry: decl.hasSorry,
      sourceHash: decl.sourceHash ?? null,
    }))));
  }
  return evidence;
}

const CITED_PASS = new Set(["cited-verified", "cited-verified-attested", "cited-source-unverifiable"]);

/** Require one current source-bound receipt from each F4 peer for every delivered cited node. */
export function auditCitedReview(args: {
  core: Core;
  plan: Plan;
  graph: FormalizationGraph;
  leanEvidence: Record<string, string>;
  receipts?: CitedReviewReceipt[];
}): DeliveryAuditFinding[] {
  const findings: DeliveryAuditFinding[] = [];
  const receipts = args.receipts ?? [];
  const graphById = new Map(args.graph.nodes.map((node) => [node.id, node] as const));
  const citationById = new Map(args.plan.citations.map((citation) => [citation.id, citation] as const));
  const frozenCitedIds = new Set(args.core.statements.filter((statement) => statement.status === "cited").map((statement) => statement.id));

  // Enforce the inverse inventory first. Otherwise a graph-only cited gate (or a graph relabel of
  // an ordinary plan node) is absent from the plan-driven loop below and needs no receipts at all.
  for (const graphNode of args.graph.nodes) {
    if (graphNode.gate?.gate_class !== "cited" || isUndeliveredNode(graphNode)) continue;
    const planNode = args.plan.nodes[graphNode.id];
    if (!planNode || planNode.gate_class !== "cited" || planNode.delivery_status === "undelivered") {
      findings.push({
        code: "cited-review",
        node_id: graphNode.id,
        message: "delivered cited graph node is absent from the authoritative plan cited inventory",
      });
      continue;
    }
    if (graphNode.gate.source !== planNode.source) {
      findings.push({
        code: "cited-review",
        node_id: graphNode.id,
        message: `plan/graph cited source drift (plan=${planNode.source ?? "missing"}; graph=${graphNode.gate.source ?? "missing"})`,
      });
    }
  }
  for (const [nodeId, planNode] of Object.entries(args.plan.nodes)) {
    if (!frozenCitedIds.has(nodeId) || planNode.delivery_status === "undelivered") continue;
    const citation = planNode.source ? citationById.get(planNode.source) : undefined;
    const graphNode = graphById.get(nodeId);
    const deferred = planNode.gate_class === "cited";
    const discharged = planNode.citation_discharged === true &&
      (planNode.lean_kind === "lemma" || planNode.lean_kind === "theorem") && planNode.disposition !== "reuse";
    if (!citation || !graphNode || (!deferred && !discharged) || (deferred && graphNode.gate?.gate_class !== "cited")) {
      findings.push({
        code: "cited-review",
        node_id: nodeId,
        message: !citation
          ? "delivered cited node has no resolvable plan citation"
          : !graphNode
            ? "delivered cited node is missing from graph"
            : !deferred && !discharged
              ? "frozen cited node is neither a deferred cited carrier nor a locally discharged theorem"
              : "deferred cited plan node is not classified as cited in graph",
      });
      continue;
    }
    if (deferred && graphNode.gate?.source !== planNode.source) {
      // Already an inventory failure; do not let receipts against either side make it pass.
      continue;
    }
    const leanEvidence = args.leanEvidence[nodeId];
    if (!leanEvidence) {
      findings.push({ code: "cited-review", node_id: nodeId, message: "current cited Lean evidence is missing" });
      continue;
    }
    const expectedHash = citedEvidenceHash(args.core, args.plan, args.graph, nodeId, leanEvidence);
    for (const reviewer of ["codex", "claude"] as const) {
      const matches = receipts.filter((receipt) => receipt.node_id === nodeId && receipt.reviewer === reviewer);
      if (matches.length !== 1) {
        findings.push({ code: "cited-review", node_id: nodeId, message: `expected exactly one ${reviewer} cited-source receipt, found ${matches.length}` });
        continue;
      }
      const receipt = matches[0];
      if (receipt.cite_id !== citation.id || receipt.locator !== citation.locator) {
        findings.push({ code: "cited-review", node_id: nodeId, message: `${reviewer} cited receipt targets a different source or locator` });
      }
      if (!CITED_PASS.has(receipt.check_status)) {
        findings.push({ code: "cited-review", node_id: nodeId, message: `${reviewer} cited-source verdict is ${receipt.check_status}` });
      }
      if (receipt.evidence_hash !== expectedHash) {
        findings.push({ code: "cited-review", node_id: nodeId, message: `${reviewer} cited receipt is stale for the current source interface` });
      }
    }
  }
  return findings;
}

function deliveryConsumers(graph: FormalizationGraph, nodeId: string): string[] {
  const reverse = new Map<string, string[]>();
  for (const edge of graph.edges) {
    if (!DEP_KINDS.has(edge.kind)) continue;
    const xs = reverse.get(edge.to) ?? [];
    xs.push(edge.from);
    reverse.set(edge.to, xs);
  }
  const byId = new Map(graph.nodes.map((node) => [node.id, node] as const));
  const seen = new Set<string>();
  const delivered: string[] = [];
  const stack = [...(reverse.get(nodeId) ?? [])];
  while (stack.length > 0) {
    const id = stack.pop()!;
    if (seen.has(id)) continue;
    seen.add(id);
    const node = byId.get(id);
    if (node && !isUndeliveredNode(node)) delivered.push(`${node.id}:${node.kind}`);
    stack.push(...(reverse.get(id) ?? []));
  }
  return delivered.sort();
}

/** Hash exactly the durable evidence that licenses omission. */
export function deliveryEvidenceHash(
  core: Core,
  plan: Plan,
  graph: FormalizationGraph,
  nodeId: string,
): string {
  const node = graph.nodes.find((candidate) => candidate.id === nodeId);
  const planNode = plan.nodes[nodeId];
  const statement = core.statements.find((candidate) => candidate.id === nodeId);
  return statementHash(JSON.stringify({
    node_id: nodeId,
    contribution: {
      tldr: core.tldr ?? null,
      honest_scope: core.honest_scope ?? null,
      project_justification: core.project_justification ?? null,
    },
    statement: statement ?? null,
    plan_delivery: planNode ? {
      role: planNode.delivery_role ?? null,
      status: planNode.delivery_status,
      reason: planNode.delivery_reason ?? null,
      gate: planNode.gate,
      gate_class: planNode.gate_class ?? null,
    } : null,
    graph_delivery: node ? {
      kind: node.kind,
      delivery: node.delivery ?? null,
      gate: node.gate ?? null,
    } : null,
    delivered_consumers: deliveryConsumers(graph, nodeId),
  }));
}

export function auditDelivery(args: {
  core: Core;
  plan: Plan;
  graph: FormalizationGraph;
  leanDeclNames?: Iterable<string>;
  annotatedDecls?: ExtractedDecl[];
  stageCompleted?: string;
  requireFinalStage?: boolean;
  receipts?: DeliveryReviewReceipt[];
  requireReceipts?: boolean;
}): DeliveryAuditFinding[] {
  const findings: DeliveryAuditFinding[] = [];
  const gate = runPlanGate(args.plan, args.core, {
    annotatedDecls: args.annotatedDecls,
    // The checks below validate exactly one fresh codex and claude receipt for
    // every omitted node. Without that required receipt mode, retain F1's
    // fail-closed ban on planner-authored secondary omissions.
    allowReviewedSecondaryUndelivered: args.requireReceipts === true,
  });
  // P5/P6 are advisory planning-quality checks. Every other plan invariant is structural and
  // must still hold at F5/banking; otherwise a post-F2 edit can bypass the earlier gate.
  for (const violation of gate.violations.filter((v) => v.code !== "P5" && v.code !== "P6")) {
    findings.push({ code: "plan", node_id: violation.where, message: `${violation.code}: ${violation.message}` });
  }

  const graphById = new Map(args.graph.nodes.map((node) => [node.id, node] as const));
  const undeliveredIds = Object.entries(args.plan.nodes)
    .filter(([, node]) => node.delivery_status === "undelivered")
    .map(([id]) => id)
    .sort();

  for (const [id, planNode] of Object.entries(args.plan.nodes)) {
    const graphNode = graphById.get(id);
    if (!graphNode) {
      findings.push({ code: "plan-graph", node_id: id, message: "plan node is missing from graph" });
      continue;
    }
    const graphStatus = graphNode.delivery?.status ?? "deliver";
    const graphRole = graphNode.delivery?.role;
    const graphReason = graphNode.delivery?.reason;
    if (graphStatus !== planNode.delivery_status || graphRole !== planNode.delivery_role || graphReason !== planNode.delivery_reason) {
      findings.push({
        code: "plan-graph",
        node_id: id,
        message: `delivery metadata drift (plan=${planNode.delivery_status}/${planNode.delivery_role ?? "none"}/${planNode.delivery_reason ?? "none"}; graph=${graphStatus}/${graphRole ?? "none"}/${graphReason ?? "none"})`,
      });
    }
  }

  // Plan/core are the authoritative delivery inventory. A graph-only undelivered node would
  // otherwise become a phantom presentation remark with no discovery or planning owner.
  const coreIds = new Set([
    ...args.core.assumptions.map((node) => node.id),
    ...args.core.definitions.map((node) => node.id),
    ...args.core.statements.map((node) => node.id),
  ]);
  for (const graphNode of args.graph.nodes.filter(isUndeliveredNode)) {
    const planNode = args.plan.nodes[graphNode.id];
    if (!planNode || planNode.delivery_status !== "undelivered") {
      findings.push({
        code: "plan-graph",
        node_id: graphNode.id,
        message: "graph-only undelivered node is absent from the authoritative plan delivery inventory",
      });
    }
    if (!coreIds.has(graphNode.id)) {
      findings.push({
        code: "plan-graph",
        node_id: graphNode.id,
        message: "undelivered graph node is absent from the corrected core",
      });
    }
  }

  const declNames = new Set<string>();
  for (const name of args.leanDeclNames ?? []) {
    declNames.add(name);
    declNames.add(name.split(".").at(-1) ?? name);
  }
  for (const id of undeliveredIds) {
    const planNode = args.plan.nodes[id];
    const graphNode = graphById.get(id);
    if (!graphNode || !isUndeliveredNode(graphNode)) continue;
    if (graphNode.lean.decl_name || graphNode.lean.file) {
      findings.push({ code: "lean-anchor", node_id: id, message: "undelivered node retains a Lean anchor" });
    }
    const shortName = planNode.lean_name.split(".").at(-1) ?? planNode.lean_name;
    if (declNames.has(planNode.lean_name) || declNames.has(shortName)) {
      findings.push({ code: "lean-anchor", node_id: id, message: `Lean declaration '${planNode.lean_name}' exists for an undelivered node` });
    }
    const consumers = deliveryConsumers(args.graph, id);
    if (consumers.length > 0) {
      findings.push({ code: "dependency", node_id: id, message: `delivered transitive consumers: ${consumers.join(", ")}` });
    }
  }

  if (args.requireFinalStage) {
    const current = STAGE_ORDER.indexOf(args.stageCompleted as (typeof STAGE_ORDER)[number]);
    const required = STAGE_ORDER.indexOf("5");
    if (current < required) {
      findings.push({ code: "stage", message: `accepted delivery audit requires stage 5 (found ${args.stageCompleted ?? "missing"})` });
    }
  }

  if (args.requireReceipts) {
    const receipts = args.receipts ?? [];
    for (const id of undeliveredIds) {
      const expectedHash = deliveryEvidenceHash(args.core, args.plan, args.graph, id);
      for (const reviewer of ["codex", "claude"] as const) {
        const matches = receipts.filter((receipt) => receipt.node_id === id && receipt.reviewer === reviewer);
        if (matches.length !== 1) {
          findings.push({ code: "review", node_id: id, message: `expected exactly one ${reviewer} delivery receipt, found ${matches.length}` });
          continue;
        }
        const receipt = matches[0];
        if (receipt.verdict !== "matched") {
          findings.push({ code: "review", node_id: id, message: `${reviewer} rejected the omission${receipt.note ? `: ${receipt.note}` : ""}` });
        }
        if (receipt.evidence_hash !== expectedHash) {
          findings.push({ code: "review", node_id: id, message: `${reviewer} receipt is stale for the current delivery evidence` });
        }
      }
    }
  }
  return findings;
}

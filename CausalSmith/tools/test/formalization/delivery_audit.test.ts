import { describe, expect, it } from "vitest";
import type { Core } from "../../src/discovery/core/schema.js";
import { auditCitedReview, citedEvidenceHash, deliveryEvidenceHash, auditDelivery } from "../../src/formalization/delivery_audit.js";
import { PlanSchema } from "../../src/formalization/plan/schema.js";
import { GraphSchema } from "../../src/graph/types.js";

const core: Core = {
  qid: "q",
  specialization: "v1",
  symbols: [],
  assumptions: [],
  definitions: [],
  statements: [{ id: "thm:atlas", kind: "theorem", statement: "exact atlas", depends_on: [], status: "proved" }],
  target_estimand: "causal arrow",
  bibliography: [],
  tldr: "The delivered contribution recovers the arrow; the atlas is secondary.",
};

const plan = PlanSchema.parse({
  qid: "q",
  specialization: "v1",
  env: [],
  nodes: {
    "thm:atlas": {
      lean_kind: "theorem",
      lean_name: "exactRealAtlas",
      disposition: "define-local",
      delivery_role: "secondary",
      delivery_status: "undelivered",
      delivery_reason: "major non-headline CAD substrate",
    },
  },
  citations: [],
  feasibility: "formalizable-now",
});

const graph = GraphSchema.parse({
  qid: "q",
  specialization: "v1",
  nodes: [{
    id: "thm:atlas",
    kind: "theorem",
    provenance: "from-note",
    nl: { statement: "exact atlas", tex_anchor: "", frozen: true },
    lean: { decl_name: null, file: null },
    review: { status: "matched", passed_hash: null },
    proof: { state: "complete", sorry_count: 0 },
    delivery: { role: "secondary", status: "undelivered", reason: "major non-headline CAD substrate" },
  }],
  edges: [],
});

describe("undelivered delivery audit", () => {
  it("accepts exactly two current independent receipts", () => {
    const evidence_hash = deliveryEvidenceHash(core, plan, graph, "thm:atlas");
    expect(auditDelivery({
      core,
      plan,
      graph,
      stageCompleted: "5",
      requireFinalStage: true,
      requireReceipts: true,
      receipts: [
        { node_id: "thm:atlas", reviewer: "codex", verdict: "matched", evidence_hash },
        { node_id: "thm:atlas", reviewer: "claude", verdict: "matched", evidence_hash },
      ],
    })).toEqual([]);
  });

  it("rejects a stale untagged Lean declaration and missing peer receipt", () => {
    const evidence_hash = deliveryEvidenceHash(core, plan, graph, "thm:atlas");
    const findings = auditDelivery({
      core,
      plan,
      graph,
      leanDeclNames: ["Namespace.exactRealAtlas"],
      stageCompleted: "4",
      requireFinalStage: true,
      requireReceipts: true,
      receipts: [{ node_id: "thm:atlas", reviewer: "codex", verdict: "matched", evidence_hash }],
    });
    expect(findings.some((finding) => finding.code === "lean-anchor")).toBe(true);
    expect(findings.some((finding) => finding.code === "stage")).toBe(true);
    expect(findings.some((finding) => finding.code === "review" && /claude/.test(finding.message))).toBe(true);
  });

  it("rejects plan/graph delivery drift", () => {
    const changed = {
      ...graph,
      nodes: graph.nodes.map((node) => ({
        ...node,
        delivery: { ...node.delivery!, reason: "different reason" },
      })),
    };
    expect(auditDelivery({ core, plan, graph: changed }).some((finding) => finding.code === "plan-graph")).toBe(true);
  });

  it("rejects a graph-only undelivered phantom absent from plan and core", () => {
    const emptyPlan = PlanSchema.parse({
      qid: "q", specialization: "v1", env: [], nodes: {}, citations: [], feasibility: "formalizable-now",
    });
    const phantomGraph = {
      ...graph,
      nodes: [{ ...graph.nodes[0], id: "thm:phantom" }],
    };
    const findings = auditDelivery({ core: { ...core, statements: [] }, plan: emptyPlan, graph: phantomGraph });
    expect(findings.some((finding) => finding.code === "plan-graph" && /graph-only/.test(finding.message))).toBe(true);
    expect(findings.some((finding) => finding.code === "plan-graph" && /corrected core/.test(finding.message))).toBe(true);
  });
});

describe("cited F4 receipt audit", () => {
  const citedCore: Core = {
    ...core,
    statements: [{
      id: "lem:source", kind: "lemma", statement: "For every x, P x.", depends_on: [], status: "cited",
      source: { cite: "source", locator: "Theorem 2", carrier: "logical-claim", verbatim_statement: "For every x, P x." },
    }],
  };
  const leanEvidence = { "lem:source": "current-lean-digest" };
  const citedPlan = PlanSchema.parse({
    qid: "q",
    specialization: "v1",
    env: [],
    nodes: {
      "lem:source": {
        lean_kind: "assumption",
        lean_name: "sourceInterface",
        disposition: "define-local",
        gate: true,
        gate_class: "cited",
        source: "cite:source",
      },
    },
    citations: [{
      id: "cite:source", title: "Source", authors: "A", year: 2020,
      locator: "Theorem 2", verbatim_statement: "For every x, P x.",
    }],
    feasibility: "formalizable-now",
  });
  const citedGraph = {
    qid: "q",
    specialization: "v1",
    nodes: [{
      id: "lem:source",
      kind: "gate" as const,
      provenance: "from-note" as const,
      nl: { statement: "source interface", tex_anchor: "", frozen: true },
      lean: { decl_name: "sourceInterface", file: "Basic.lean" },
      review: { status: "matched" as const, passed_hash: "h" },
      proof: { state: "complete" as const, sorry_count: 0 },
      gate: { gate_class: "cited" as const, source: "cite:source" },
    }],
    edges: [],
  };

  it("requires one current cite-id-and-locator receipt from each peer", () => {
    const evidence_hash = citedEvidenceHash(citedCore, citedPlan, citedGraph, "lem:source", leanEvidence["lem:source"]);
    expect(auditCitedReview({
      core: citedCore,
      plan: citedPlan,
      graph: citedGraph,
      leanEvidence,
      receipts: [
        { node_id: "lem:source", reviewer: "codex", check_status: "cited-verified-attested", cite_id: "cite:source", locator: "Theorem 2", evidence_hash },
        { node_id: "lem:source", reviewer: "claude", check_status: "cited-verified-attested", cite_id: "cite:source", locator: "Wrong theorem", evidence_hash },
      ],
    }).some((finding) => /different source or locator/.test(finding.message))).toBe(true);
  });

  it("invalidates cited receipts when the plan carrier kind changes", () => {
    const before = citedEvidenceHash(citedCore, citedPlan, citedGraph, "lem:source", leanEvidence["lem:source"]);
    const changed = structuredClone(citedPlan);
    changed.nodes["lem:source"].lean_kind = "def";
    expect(citedEvidenceHash(citedCore, changed, citedGraph, "lem:source", leanEvidence["lem:source"])).not.toBe(before);
    expect(citedEvidenceHash(citedCore, citedPlan, citedGraph, "lem:source", "edited-lean-digest")).not.toBe(before);
  });

  it("keeps a locally discharged citation in the source-receipt inventory", () => {
    const discharged = structuredClone(citedPlan);
    Object.assign(discharged.nodes["lem:source"], {
      lean_kind: "theorem", gate: false, gate_class: undefined,
      citation_discharged: true, target_file: "Source.lean", hyps: [],
    });
    const dischargedGraph = {
      ...citedGraph,
      nodes: [{ ...citedGraph.nodes[0], kind: "theorem" as const, gate: undefined }],
    };
    const oldHash = citedEvidenceHash(citedCore, citedPlan, citedGraph, "lem:source", leanEvidence["lem:source"]);
    const findings = auditCitedReview({
      core: citedCore, plan: discharged, graph: dischargedGraph,
      leanEvidence: { "lem:source": "discharged-theorem-digest" },
      receipts: [
        { node_id: "lem:source", reviewer: "codex", check_status: "cited-verified", cite_id: "cite:source", locator: "Theorem 2", evidence_hash: oldHash },
        { node_id: "lem:source", reviewer: "claude", check_status: "cited-verified", cite_id: "cite:source", locator: "Theorem 2", evidence_hash: oldHash },
      ],
    });
    expect(findings.filter((finding) => /stale/.test(finding.message))).toHaveLength(2);
  });

  it("rejects a graph-only delivered cited node even when the plan is empty", () => {
    const emptyPlan = PlanSchema.parse({
      qid: "q", specialization: "v1", env: [], nodes: {}, citations: [], feasibility: "formalizable-now",
    });
    expect(auditCitedReview({ core: citedCore, plan: emptyPlan, graph: citedGraph, leanEvidence, receipts: [] }).some(
      (finding) => /absent from the authoritative plan cited inventory/.test(finding.message),
    )).toBe(true);
  });
});

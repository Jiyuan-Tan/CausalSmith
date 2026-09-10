import { describe, it, expect } from "vitest";
import {
  actionForFinding,
  renderRoutingPlan,
  KIND_ACTION,
  partitionFindings,
  findingFingerprint,
  requiresNewResearch,
} from "../src/presentation/revision_routing.js";
import type { ReviewFinding } from "../src/presentation/revision_brief.js";

const f = (kind: ReviewFinding["kind"], section = "s"): ReviewFinding => ({
  severity: "major",
  section,
  issue: "i",
  fix: "x",
  kind,
});

describe("hand revision routing", () => {
  it("maps each kind to its orchestrator action", () => {
    expect(KIND_ACTION.prose).toEqual({ type: "revise" });
    expect(KIND_ACTION.structure).toEqual({ type: "revise" });
    expect(KIND_ACTION.statement).toEqual({ type: "escalate" });
    expect(KIND_ACTION.citation).toEqual({ type: "decide" });
    expect(KIND_ACTION.other).toEqual({ type: "decide" });
  });
  it("treats an absent kind as `other` → decide", () => {
    expect(actionForFinding(f(undefined))).toEqual({ type: "decide" });
  });
  it("renders a plan grouping by action incl. an out-of-scope + decide section", () => {
    const md = renderRoutingPlan({
      recommendation: "major_revision",
      findings: [f("prose"), { ...f("structure", "global"), issue: "retitle the paper" }, f("statement"), f("other")],
    });
    expect(md).toContain("fix by hand in the authored sources");
    expect(md).not.toContain("rewind P");
    expect(md).toContain("escalate");
    expect(md).toMatch(/your call|decide/i);
  });
  it("routes only rewrite findings to the hand-revision bucket", () => {
    const p = partitionFindings([f("prose"), f("structure"), f("statement"), f("citation"), f("other")]);
    expect(p.repairable).toHaveLength(2);
    expect(p.blocked).toHaveLength(3);
  });
  it("routes local and paper-wide structure findings alike to hand revision", () => {
    const local = { ...f("structure", "Discussion"), issue: "paragraph is hard to follow" };
    const global = { ...f("structure", "global"), issue: "reframe the contribution for econometric readers" };
    expect(actionForFinding(local)).toEqual({ type: "revise" });
    expect(actionForFinding(global)).toEqual({ type: "revise" });
  });
  it("trusts a structured `rewrite` remedy over research keywords in the suggested fix", () => {
    const f = { kind: "prose", section: "Introduction", severity: "minor", remedy: "rewrite",
      issue: "The phrase 'a sharp summary-inversion set' suggests an optimality result that is not stated.",
      fix: "Replace 'sharp' with 'exact' unless the authors add and prove a formal sharpness criterion." } as ReviewFinding;
    expect(requiresNewResearch(f)).toBe(false);
    expect(actionForFinding(f)).toEqual({ type: "revise" });
    // Without a remedy the keyword fallback still applies.
    expect(requiresNewResearch({ ...f, remedy: undefined })).toBe(true);
  });

  it("blocks new-research remedies and uses stable issue ids", () => {
    const research = { ...f("prose"), finding_id: "missing-simulation", remedy: "simulation" as const };
    expect(requiresNewResearch(research)).toBe(true);
    expect(actionForFinding(research)).toEqual({ type: "escalate" });
    expect(findingFingerprint(research)).toBe("missing simulation");
  });
});

import { describe, expect, it } from "vitest";
import {
  applyTargetedReplacements,
  claimUnits,
  revisionContext,
} from "../src/presentation/stages/p3_gates.js";
import { notationForArtifact } from "../src/presentation/stage_util.js";
import { buildVerificationContract } from "../src/presentation/verification_contract.js";

describe("presentation token-efficiency helpers", () => {
  it("selects only artifact-relevant notation rows", () => {
    const notation = "q_n: schedule\nR_P: regret\nmu: mean";
    const selected = notationForArtifact(notation, "The proof controls q_n.");
    expect(selected).toContain("q_n");
    expect(selected).not.toContain("R_P");
  });

  it("splits claim units and applies exact unique patches", () => {
    expect(claimUnits("First claim. Second claim!")).toHaveLength(2);
    expect(applyTargetedReplacements("alpha beta", [{ before: "beta", after: "gamma" }]).tex).toBe("alpha gamma");
    // A non-unique or missing patch is skipped and reported; the others still apply.
    const partial = applyTargetedReplacements("x x beta", [{ before: "x", after: "y" }, { before: "beta", after: "gamma" }, { before: "zeta", after: "eta" }]);
    expect(partial.tex).toBe("x x gamma");
    expect(partial.skipped).toEqual([{ before: "x", reason: "non-unique" }, { before: "zeta", reason: "missing" }]);
    // Source propagation needs exact accepted patches, not a set of skipped search strings:
    // a rejected edit and a later valid edit may have the same `before`.
    const accepted = { before: "alpha", after: "beta" };
    const guarded = applyTargetedReplacements("alpha", [
      { before: "alpha", after: "protected change" }, accepted,
    ], candidate => !candidate.includes("protected"));
    expect(guarded.tex).toBe("beta");
    expect(guarded.applied).toEqual([accepted]);
    expect(guarded.skipped).toEqual([{ before: "alpha", reason: "protected" }]);
  });

  it("selects relevant paragraphs rather than the whole paper", () => {
    const tex = "Introduction prose.\n\nA rate comparison is overstated.\n\nUnrelated appendix details.";
    expect(revisionContext(tex, ["fix the overstated rate comparison"])).toBe("A rate comparison is overstated.");
  });

  it("deduplicates repeated Lean declarations in the P5 contract", () => {
    const formal = {
      commit: "abc",
      blocks: ["a", "b"].map((obj_id) => ({
        obj_id, alias: null, kind: "theorem", env: "theoremv", title: null,
        body: `statement ${obj_id}`, ref_set: [], lean: { decl: "shared", file: "X.lean" },
        status: "matched", provenance: "from-note",
      })),
    };
    const snippets = {
      commit: "abc",
      snippets: Object.fromEntries(["a", "b"].map((id) => [id, {
        decl: "shared", file: "X.lean", line: 1, statement: "theorem shared : True", sorry_free: true, axioms: null,
      }])),
    };
    const contract = buildVerificationContract(formal, snippets);
    expect(Object.keys(contract.declarations)).toHaveLength(1);
    expect(contract.objects[0].lean?.declaration_refs).toEqual(contract.objects[1].lean?.declaration_refs);
  });
});

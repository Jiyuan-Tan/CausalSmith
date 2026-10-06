import { describe, expect, it } from "vitest";
import { revisionContext, stripLatexCommentLines } from "../src/presentation/stages/p3_gates.js";
import { applyProseRevision, applyTargetedReplacements, proofBlocks, restoreAuditedProofBlocks } from "../src/presentation/prose_revision.js";
import { citedScopeFootnote, texEnvFor, type FormalBlock } from "../src/presentation/formal_layer.js";

describe("P3 audited-proof restoration", () => {
  const audited = [
    "\\begin{proof}\nAudited first proof.\n\\end{proof}",
    "\\begin{proof}[Second]\nAudited second proof.\n\\end{proof}",
  ];

  it("keeps prose revisions while restoring proof edits in order", () => {
    const revised = [
      "Revised introduction.",
      "\\begin{proof}\nModel-edited first proof.\n\\end{proof}",
      "Revised discussion.",
      "\\begin{proof}[Second]\nModel-edited second proof.\n\\end{proof}",
    ].join("\n\n");

    const restored = restoreAuditedProofBlocks(revised, audited);
    expect(restored).not.toBeNull();
    expect(restored).toContain("Revised introduction.");
    expect(restored).toContain("Revised discussion.");
    expect(restored).toContain("Audited first proof.");
    expect(restored).toContain("Audited second proof.");
    expect(restored).not.toContain("Model-edited");
  });

  it("fails closed when a proof block is inserted or deleted", () => {
    expect(restoreAuditedProofBlocks(audited[0], audited)).toBeNull();
  });

  it("makes the post-proof assembly a fixed point while keeping prose editable and proofs protected", () => {
    const block: FormalBlock = {
      obj_id: "lem:cited",
      alias: null,
      kind: "lemma",
      env: "lemmav",
      title: "Cited result",
      body: "Formal statement.",
      ref_set: [],
      lean: null,
      status: "matched",
      provenance: "test",
      cited_dependencies: [{
        node_id: "cite:source",
        cite_id: "cite:source",
        cite_key: "source2026",
        locator: "Lemma 1",
        statement: "Published input.",
        status: "matched",
      }],
    };
    const proof = "\\begin{proof}\nAudited proof text.\n\\end{proof}";
    // Reproduce P2 before its final boundary: the section-local scope note was emitted
    // before the inline proof existed, so proof insertion left the note after the proof.
    const inserted = [
      texEnvFor(block),
      proof,
      citedScopeFootnote(block),
      "Reader prose.",
    ].join("\n");
    const canonical = applyProseRevision({
      before: inserted,
      revised: inserted,
      blocks: [block],
      who: "P2 assembly",
    });
    expect(canonical.indexOf(citedScopeFootnote(block))).toBeLessThan(canonical.indexOf(proof));
    expect(applyProseRevision({
      before: canonical,
      revised: canonical,
      blocks: [block],
      auditedProofs: proofBlocks(canonical),
      who: "P3 fixed-point check",
    })).toBe(canonical);

    const audited = proofBlocks(canonical);
    const safe = applyTargetedReplacements(
      canonical,
      [{ before: "Reader prose.", after: "Clear reader prose." }],
      (candidate, current) => applyProseRevision({
        before: current,
        revised: candidate,
        blocks: [block],
        auditedProofs: audited,
        who: "P3 safe patch",
      }) === candidate,
    );
    expect(safe.applied).toHaveLength(1);
    expect(safe.skipped).toEqual([]);
    expect(safe.tex).toContain("Clear reader prose.");

    const protectedEdit = applyTargetedReplacements(
      safe.tex,
      [{ before: "Audited proof text.", after: "Altered proof text." }],
      (candidate, current) => applyProseRevision({
        before: current,
        revised: candidate,
        blocks: [block],
        auditedProofs: audited,
        who: "P3 protected patch",
      }) === candidate,
    );
    expect(protectedEdit.applied).toEqual([]);
    expect(protectedEdit.skipped).toEqual([
      { before: "Audited proof text.", reason: "protected" },
    ]);
    expect(protectedEdit.tex).toContain("Audited proof text.");
  });
});

describe("P3 model-facing comment stripping", () => {
  it("removes invisible provenance comments without removing escaped percentages", () => {
    const tex = [
      "% DERIVED from formal_layer.json — read-only, do not edit.",
      "Visible prose with 95\\% coverage.",
      "  % another invisible comment",
      "More visible prose.",
    ].join("\n");

    expect(stripLatexCommentLines(tex)).toBe(
      "Visible prose with 95\\% coverage.\nMore visible prose.",
    );
  });
});


describe("P3 editable revision context", () => {
  it("omits protected proof text even when it best matches the rubric finding", () => {
    const tex = String.raw`Editable introduction about notation.

\begin{proof}[Proof of the result]
Protected notation with a spectral radius.

More protected notation.
\end{proof}

Editable conclusion about notation.`;
    const context = revisionContext(tex, ["Repair notation in the spectral radius argument"]);
    expect(context).toContain("Editable introduction");
    expect(context).toContain("Editable conclusion");
    expect(context).not.toContain("Protected");
    expect(context).not.toContain("protected");
    expect(context).not.toContain("\\begin{proof}");
  });
});

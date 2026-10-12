import { describe, expect, it } from "vitest";
import { presentationPrompt } from "../src/presentation/prompt_io.js";

describe("notation-check reviewer is told which symbols Lean already resolves", () => {
  it("renders the Lean-realized symbol list with no unreplaced placeholders", async () => {
    const prompt = await presentationPrompt("p1_notation_check", {
      frozen_layer: "\\begin{definitionv}{P-1}[Setup]body\\end{definitionv}",
      notation_table: "| a | p_k | mass | notation_gaps |",
      lean_realized_symbols: "- p_k\n- \\pi_k",
    });
    expect(prompt.match(/\{\{[a-z_]+\}\}/g)).toBeNull(); // no placeholder survives rendering
    expect(prompt).toContain("- p_k");
    expect(prompt).toContain("- \\pi_k");
  });
});

describe("a Proposition is a main result, not an unproved statement", () => {
  // Every proof path in p2_draft filtered on `theoremv`/`lemmav` and never mentioned
  // `propositionv`, which the anchor parser does recognize. All three propositionv envs in the
  // shipped bundles (prop:two-category-confounding, prop:oracle-regime-reduction,
  // prop:cty-a1-a2-winsorized-expected-outer-upper) therefore reached the reader with no proof
  // rendered, none audited, and none in paper.tex — each despite a verified Lean declaration.
  it("routes propositionv through the main-result proof path", async () => {
    const { isMainProofEnv } = await import("../src/presentation/stages/p2_draft.js");
    expect(isMainProofEnv("theoremv")).toBe(true);
    expect(isMainProofEnv("propositionv")).toBe(true);
    expect(isMainProofEnv("lemmav")).toBe(false);
    expect(isMainProofEnv("definitionv")).toBe(false);
    expect(isMainProofEnv("assumptionv")).toBe(false);
    expect(isMainProofEnv("remarkv")).toBe(false);
  });
});

describe("a rendered proof must reach the paper", () => {
  it("flags a rendered proof that was never placed, and passes one that was", async () => {
    const { lintProofsReachedPaper } = await import("../src/presentation/stages/p2_draft.js");
    const paper = String.raw`
\begin{lemmav}{lem:a}[A]body\end{lemmav}
\begin{proof}[Proof of \cref{obj:lem:a}]argument\end{proof}
\begin{propositionv}{prop:b}[B]body\end{propositionv}
`;
    expect(lintProofsReachedPaper(paper, ["lem:a"])).toEqual([]);
    const dropped = lintProofsReachedPaper(paper, ["lem:a", "prop:b"]);
    expect(dropped).toHaveLength(1);
    expect(dropped[0]).toMatchObject({ gate: "proof-dropped", objId: "prop:b" });
    expect(dropped[0].detail).toContain("never placed in paper.tex");
  });

  it("finds no dropped proofs in the shipped bundles", async () => {
    // Until 2026-08-25 this test asserted the historical failure set (seven dropped proofs
    // shipped live); the isolated-lemma fix wave reassembled those bundles, so the invariant
    // flips: shipped bundles must stay clean. Removing an object from a paper also deletes its
    // proofs/*.tex, so every id under proofs/ is expected to be placed — no filtering.
    const { lintProofsReachedPaper } = await import("../src/presentation/stages/p2_draft.js");
    const { proofObjId } = await import("../src/presentation/proof_files.js");
    const { readFile, readdir } = await import("node:fs/promises");
    const root = new URL("../../doc/presentation/", import.meta.url);
    const found: string[] = [];
    for (const q of ["panel_ppml_forbidden_comparison_v1",
                     "eid_lingam_direction_min_order_v1_truncated_cumulant_minimality",
                     "stat_dose_response_minimax_holder_anisotropic_converse"]) {
      const paper = await readFile(new URL(`${q}/paper.tex`, root), "utf8");
      const ids = (await readdir(new URL(`${q}/proofs/`, root)))
        .map(proofObjId).filter((id): id is string => id !== null);
      found.push(...lintProofsReachedPaper(paper, ids).map((p) => p.objId!));
    }
    expect(found).toEqual([]);
  });
});

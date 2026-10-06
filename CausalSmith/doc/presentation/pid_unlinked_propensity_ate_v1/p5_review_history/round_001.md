# Referee review

**Recommendation:** major_revision
**Overall score:** 7.2/10 — The verified identification, label-design, and inference results are substantial, but publication requires stronger engagement with close work and a clearer account of formal provenance and the projection procedure.

The paper characterizes the maximum sharp ATE interval width under deterministic score labels, derives finite-label rates and a high-resolution constant, and establishes honest-interval rates with known and externally sampled score laws. These are significant contributions under the stated overlap, outcome, and density conditions. The main revisions concern positioning against close results, accuracy of the verification-scope account, and accessibility of the external-log construction.

## Strengths
- The exact ambiguity formula and common released law give a clear criterion for comparing label rules, including with atomic scores and disconnected cells.
- The inverse-budget bounds and high-resolution constant connect release design directly to ATE ambiguity.
- The inference results distinguish known-score minimax length from excess length with an independent score log.

## Findings
- **[major·citation] Related work** — The section names broad literatures but does not engage the closest results on coarse inverse weighting, limited pooling, and link quality. Readers cannot tell how the paper's inverse-label-budget and honest-length results compare in estimand, observation scheme, and assumptions with KalavasisMehrotraZampetakis2024, LeeWeidner2026, or Komarova2015 and Komarova2018.
  - *Fix:* Add a focused comparison of those papers' stated bounds or rates and conditions, then specify the contribution here for a deterministic label linked to each trial row and a known score marginal.
- **[major·prose] Proofs and verification scope** — The sentence “The published fixed-law result of FanShermanShum2014 is used as a cited input for the sharp fixed released law bounds” gives a stale formal trust boundary. The current verified declaration has no external dependency and a checked proof under its stated model conditions.
  - *Fix:* Describe FanShermanShum2014 as the published mathematical antecedent and credit its fixed-law result at the point of use. State separately that the current formal declaration is proved under the displayed conditions, without describing the publication as a maintained formal input.
- **[major·structure] Proofs and verification scope** — The author note says the verification appendix records scope, toolchain, commit, and formal mappings, but that appendix provides only two sentences. A reader cannot identify the checked artifact or distinguish matched statements from presentation-level definitions.
  - *Fix:* Provide the promised commit, Lean toolchain, verification scope, and a compact mapping or accessible manifest for the formal objects; align the author note with what the appendix records.
- **[minor·prose] Inference with an independent score log** — The candidate sieve enforces equal outcome and score mass within each arm-label cell, but the text calls its arrays “compatible” without explaining that candidates need not themselves arise from a common score law and release rule. This obscures why the projection is a valid, potentially conservative outer construction.
  - *Fix:* State the exact constraints imposed on sieve candidates and explain that the closed projection contains the population sharp interval on the coverage event.
- **[minor·citation] Related work** — Many substantive source claims use bare citations, including the descriptions of conditional transport, statistical matching, and subclassification, despite the paper's pinpoint-citation convention.
  - *Fix:* Check the cited works and add accurate section, theorem, or page locators to claims about their specific results and assumptions.
- **[minor·structure] Trial setup and the sharp identified interval** — The endpoint formulas use generalized quantiles before their definition appears, and the target θ(P) is used well before its formal definition in the inference section.
  - *Fix:* Move the generalized-quantile and ATE-functional definitions ahead of their first substantive use.
- **[minor·structure] Designing a finite-label release** — The high-resolution theorem indexes its constructed labels by 0,…,K−1, while the defined release class uses 1,…,K. The proof compares its ambiguity directly with the optimum over the latter class without stating the relabeling.
  - *Fix:* Explicitly identify the two alphabets by the bijection r ↦ r+1 when comparing the constructed rule with the K-label optimum.
- **[minor·prose] Introduction** — The overlap symbol ε first appears in the companding integral before prose identifies it as the overlap margin.
  - *Fix:* At that first use, add a brief gloss such as “the overlap margin ε,” or describe the allocation in words there.
- **[minor·prose] Designing a finite-label release** — The lower-density class is empty when its proposed floor exceeds the reciprocal length of the score interval. The discussion states the feasible range, but the class definition and first rate interpretation leave it implicit.
  - *Fix:* State the feasible range 0 < m_f ≤ (1−2ε)⁻¹ when first interpreting the uniform lower bound.

## Questions for authors
- Can the verification appendix identify the exact checked commit and toolchain and clarify the published fixed-law result's role relative to the current formal proof?
- Is the external-log projection intended as a theoretical measurable procedure, or can a finite approximation with a stated coverage and length guarantee be supplied?

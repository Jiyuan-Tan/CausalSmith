# Referee review

**Recommendation:** major_revision
**Overall score:** 7.2/10 — The verified minimax characterization is substantial, but statement clarity, positioning against close work, and the organization of the main argument need significant revision.

The paper establishes a matched finite-sample rate for the budget-value curve under fixed overlap and a known discrete alphabet, with a capacity-active lower bound at half budget. The result is a meaningful contribution. The manuscript needs a clearer route through the estimator and proof, sharper comparisons with close value-process work, and repairs to two definitions or statements that obscure the verified scope.

## Strengths
- The matched rate covers every symmetric closed budget interval, including the full curve and the single half-budget value.
- The lower-bound family keeps treatment effects positive, capacity binding, and full-capacity value fixed.
- The dual representation gives a clear reason why one estimated process controls all budgets.

## Findings
- **[major·statement] Setup and assumptions** — The cell-mean definition says “define the cell potential-outcome mean by” a conditional expectation for any cell, although null cells are allowed and the manuscript elsewhere assigns their means zero. The displayed definition leaves that convention unclear at exactly the laws covered by the main result.
  - *Fix:* Define the conditional mean for occupied cells and state the zero convention for null cells inside the cell-mean definition; use it consistently in later definitions.
- **[major·statement] Minimax risk for the budget-value curve** — In the fixed-alphabet proposition, “there are constants c,C” is followed by “If some c>0 satisfies τ_j=c.” Reusing c makes the common effect appear tied to the risk lower-bound constant, whereas the verified identity applies to any positive common effect.
  - *Fix:* Use a distinct symbol, such as γ, for the common effect in the proposition and its displayed identity.
- **[major·citation] Related work** — The discussion names the closest value-process and unrestricted-value studies but gives little direct comparison of their estimands, conditions, and statistical guarantees. Readers cannot readily assess the precise advance supplied by the finite-sample curve rate.
  - *Fix:* Compare the Feng–Hong–Nekipelov value-process result, the optimized-value inference results, Qini-value inference, and the unrestricted discrete scalar rate using their stated conditions and loss criteria. Cite specific results where making quantitative claims.
- **[major·structure] Minimax risk for the budget-value curve** — The full estimator specification and extensive auxiliary material interrupt the path from the dual identity to the matched rate and its lower-bound mechanism. The central statistical argument is difficult to follow on a first reading.
  - *Fix:* Give a concise main-text account of the estimator branches, process bound, and paired reduction, with the complete polynomial construction and technical lemmas in an appendix. Put a short proof roadmap beside the matched theorem.
- **[minor·structure] Proofs and verification scope** — The paired-family definition uses “the simplex” before the simplex is defined, and the sentence after the family calls it “the following causal family.”
  - *Fix:* Move the simplex definition before the paired-family definition and revise the connecting sentence.
- **[minor·citation] Related work** — The sentence naming Bhattacharya and Dupas, Luedtke and van der Laan, and Hirano and Porter gives no citations for the specific studies or results it describes.
  - *Fix:* Add the appropriate citations and locators, and check that each cited study supports the stated characterization.
- **[minor·prose] Minimax risk for the budget-value curve** — “An implementation can approximate that average by Monte Carlo draws, with computational cost and Monte Carlo error determined by the number of draws” suggests an operational route without specifying a draw count or error guarantee for the reported rate.
  - *Fix:* Describe the theorem's estimator as the exact conditional average. Place Monte Carlo evaluation in the limitations discussion as a computational direction unless a quantitative approximation guarantee is supplied.

## Questions for authors
- Which specific Hirano–Porter result is intended in the related-work paragraph?
- Can the main text give a compact comparison of the present curve risk with the cited unrestricted scalar rate under matched model conditions?

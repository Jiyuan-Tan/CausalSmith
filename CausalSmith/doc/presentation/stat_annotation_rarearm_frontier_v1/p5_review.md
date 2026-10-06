# Referee review

**Recommendation:** major_revision
**Overall score:** 7.2/10 — The verified overlap-uniform frontier offers a credible theoretical contribution, but the manuscript needs substantial reorganization and several concrete presentation corrections to communicate it effectively.

The paper establishes a numerical-constant minimax squared-error frontier for passive independent complete and auxiliary records with binary treatment and outcomes, finite covariates, and possibly diminishing treatment overlap. It also delivers original-record attainment, exact resource characterizations, and fixed-parameter convergence to the exact-marginal benchmark. The principal claims faithfully reflect the verified statements and fairly credit the fixed-overlap predecessors; publication readiness chiefly depends on improving the exposition and correcting an illustrative-sequence error.

## Strengths
- The comparison constants are uniform across both sample sizes, alphabet size, and overlap floor, making diminishing overlap an explicit part of the contribution.
- The manuscript carefully distinguishes benchmark-order attainment, exact fixed-parameter risk convergence, and a vanishing relative risk.
- The related-work section engages the closest supervised and two-channel results through their actual rates and conditions.
- The causal interpretation retains consistency and conditional exchangeability, and the baseline comparison correctly compares upper guarantees.
- The labelled limitations subsection candidly explains the proof-oriented tuning and the scope of the passive sampling experiment.

## Findings
- **[major·structure] Minimax precision with two information budgets; An attaining estimator; appendices** — The presentation hierarchy obscures the central contribution. A lengthy six-step estimator construction precedes the main risk theorem, the following estimator section repeatedly describes that same construction, and extensive presentations of standard tools occupy substantial space before the distinctive lower-bound argument. Repeated definitions, condition lists, and post-result paraphrases make the paper considerably harder to navigate.
  - *Fix:* Present the rate and main comparison early, accompanied by a concise explanation of the two information scales. Place the complete estimator construction in the estimator section and consolidate its repeated explanations. Condense the presentations of standard tools using the existing precise citations, retaining detailed derivations in a supplementary appendix. Preserve the exact hypotheses and anchored object identifiers throughout the reorganization.
- **[minor·prose] Consistency and the value of auxiliary records — Three illustrative sequences** — The sentence “Let \(t=k+2\), so every displayed public index is legal” is false for the stated zero-based sequence domain. At the first two coordinates, \(\epsilon_k=t^{-1}\) equals \(1/2\) and \(1/3\), exceeding the public upper bound \(1/4\).
  - *Fix:* Use \(t=k+4\) in all three examples. This makes every coordinate admissible and preserves the displayed asymptotic orders.
- **[minor·prose] abstract; Introduction; An attaining estimator** — The abstract and introduction emphasize explicit attainment, while the construction's zero-output threshold \(n\epsilon<\exp(4096)\) receives its practical interpretation much later. Attainment is faithful to the verified theorem, but readers need an earlier distinction between this uniform order guarantee and the numerical performance of the displayed tuning.
  - *Fix:* Describe the construction early as attaining the uniform minimax order with proof-oriented tuning and numerical constants. In the estimator section, explain the threshold's mathematical role immediately after presenting it. Keep the discussion of moderate-budget implementation and calibration in the labelled limitations subsection.
- **[minor·prose] Minimax precision with two information budgets — closing paragraph** — “The next section gives the estimator that attains the uniform upper comparison” points to a section that explains an estimator already fully specified earlier. The directional section reference also bypasses the required cleveref convention.
  - *Fix:* Give the estimator section a structural label and write, for example, “\Cref{sec:attaining-estimator} explains the construction in \cref{obj:def:estimator-handle} and compares its guarantee with an inverse-count baseline.” Convert comparable directional structural references to cleveref references with exact labels.
- **[nit·prose] Minimax precision with two information budgets — opening paragraph** — The symbol \(r(n,m,d,\epsilon)\) appears in running prose before its defining environment without an attached first-use gloss.
  - *Fix:* At its first occurrence, call \(r(n,m,d,\epsilon)\) “the numerical risk rate,” or introduce the rate definition before the opening comparison.


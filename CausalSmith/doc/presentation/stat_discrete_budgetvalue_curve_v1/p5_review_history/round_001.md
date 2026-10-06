# Referee review

**Recommendation:** major_revision
**Overall score:** 7.2/10 — The verified matched minimax result is substantial, but the main argument is difficult to extract from the presentation and several interpretive claims need tighter scope.

The paper establishes a finite-sample minimax rate for estimating the population budget-value curve on a known discrete alphabet under fixed overlap. Its dual representation, uniform estimator bound, and capacity-active lower-bound family make a strong theoretical contribution. The result merits serious consideration after a substantial presentation revision that foregrounds the statistical insight and sharpens a few claims.

## Strengths
- The matched rate covers every sample size, alphabet size, and symmetric budget interval, including the full curve and the single half-budget value.
- The half-budget lower bound remains active with positive treatment effects and a fixed full-budget value.
- The dual contraction gives a clear reason one threshold-process estimate controls the entire curve.

## Findings
- **[major·structure] Setup and assumptions; Minimax risk for the budget-value curve** — The central theorem arrives after a long sequence of technical definitions, while the full Jackson–factorial construction dominates the main results section. This obscures the estimand, the dual insight, and the substantive meaning of the lower-bound family.
  - *Fix:* Present the model, loss, dual identity, and matched theorem in a compact main-text sequence. Give a short estimator overview there and place its full tuning and count construction with the technical process definitions in the appendix.
- **[minor·prose] Setup and assumptions** — “The risk constants have polynomial dependence on \(1/\epsilon\)” is more specific than the verified results, which state that the constants depend only on \(\epsilon\).
  - *Fix:* State that the constants depend only on fixed overlap, or provide an explicit uniform polynomial bound if this sharper dependence is intended as a result.
- **[minor·prose] Introduction** — “Estimating the half-budget value amounts to estimating that process at one fixed shadow price, an \(L_1\)-distance problem” can suggest equivalence of statistical experiments. The stated reduction maps two-sample observations into causal observations in the direction needed for the lower bound.
  - *Fix:* State the affine target identity and describe the exact sample map as a lower-bound reduction from two-sample \(L_1\) estimation.
- **[minor·prose] Related work** — The closest value-process comparison is described chiefly by method and broad regularity. Readers need a more precise account of how its asymptotic setting relates to the present finite-sample rate, especially for fixed alphabets and treatment-effect ties.
  - *Fix:* Add a concise comparison of estimand, loss, sampling regime, regularity conditions, and delivered conclusion for the closest constrained-value and unrestricted scalar results.
- **[nit·statement] Minimax risk for the budget-value curve** — The estimator lists \(\kappa=1/512\) as a tuning quantity but subsequently writes \(L/512\) directly and never uses \(\kappa\).
  - *Fix:* Use \(\kappa L\) in the degree definition or remove the redundant symbol.

## Questions for authors
- Can the main text give a compact example showing how unequal positive cell effects shape the budget curve and why the half-budget value remains difficult when the full-budget value is fixed?

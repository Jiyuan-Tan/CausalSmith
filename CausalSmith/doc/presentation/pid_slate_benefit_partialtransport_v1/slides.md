# Sharp Ordinal Benefit Bounds

Under IV independence, monotonicity, weak selection monotonicity, overlap, and positive survivor-complier mass, we characterize the sharp interval for the probability that treatment strictly improves an ordered outcome among survivor compliers.

---

## Overview

- We study ordered outcomes observed only for selected units.
- The running example is a training offer, treatment receipt, employment, and wage category.
- The target is \(\theta\), the survivor-complier benefit probability: among compliers employed under either treatment state, how often does treatment raise the wage category?
- Observed IV contrasts identify two selected-complier outcome capacities.
- Exact-mass partial transport turns those capacities into sharp lower and upper bounds.
- Plug-in estimation and a deterministic guard give finite-sample containment of the whole sharp interval.

---

## Motivation

- In Job Corps-style settings, an offer changes who receives training.
- Training can also change who is employed, so wage categories are observed after selection.
- For policy, a mean wage effect among observed workers answers a different question from: who is made strictly better off among workers observed under both treatment states?
- The survivor-complier target combines the IV complier group with the always-selected group.
- Ordered outcomes make the target a same-unit comparison, not a difference in marginal distributions.

@figure iv-selection-pipeline: A box-and-arrow schematic showing instrument offer, treatment receipt, selection into observed wages, ordered wage category, and the survivor-complier target group.

---

## Setup

- \(Z\) is the binary instrument, \(D\) is treatment receipt, \(S\) is selection, and \(Y\) is an ordered outcome.
- \(D_0,D_1\) are potential treatments under the two instrument states.
- \(S_0,S_1\) are potential selection indicators under the two treatment states.
- \(Y_0,Y_1\) are potential ordered outcomes under the two treatment states.
- \(C\) is the complier event: treatment receipt is shifted from 0 to 1 by the instrument.
- Survivor compliers satisfy \(C\) and \(S_0=S_1=1\).

---

## Assumptions

- Conditional on \(X\), the instrument is independent of potential treatments, selections, and outcomes.
- Observed treatment, selection, and selected outcomes equal the corresponding realized potential variables.
- Instrument propensity overlap keeps both \(Z=0\) and \(Z=1\) available in each supported covariate cell.
- Treatment monotonicity orients the first stage toward compliers.
- Weak selection monotonicity lets treatment move complier selection in one direction within each covariate cell.
- In the training example, one cell may have training weakly increasing employment among compliers, while another may have training weakly decreasing it.

@formal ass:iv-independence

@formal ass:weak-selection-monotonicity

---

## Observable capacities

- \(\ell_i(x)\) is the lower-arm selected-complier capacity at outcome level \(i\) in covariate cell \(x\).
- \(h_j(x)\) is the upper-arm selected-complier capacity at outcome level \(j\) in covariate cell \(x\).
- Their totals are \(q_0(x)\) and \(q_1(x)\).
- The exact survivor-complier mass is \(m(x)=\min\{q_0(x),q_1(x)\).
- The selection direction identifies which selected-complier capacity total contains extra one-sided selected mass.

@informal prop:capacity-identification: Under the IV, consistency, overlap, no-defier, and weak selection monotonicity conditions, the observable contrasts recover the selected-complier capacities and the survivor-complier mass in each supported covariate cell.

---

## Key idea

- The observed law gives two selected-complier submargins, one for \(Y_0\) and one for \(Y_1\).
- Selection can make their totals unequal.
- The survivor-complier comparison pairs exactly \(m(x)\) units in each cell.
- That pairing is an exact-mass partial-transport problem.
- Benefit mass is the amount paired with treatment-one outcome strictly above treatment-zero outcome.

@figure capacity-transport: A box-and-arrow schematic showing lower-arm capacity, upper-arm capacity, exact survivor-complier mass, partial-transport coupling, and strict-benefit mass.

---

## Main result

@informal thm:sharp-exact-mass-threshold-interval: Under the structural restrictions and positive aggregate survivor-complier mass, the sharp identified interval is exactly the aggregate of the cellwise threshold-cut lower and upper benefit masses.

@formal thm:sharp-exact-mass-threshold-interval

---

## Threshold formulas

- The lower endpoint forces as much mass as possible onto nonbenefit pairs.
- The upper endpoint packs as much mass as possible onto strict-benefit pairs.
- Ordered support lets both calculations collapse to prefix and tail threshold cuts.
- The formulas apply uniformly across positive-gap, negative-gap, zero-gap, and zero-survivor cells.

@formal def:threshold-cuts

---

## Endpoint attainment

- Sharpness requires full latent laws, not just cellwise couplings.
- The construction first builds endpoint-attaining couplings in each cell.
- It assigns unmatched selected-complier capacity to the one-sided selected stratum allowed by the selection direction.
- It then completes the law with never-taker and always-taker components that preserve the observed IV distribution.

@informal thm:full-law-endpoint-attainment: For the same observed law and structural restrictions, there are full latent laws that attain the lower and upper endpoint probabilities.

---

## Known benchmark

- When all compliers are selected under both treatment states, the capacity totals match.
- The exact-mass transport problem becomes the complete-marginal ordinal benefit problem.
- This recovers the Lu et al. (2018) style threshold formulas on the no-selection face.
- The zero-gap result explains the algebraic transition from unequal selected capacities to complete marginal coupling.

@informal prop:tie-face-collapse: In every supported zero-gap cell, the row-exact, column-exact, and doubly exact comparison polytopes coincide with the exact-mass coupling polytope.

@informal thm:no-selection-reduction: In the no-selection submodel, the cellwise normalized threshold cuts reduce to the complete-marginal ordinal benefit formulas.

---

## Related literature

- Imbens and Angrist (1994) and Angrist et al. (1996) supply the complier IV framework.
- Frangakis and Rubin (2002), Kennedy et al. (2019), and Chen and Flores (2015) motivate survivor-complier targets under selection.
- Lee (2009), Semenova (2025), and Dong and Heiler (2026) develop monotone selection bounds and covariate-specific selection directions.
- Lu et al. (2018), Gabriel et al. (2024), and de Aguas et al. (2025) study ordinal benefit bounds under different observable restrictions.
- Our contribution combines IV noncompliance, treatment-induced selection, and same-unit ordinal benefit through exact-mass partial transport.

---

## Example

- The synthetic witness has one covariate cell and three ordered outcome levels.
- Everyone is a complier, and treatment weakly increases selection.
- The lower-arm selected-complier capacity total is \(1/4\).
- The upper-arm selected-complier capacity total is \(1/2\).
- The exact survivor-complier mass is \(1/4\), and the upper threshold cut is \(7/40\).

@informal prop:three-level-witness: In the three-level witness, the sharp identified interval for the survivor-complier strict-benefit probability is \([0,7/10]\), and both endpoints are attained by compatible latent laws.

---

## Computation

- The algorithm works cell by cell.
- It computes totals, exact mass, prefix sums, tail sums, and threshold cuts.
- It builds sparse lower and upper allocation traces using nested benefit and nonbenefit graphs.
- Full coupling matrices are materialized only when needed.

@informal thm:linear-sparse-threshold-flow: For finite covariate support and \(K\) ordered levels, sparse endpoint construction takes at most \(C_{\mathrm{sparse}}\,|\mathcal X|\,K\) operations, while dense matrix materialization takes at most \(C_{\mathrm{dense}}\,|\mathcal X|\,K^2\) operations.

---

## Estimation

- The plug-in estimator replaces observed probabilities by empirical probabilities.
- It projects empirical capacities onto the nonnegative cone.
- It evaluates the same threshold-cut formulas cell by cell.
- It screens cells using \(\eta_n\), the screening threshold, so the endpoint quotient is evaluated on empirically retained survivor mass.

@formal def:plugin-endpoint-estimator

---

## Asymptotics

@informal thm:branch-free-pointwise-directional-limit: For a fixed finite-support law, if \(\eta_n\to0\) and \(\sqrt n\,\eta_n\to\infty\), the screened plug-in endpoints are consistent and have a Hadamard directional Gaussian limit.

@formal thm:branch-free-pointwise-directional-limit

---

## Guarded inference

- The guarded interval pads the plug-in lower and upper endpoints by a deterministic radius.
- The radius uses the instrument-overlap bound, a positive lower bound on aggregate survivor-complier mass, the support dimensions, and the screening threshold.
- The guarantee covers the entire sharp identified interval, not just one endpoint.
- The constants are large, so at realistic sample sizes the padded interval is the whole unit interval: this is an existence result for uniform finite-sample validity, not a procedure we recommend reporting on its own.

@informal thm:uniform-deterministic-guard: Uniformly over the finite-slate law class with fixed overlap and positive aggregate survivor-complier mass lower bound, the guarded confidence interval contains the full sharp identified interval with probability at least \(1-\alpha\) for every sample size.

---

## Conclusion

- We identify selected-complier outcome capacities from IV contrasts under weak selection monotonicity.
- We characterize the survivor-complier strict-benefit target by exact-mass partial transport.
- We give closed threshold-cut formulas for the sharp interval and endpoint-attaining latent laws.
- We compute sparse endpoint witnesses in linear time in \(|\mathcal X|K\).
- We provide plug-in endpoint estimation, a fixed-law directional limit, and a deterministic finite-sample guard for whole-interval containment.

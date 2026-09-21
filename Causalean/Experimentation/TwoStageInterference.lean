/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Experimentation.TwoStageInterference.Asymptotic.Asymptotic
public import Causalean.Experimentation.TwoStageInterference.Basic
public import Causalean.Experimentation.TwoStageInterference.BetweenGroup
public import Causalean.Experimentation.TwoStageInterference.BetweenGroupEffect
public import Causalean.Experimentation.TwoStageInterference.CompleteRandomization
public import Causalean.Experimentation.TwoStageInterference.DesignBasedDifferenceInMeans
public import Causalean.Experimentation.TwoStageInterference.Effects
public import Causalean.Experimentation.TwoStageInterference.StageOne
public import Causalean.Experimentation.TwoStageInterference.Stratified
public import Causalean.Experimentation.TwoStageInterference.Unbiased
public import Causalean.Experimentation.TwoStageInterference.Variance
public import Causalean.Experimentation.TwoStageInterference.VarianceConservative
public import Causalean.Experimentation.TwoStageInterference.VarianceMoments

/-!
# Hudgens & Halloran (2008) — causal inference with interference, two-stage designs

Formalization of Hudgens & Halloran (2008), "Toward Causal Inference With Interference"
(JASA), building on the paper-agnostic design-based substrate `Experimentation.DesignBased`.

* `Basic` — the two-stage mixed-strategy design, the average-potential-outcome estimands, the
  four causal-effect contrasts (direct, indirect, total, overall), and the within-group /
  population / effect estimators.
* `Unbiased` — within-group unbiasedness (Theorem 1), population unbiasedness (Theorem 2), and
  the total = direct + indirect decomposition.
* `Effects` — strategy-agnostic population unbiasedness and the Theorem 2 unbiasedness corollaries
  for the direct, indirect, and total effect estimators.
* `Stratified` — the stratified-interference specialization.
* `CompleteRandomization` — the Boolean-vector complete-randomization design and its inclusion,
  pair-inclusion, and fixed-count-on-support facts.
* `DesignBasedDifferenceInMeans` — design-based unbiasedness and variance identities for the
  generic difference-in-means estimator used by this application.
* `Variance` — the within-group difference-in-means estimator has the classical Neyman
  completely-randomized variance `S₁/K + S₀/(n−K) − Sτ/n`, an ingredient in the
  paper's variance-estimator analysis rather than the statement of its Theorem 5.
* `VarianceMoments` — the generic expected-sample-variance moment lemma `E_Shat`: under a
  completely randomized design the realized sample variance of a selected subgroup's outcomes has
  expectation the population sample variance.
* `VarianceConservative` — the conservative variance estimator `Ŝ₁/K + Ŝ₀/(n−K)`, its pointwise
  nonnegativity, and its conservativeness `Var(τ̂) ≤ E[v̂ar]`; the estimator is Equation (8),
  while the inequality follows from Theorem 5 (Equation (9) is an equality condition).
* `StageOne` — the between-group SRS ingredient: the variance of the mean of a simple random
  sample of `m` of `N` fixed group-level quantities is `(1 − m/N)/m` times their population sample
  variance — the finite-population correction (`Var_srs_mean`).
* `BetweenGroup` — the Appendix A.2 two-stage variance decomposition of the population estimator
  `Ŷ(z;ψ)` (`Var_popEst`).  Via the design-based law of total variance, the variance splits into a
  between-group SRS term `(1 − C/N)/C · Sμ²(ȳ·(z;ψ))` (finite-population correction) plus a
  within-group term `(1/(C·N)) · ∑ᵢ Var_{ψ i}(Ŷ_i(z))`.  The core is the design-agnostic
  `Var_groupAgg`, the same decomposition for an arbitrary per-group within-group statistic `g i`.
* `BetweenGroupEffect` — the analogous two-stage variance of the direct-effect estimator
  `ĈE^D(ψ) = Ŷ(0;ψ) − Ŷ(1;ψ)` (`Var_estDirect`), obtained from `Var_groupAgg` with the per-group
  direct-effect statistic `dᵢ = Ŷ_i(0) − Ŷ_i(1)`: a between-group SRS term over the group-level
  direct effects `ȳ_i(0;ψ) − ȳ_i(1;ψ)` plus a within-group term averaging the per-group
  direct-effect-estimator variances `Var(dᵢ ∣ Sᵢ=ψ)`.
* `Asymptotic/` — Liu–Hudgens (2014) large-sample layer: the sequence-of-experiments bundle
  `LHExperiment` (carrying the two-stage design + known propensities, with the `E_estD` /
  `var_estD` bridges), support-aware consistency of the direct-effect estimator as the number of
  groups grows (`estDirect_consistent_of_bounded_outcomes`), the conditional-to-unconditional CDF
  transfer `directEffect_cdf_tendsto_of_uniform_conditional`, homogeneous and identical-group CLT
  special cases, and oracle/feasible Wald coverage. These results retain the Hudgens–Halloran
  control-minus-treatment sign, the negative of Liu–Hudgens' treatment-minus-control estimand.
-/

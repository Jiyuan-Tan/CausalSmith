/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Experimentation.DesignBased.CompoundVariance
public import Causalean.Experimentation.DesignBased.Concentration
public import Causalean.Experimentation.DesignBased.DependencyCLT
public import Causalean.Experimentation.DesignBased.Designs
public import Causalean.Experimentation.DesignBased.EdgeVarianceBound
public import Causalean.Experimentation.DesignBased.Estimators
public import Causalean.Experimentation.DesignBased.Exposure
public import Causalean.Experimentation.DesignBased.FinitePopulationCLT
public import Causalean.Experimentation.DesignBased.FinitePopulationCLT.DifferenceInMeans
public import Causalean.Experimentation.DesignBased.FinitePopulationCLT.NeymanCoverage
public import Causalean.Experimentation.DesignBased.FinitePopulationCLT.PermutationTransport
public import Causalean.Experimentation.DesignBased.FinitePopulationCLT.PredictableVariance
public import Causalean.Experimentation.DesignBased.FinitePopulationCLT.PredictableVarianceConcentration
public import Causalean.Experimentation.DesignBased.FinitePopulationCLT.PredictableVarianceMoments
public import Causalean.Experimentation.DesignBased.FinitePopulationCLT.PredictableVarianceWeights
public import Causalean.Experimentation.DesignBased.FinitePopulationCLT.SRS
public import Causalean.Experimentation.DesignBased.FinitePopulationVariance
public import Causalean.Experimentation.DesignBased.GaussianCDF
public import Causalean.Experimentation.DesignBased.HT.Estimator
public import Causalean.Experimentation.DesignBased.HT.Unbiased
public import Causalean.Experimentation.DesignBased.HT.Variance
public import Causalean.Experimentation.DesignBased.HeydeBrownBridge
public import Causalean.Experimentation.DesignBased.InProb
public import Causalean.Experimentation.DesignBased.IndepSummandsCLT
public import Causalean.Experimentation.DesignBased.LocalDependenceVariance
public import Causalean.Experimentation.DesignBased.NeymanComposition
public import Causalean.Experimentation.DesignBased.Optimality
public import Causalean.Experimentation.DesignBased.Optimality.Minimax
public import Causalean.Experimentation.DesignBased.Optimality.Neyman
public import Causalean.Experimentation.DesignBased.PotentialOutcome
public import Causalean.Experimentation.DesignBased.ProductBlock
public import Causalean.Experimentation.DesignBased.ProductReindex
public import Causalean.Experimentation.DesignBased.ProductVariance
public import Causalean.Experimentation.DesignBased.RatioLinearization
public import Causalean.Experimentation.DesignBased.Risk
public import Causalean.Experimentation.DesignBased.SequentialSampling
public import Causalean.Experimentation.DesignBased.Slutsky
public import Causalean.Experimentation.DesignBased.TwoStage
public import Causalean.Experimentation.DesignBased.Variance
public import Causalean.Experimentation.DesignBased.WaldCoverage
public import Causalean.Experimentation.DesignBased.WaldPipeline


/-!
# Design-based (randomization) inference substrate

The shared, paper-agnostic substrate for design-based / randomization inference under
interference: the finite-population, fixed-potential-outcome flavor of the potential-outcomes
framework, where probability comes from the experimenter's randomization over a finite assignment
space `Ω`.  Reused by every experimentation paper under `Causalean/Experimentation/`.

* `Exposure` — exposure mappings and the generalized probability of exposure.
* `PotentialOutcome` — properly-specified mapping (Cond 1) and consistency (Cond 2); `Yobs`.
* `HT.{Estimator,Unbiased,Variance}` — Horvitz–Thompson total/mean/effect estimators with
  unbiasedness and randomization variance.
* `RatioLinearization` — finite-sample delta-method identities: exact design-mean of normalized
  (Horvitz–Thompson / Hájek) ratios and their products (the ratio linearization kernel).
* `WaldCoverage` — paper-agnostic conservative Wald-interval liminf coverage from a studentized
  CLT plus a dominating deterministic variance estimator.
* `WaldPipeline` — the full pipeline (`dependency_wald_coverage`): chains `DependencyCLT` into
  `WaldCoverage`, so dependency-graph primitives plus a conservative variance give Wald coverage in
  one theorem.
* `EdgeVarianceBound` — abstract `var_edge_sum_le`: variance of an edge-sum over a bounded-degree
  dependency graph (`≤ 8M²m³N`).
* `GaussianCDF` — standard-normal CDF facts (agreement with Mathlib `cdf`, symmetry, continuity).
* `Concentration` — Bernstein/sub-exponential tail bounds for a bounded design statistic
  (`exp(−ε²/·)`, sharper than Chebyshev).
* `DependencyCLT` — the general design-based CLT (`dependency_studentized_cdf`): a bounded-degree
  dependency-graph sum's studentized statistic is asymptotically standard normal under the design,
  by transporting the Stein CLT engine across the measure bridge.  Composes with `WaldCoverage`.
* `CompoundVariance` — law of total variance for the two-stage `compound` design
  (`E_compound_tower`, `Var_compound_eq_tower`): total variance = expected within-stage variance +
  variance of the conditional mean; underlies between-group / within-group decompositions.
* `ProductVariance` — cross-coordinate independence of the `prodDesign`: distinct-coordinate
  functions are uncorrelated (`Cov_prod_apply_of_ne`), so the variance of a linear combination of
  single-coordinate functions is the sum of the coordinate variances (`Var_prod_linear_comb`).
* `ProductReindex` — relabeling a product design over a common coordinate space by a coordinate
  permutation `σ` (`prodDesign_Pr_reindex`): a permuted predicate's probability under
  `prodDesign D` equals the predicate's probability under the permuted product
  `prodDesign (D ∘ σ)`; pure finite-sum reindexing, the kernel for selection-symmetry arguments.
* `IndepSummandsCLT` — the independent-summands CLT (`prodDesign_clt`): a normalized sum of
  independent, uniformly bounded, mean-zero per-coordinate summands over a product design converges
  to the standard normal, via the trivial diagonal dependency graph fed into
  `stein_cdf_clt_of_depGraph`.
* `Risk` — bias, mean squared error, and the bias–variance decomposition `mse = Var + bias²` for a
  design-based estimator of a fixed target; the `mse`-as-functional-of-the-design that the
  optimality layer minimizes.
* `Optimality` — the design as a chosen parameter: `DesignFamily`, design domination, optimal
  designs (`IsOptimalOn`) with existence over a finite family, and the mean-squared-error risk
  `mseRisk` of a design-indexed estimator.
* `Designs` — the design zoo: canonical Bernoulli, complete-randomization, and stratified designs
  with their first/second-order inclusion probabilities.
* `Optimality.Minimax` — worst-case risk over a family of states, minimax designs, and regret.
* `Optimality.Neyman` — Neyman optimal allocation: the treatment fraction minimizing the two-arm
  variance `A/x + B/(1−x)` is `√A/(√A+√B)`.
* `Estimators` — design-based estimators: the difference-in-means estimator and its unbiasedness.
* `Variance` — conservative variance estimators (`E[V̂] ≥ Var`) and the conservative
  Chebyshev bound.
-/

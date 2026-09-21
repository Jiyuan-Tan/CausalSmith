# Substrate requirement: independent-unequal-prefix-rao-blackwell

## Goal
Build axiom-clean reusable Causalean finite decision-theory substrate for two independent fixed iid pools with possibly different finite alphabets and capacities.

## Provides (API contract)
- Define the capped-prefix implementation of a bounded measurable statistic of two independently retained variable-length prefixes (or their histograms).
- Define its conditional Rao–Blackwell average as a deterministic statistic of the two fixed pools.
- Prove measurability and the exact product law of the two untruncated Poisson prefixes.
- Prove that capped and untruncated statistics agree off the union of prefix-overflow events.
- Prove squared-risk contraction under conditional averaging.
- Prove a risk bound by the untruncated Poissonized risk plus a bounded-loss penalty times the two Poisson upper tails.
- Expose a specialization for independently retained prefixes of different sizes and alphabets, directly instantiable for one complete-record pool and one treatment-covariate pool, without coordinatewise pairing or an equal-length assumption.

## Statement / milestones
Given probability laws `P` on `X` and `Q` on `Y`, independent fixed iid pools of sizes `NX` and `NY`, independent Poisson prefix lengths with intensities `lambdaX` and `lambdaY`, and a bounded measurable statistic of the two retained prefixes, identify the joint untruncated prefix law exactly. Construct the capped statistic and its conditional average on the fixed pools, prove the Rao–Blackwell squared-risk contraction, and bound fixed-pool risk by the corresponding untruncated Poissonized risk plus explicit bounded-loss penalties for the two overflow events.

## Standard reference
Conditional Jensen/Rao–Blackwell contraction, independent product measures, Poissonization/depoissonization, and union bounds for independent prefix overflow.

## Intended reuse
`T_InverseCountBaseline.lean` in `stat_semisupervised_discrete_ate_annotation_frontier/v1` will instantiate the result with the disjoint complete-record block of capacity `M0` and pooled `XA` block of capacity `nf+mf`, then combine `poisson_inverse_count_risk` with explicit Poisson overflow bounds. The construction should remain reusable for arbitrary different finite alphabets and capacities.

## May assume / must derive
May assume probability laws, measurability and bounded range of the supplied statistic, independence/product sampling of the two fixed pools, and standard Poisson tail inputs where an explicit tail estimate is supplied by the consumer. Must derive the two-prefix product-law identity, capped/untruncated agreement off overflow, conditional squared-risk contraction, and the combined risk-transfer inequality. All public declarations must contain zero `sorry`, use no `admit`, and introduce no axioms.

## Non-goals (optional)
Do not import `CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research` or any paper-specific module. Do not assume equal pool sizes, equal alphabets, coordinatewise pairing, or a shared prefix length. Do not prove the paper-specific inverse-count risk or Poisson tail constants.

## Known building blocks (optional)
`Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Depoissonization`, `Causalean.Stat.FiniteRaoBlackwell.Basic`, `Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.Risk`, and `Mathlib.MeasureTheory.Integral.ConditionalExpectation.Basic`.

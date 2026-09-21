# Substrate requirement: finite-family-independent-poisson-prefix-rao-blackwell

## Goal
Extend the axiom-clean finite Rao--Blackwell substrate from two independent
unequal Poisson prefixes to a finite heterogeneous family, including a direct
three-pool specialization.

## Provides (API contract)
- A paper-independent finite-family experiment indexed by a finite type `I`,
  with per-pool finite alphabets, iid laws, capacities, and independent Poisson
  prefix lengths of heterogeneous intensities.
- The untruncated joint-prefix statistic, capped-prefix implementation, and its
  conditional Rao--Blackwell average as a deterministic statistic of the fixed
  pools.
- A finite-alphabet theorem directly instantiable for three independently
  randomized unequal-capacity pools, even when two pools share an alphabet and
  law but remain independently prefixed.

## Statement / milestones
Given a finite index type `I`, per-pool finite alphabets `X i`, iid laws `P i`,
capacities `N i`, independent Poisson prefix lengths with intensities
`lambda i`, and a bounded measurable statistic of the retained variable-length
prefixes, prove:

1. measurability and the exact joint product law of all untruncated prefixes;
2. agreement of capped and untruncated statistics off the union of per-pool
   overflow events;
3. squared-risk contraction under conditional averaging;
4. risk bounded by untruncated Poissonized risk plus bounded loss times the sum
   of the per-pool Poisson upper tails; and
5. the finite-alphabet three-pool specialization described above.

## Standard reference
This is the finite-product extension of the existing Causalean independent
unequal-prefix Rao--Blackwell and Poisson-prefix depoissonization results.

## Intended reuse
Finite decision-theory arguments that independently Poissonize three or more
heterogeneous fixed iid pools. The immediate consumer has one complete-record
pool and two independent treatment--covariate pools, but the API must not refer
to that paper or model.

## May assume / must derive
May assume finite/countable measurable alphabets, probability laws, positive or
nonnegative intensities as required by the existing APIs, bounded loss, and the
usual independence/product-measure setup. Must derive the exact joint prefix
law, off-overflow equality, conditional contraction, and summed overflow-tail
risk bound from those primitives.

## Non-goals (optional)
Do not change or break the existing two-pool interface. Do not import any
`CausalSmith/*_Research` module. Do not specialize names or statements to ATE,
annotation, labels, or auxiliary samples.

## Known building blocks (optional)
- `Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix`
- `Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Depoissonization`
- `Causalean.Stat.FiniteRaoBlackwell.Basic`
- `Mathlib.MeasureTheory.Integral.ConditionalExpectation.Basic`

The completed module and its imports must contain zero `sorry` and introduce no
new axioms.

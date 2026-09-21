# Substrate requirement: random-scale-unequal-two-pool-poisson-minimax-transfer

## Goal
Build reusable minimax and decision-theory substrate transferring a two-prior
lower bound from a shared random-scale marked-Poisson experiment to a fixed,
unequal two-pool sample experiment.

## Provides (API contract)
- A measurable ordered-record retention kernel for two conditionally independent
  marked-Poisson pools whose count intensities are `u * S` and `v * S` for a
  shared measurable nonnegative latent scale `S`.
- A bounded-loss decision-rule transfer comparing raw-experiment Bayes risk to
  fixed unequal-pool Bayes or worst-case risk.
- A composable minimax lower-transfer corollary that accepts a raw fuzzy-prior
  lower bound, scale concentration, Poisson-tail control, and a small-signal
  fixed-sample parametric floor.

## Statement / milestones
Parameterize by a latent parameter law, measurable nonnegative scale `S`,
normalized labeled mark law `P theta`, normalized auxiliary mark law `Q theta`,
fixed sample sizes `n,m`, and raw conditional count intensities `u*S` and `v*S`.
Prove:

1. conditional on counts at least `n` and `m`, the first `n` labeled and first
   `m` auxiliary ordered marks have exact product law
   `(P theta)^n × (Q theta)^m`;
2. a failure bound that splits the event `S` below a deterministic floor from
   the two conditional Poisson lower tails;
3. for any bounded-loss fixed-sample decision rule, a raw-experiment rule whose
   Bayes risk is at most the fixed-sample Bayes or worst-case risk plus bounded
   loss times that failure probability; and
4. a minimax lower-transfer corollary combining a raw two-fuzzy-hypothesis Bayes
   lower bound, the scale-concentration bound, and the small-signal fixed-sample
   parametric floor.

The result must support unequal `n,m`, intensities proportional to `n` and
`n+m`, a scale shared across both pools, and an equality-in-law certificate for
the full auxiliary distribution that is preserved by the transfer.

## Standard reference
This is a random-intensity extension of standard Poissonization,
depoissonization by ordered retention, fuzzy-hypothesis Bayes lower bounds, and
bounded-loss experiment comparison.

## Intended reuse
Minimax lower bounds built from normalized random measures, Cox or mixed-Poisson
experiments, and two fixed samples of unequal sizes. The immediate consumer uses
one labeled and one auxiliary pool, but the API must remain paper-independent.

## May assume / must derive
May assume measurability of the latent scale and mark kernels, probability-law
normalization, conditional independence, bounded loss, a raw Bayes lower bound,
a supplied scale-floor probability bound, and a supplied small-signal
fixed-sample floor. Must derive ordered-retention exactness, the two-tail failure
bound, the decision-rule risk comparison, and the final lower-transfer
composition.

## Non-goals (optional)
Do not import or name any CausalSmith paper research module, ATE construction,
common-marginal recipe, or annotation experiment. Do not assume equal sample
sizes or deterministic unconditional count intensities.

## Known building blocks (optional)
- `Causalean.Stat.Minimax.FuzzyHypotheses`
- `Causalean.Stat.Minimax.Mixture`
- `Causalean.Stat.Minimax.TotalVariation`
- `Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Depoissonization`
- `Causalean.Stat.Concentration.PoissonSelfNormalized.Chernoff`
- `Mathlib.MeasureTheory.Integral.ConditionalExpectation.Basic`

The completed module and its imports must contain zero `sorry` and introduce no
new axioms.

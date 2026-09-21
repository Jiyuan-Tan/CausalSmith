# Substrate requirement: finite-moment-near-gaussian-perturbation

## Goal

Build a reusable, axiom-clean construction of non-Gaussian probability measures arbitrarily close to the standard Gaussian that match any prescribed finite initial segment of its raw moments, while retaining all finite moments and an explicit Carleman-divergence certificate.

## Provides (API contract)

Expose neutral declarations under an appropriate `Causalean.Mathlib.MeasureTheory` or `Causalean.Stat.MomentProblems` namespace:

- A raw-moment definition or compatibility lemma for `\int x, x ^ k \partial\nu`.
- A total-variation distance definition compatible with `sSup {d : \mathbb R | \exists A, MeasurableSet A \land d = |(P A).toReal - (Q A).toReal|}`, or a theorem that implies the corresponding strict bound.
- A main existence theorem: for every `K : \mathbb N` and `rho : \mathbb R` with `3 \le K` and `0 < rho`, there exists a Borel probability measure `F` on `\mathbb R` satisfying all clauses below.
- A finite-moment-to-cumulant transfer theorem showing that equality of raw moments through `K` implies equality of `Causalean.Stat.MomentProblems.sourceCumulant _ id k` through `K`, preferably via `sourceCumulant_eq_cumFromMom`.

Names may follow the established library style; the consumer must be able to specialize the main theorem without importing any `CausalSmith/*_Research` module.

## Statement / milestones

For every `K \ge 3` and `rho > 0`, construct `F : Measure \mathbb R` such that:

1. `IsProbabilityMeasure F`.
2. `\int x, x \partial F = 0` and `ProbabilityTheory.variance id F = 1`.
3. `\neg Causalean.Stat.MomentProblems.IsGaussianLaw F`.
4. The total-variation distance from `F` to `ProbabilityTheory.gaussianReal 0 1` is strictly less than `rho`.
5. For every `k \le K`, `\int x, x ^ k \partial F` equals the corresponding standard-Gaussian raw moment.
6. For every `k`, `Integrable (fun x : \mathbb R => |x| ^ k) F`.
7. The explicit Hamburger-Carleman series
   `\sum' s : \mathbb N, (ENNReal.ofReal |\int x, x ^ (2 * (s + 1)) \partial F|).rpow (-(1 : \mathbb R) / (2 * (s + 1)))`
   diverges to `\top`.
8. For every `k \le K`, the source cumulant of `id` under `F` equals that under the standard Gaussian.

A natural construction is a bounded, nonzero signed density perturbation orthogonal to monomials through degree `K`, scaled small enough that the perturbed Gaussian density remains nonnegative and normalized. Tail domination by a fixed multiple of the Gaussian should yield all finite moments and a moment-growth bound strong enough for the stated Carleman divergence.

## Standard reference

This is the classical finite truncated-moment nonuniqueness/density-perturbation construction combined with the Hamburger Carleman criterion. No paper-specific causal claim belongs in this module.

## Intended reuse

The immediate consumer is `exists_nearGaussian_momentMatching_witness` in `Helpers/VeroneseKruskal.lean`, which needs arbitrary finite `K`, strict TV control, non-Gaussianity, moment matching, all finite moments, and an explicit Carleman certificate before applying its separately cited determinacy criterion. The construction should remain general enough for other finite-moment lower-bound arguments.

## May assume / must derive

May use Mathlib Gaussian measure/integration results and existing Causalean cumulant APIs. Must derive probability normalization, nonnegativity, non-Gaussianity, strict TV control, raw-moment equalities, all-moment integrability, and Carleman divergence. Do not introduce axioms, opaque gates, or `sorry`.

## Non-goals

- Do not formalize a causal model, tensor decomposition, or any paper-specific headline.
- Do not import any `CausalSmith/*_Research` module.
- It is not necessary to prove the full abstract Carleman determinacy theorem if the reusable output supplies exactly the explicit divergence premise needed by an existing/cited criterion.

## Known building blocks

- `Mathlib.Probability.Distributions.Gaussian.Real`.
- `Causalean.Stat.Nonparametric.MomentProblems.Cumulant` and `MomentCumulantInversion.sourceCumulant_eq_cumFromMom`.
- `Causalean.Mathlib.MeasureTheory.exists_moment_perturbation` is only a three-moment finite-support result and is insufficient by itself; generalize rather than pretending it covers arbitrary `K`.
- `Causalean.Stat.MomentProblems.truncatedMomentInterior` is a cumulant-neighborhood result and is not a substitute for exact Gaussian raw-moment matching plus TV/Carleman control.

# Substrate requirement: finite-design Heyde--Brown bridge

## Goal

Build a paper-independent adapter from the existing finite product-design API to an explicitly supplied measure-theoretic Heyde--Brown fourth-moment interface. The adapter must accept the cited theorem as an argument and must not reprove or axiomatize it.

## Provides (API contract)

- Generic prefix-rank and prefix-conditional-expectation definitions for a finite family of coordinate designs and a reveal permutation.
- Identification of the finite product design with its product probability measure and the corresponding reveal filtration conditional expectation.
- Identification of the finite-design predictable variation with the measure-theoretic predictable variation of the prefix-centered increments.
- Identification of the finite-design CDF/Kolmogorov expression with the measure-theoretic expression used by the supplied theorem.
- A specialization theorem yielding the one-fifth-power Kolmogorov bound from prefix centering, normalized second moments, finite fourth moments, and the supplied Heyde--Brown premise.

## Statement / milestones

For finite `Fin N`-indexed coordinate types `alpha i`, coordinate designs `D : forall i, FiniteDesign (alpha i)`, a permutation `pi`, and increments `X : Fin N -> (forall i, alpha i) -> R`, assume every increment has zero prefix conditional expectation and the sum of finite-design second moments is one. Finite fourth moments are automatic. Given the cited Heyde--Brown theorem as an explicit higher-order argument, prove that the Kolmogorov distance of `sum_s X_s` from standard normal is bounded by its constant times the one-fifth power of `sum_s E |X_s|^4 + E |Q-1|^2`, where `Q` is built using the same generic prefix conditional expectation. The proof must identify the product measure, reveal conditional expectation, predictable variation, and CDF interfaces, not merely compare them.

## Standard reference

Finite discrete probability spaces and product filtrations, used solely to instantiate the source-matched Heyde--Brown (1970) martingale inequality at moment parameter two.

## Intended reuse

Design-based randomization-inference arguments on finite product assignments that need to apply an external martingale normal-approximation theorem without rebuilding measure-theoretic adapters per paper.

## May assume / must derive

May accept the Heyde--Brown inequality as an explicit theorem argument. May use `FiniteDesign.toMeasure`, `prodDesign_toMeasure_eq_pi`, and the existing finite expectation/integral bridges. Must derive the finite-design/product-measure, filtration/conditional-expectation, predictable-variation, and CDF/Kolmogorov identifications. No declaration-level axiom may encode Heyde--Brown.

## Non-goals

Do not prove Heyde--Brown, add an axiom for it, or import any `CausalSmith/*_Research` module. Do not define the paper-specific coordinate design, Perron reveal order, CGD increments, Doob decomposition, or graph moment bounds.

## Known building blocks

- `FiniteDesign.toMeasure`
- `prodDesign_toMeasure_eq_pi`
- finite-design expectation/integral and probability/measure bridge lemmas

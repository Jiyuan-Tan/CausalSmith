# Substrate requirement: absolute-value-moment-prior-duality

## Goal
Build a reusable approximation-duality theorem for the absolute-value function on `[-1,1]` that produces symmetric moment-matched probability measures and proves the optimal approximation error is of order `1 / K`.

## Provides (API contract)
- `bestUniformApproxErrorAbs (K : ℕ) : ℝ`: the best uniform error `E_K` for approximating `x ↦ |x|` on `[-1,1]` by real polynomials of degree at most `K`.
- `exists_symmetric_momentMatched_absGap`: for every positive even `K`, symmetric Borel probability measures `ν₀, ν₁` supported on `[-1,1]` whose moments agree through degree `K` and whose absolute first moments differ by exactly `2 E_K` (up to swapping the two measures to orient the difference).
- `bestUniformApproxErrorAbs_order`: universal constants `0 < c ≤ C` such that every positive `K` satisfies `c / K ≤ E_K ≤ C / K`.
- Convenient projection lemmas exposing support, symmetry, probability mass, moment matching, and the absolute-moment gap separately for downstream constructions.

## Statement / milestones
1. Define `E_K` intrinsically as the infimum of the uniform error over degree-`K` polynomials and establish the elementary nonnegativity, monotonicity, and compact-interval formulation needed downstream.
2. Prove the finite-dimensional approximation/measure duality: for every positive even `K`, extremal signed-measure data can be converted into two symmetric probability measures supported on `[-1,1]` that agree on `x^j` for every `0 ≤ j ≤ K` and satisfy

       ∫ |x| dν₁ - ∫ |x| dν₀ = 2 E_K.

   Swapping `ν₀` and `ν₁` may be used if the construction gives the opposite orientation.
3. Prove two-sided universal-rate bounds `c / K ≤ E_K ≤ C / K`; the sharp Bernstein constant is not required.
4. Package the result so later statistical lower-bound constructions can consume the two probability measures without reopening the functional-analytic proof.

## Standard reference
Cai and Low (2011), *Testing composite hypotheses, Hermite polynomials and optimal estimation of a nonsmooth functional*, Lemma 1 and Section 3.1, arXiv:1105.3039. The cited result supplies the moment-matched prior duality and the `1 / K` asymptotics for best polynomial approximation of absolute value.

## Intended reuse
This is a paper-agnostic approximation-theory substrate for fuzzy-hypothesis and moment-matching minimax lower bounds. Its immediate consumer is the dense moment-matching lower-bound branch of `stat_discrete_optimal_value_minimax_matched`, but its declarations must not mention that run, causal models, treatment variables, or a paper-specific parameter space.

## May assume / must derive
May use Mathlib's finite-dimensional separation/Hahn–Banach machinery, compactness and regular Borel probability-measure infrastructure, polynomial facts, and standard Jackson/Bernstein approximation results already proved in Mathlib or Causalean.

Must derive the extremal signed functional or measure, its conversion to supported symmetric probability measures, exact moment agreement, the exact `2 E_K` gap, and the two-sided `1 / K` rate. These conclusions may not be introduced as opaque hypotheses, `axiom`s, or paper-specific assumptions. If a named approximation theorem is absent from the available libraries, prove the amount needed here rather than assuming the desired rate.

## Non-goals (optional)
The sharp Bernstein constant, Gaussian/Hermite estimators, the full Cai–Low statistical model, and any causal-policy theorem are out of scope.

## Known building blocks (optional)
Use the narrowest available Mathlib/Causalean imports for polynomials, continuous functions on compact intervals, integration against finite measures, symmetry/pushforwards, and finite-dimensional duality. The final promoted dependency closure must import only Mathlib/Causalean modules, contain no `sorry` or `admit`, and introduce no new axioms.

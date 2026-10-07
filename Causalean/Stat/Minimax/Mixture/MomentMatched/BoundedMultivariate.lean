module
public import Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate.Approximation
public import Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate.CompactHull
public import Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate.ConstrainedDuality
public import Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate.FeatureSeparation
public import Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate.PoissonTail
public import Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate.PredictiveComparison
public import Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate.ProductTV
public import Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate.Scalar
public import Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate.Triple
public import Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate.TripleConstruction

/-!
# Bounded multivariate moment-matched priors

Construction of the least-favourable prior pairs for marked-Poisson lower bounds. For every degree
`K ≥ 1` there are two finitely supported priors on `[c₀/K², 1]` that give the same mean to `1/x`
and to every power `xᵐ`, `m ≤ 3K`, while their means of `x / (x + q c₀/K²)` differ by a gap not
depending on `K`. These lift to prior pairs on triples (arrival mass `p ≤ b`, propensity
`π ∈ [ε, 1 − ε]`, success probability `μ`) whose mixed moments agree through total degree `3K` and
whose mean success masses differ by at least a constant times `b / K²`. Under such a pair the
marked-Poisson predictive laws of `d` independent cells are within
`d · e^(2nb) (2nb)^(3K+1) / (3K+1)!` in total variation.

## Main results

* `exists_inverseRationalApproxGap` — `x / (x + q c₀/K²)` stays a fixed distance, uniformly in `K`,
  from every `α/x + P(x)` with `deg P ≤ 3K` on `[c₀/K², 1]`.
* `exists_finitePriors_of_constrainedApproxGap` — duality: an approximation gap against finitely
  many continuous constraints yields two finitely supported priors matching every constraint and
  separating the target (via `isCompact_convexHull_finiteDimensional` and feature separation).
* `exists_scalarPriors`, `exists_triplePriors` — the scalar pair (`ScalarPriors`) and the triple
  pair (`TriplePriors`) described above.
* `tvDist_pi_le_sum_heterogeneous` — total variation of a finite product is at most the sum of the
  coordinatewise total variations.
* `tvDist_predictiveLaw_le_factorial`, `tvDist_productPredictive_le_factorial` — the one-cell and
  `d`-cell total-variation bounds (`fourRateFactorialTail_le` supplies the factorial tail).
-/

public section

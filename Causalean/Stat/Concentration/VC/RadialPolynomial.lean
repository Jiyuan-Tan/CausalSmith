module
public import Causalean.Stat.Concentration.VC.Cover
public import Causalean.Stat.Concentration.VC.Geometry
public import Causalean.Stat.Concentration.VC.Score
public import Causalean.Stat.Concentration.VC.Trace

/-!
# Euclidean radial-polynomial VC-subgraph classes

Covering-number bounds for the function classes that appear in local-polynomial empirical-process
arguments. The basic object is the compactly supported radial monomial `(dist(z, x)/q)^k` restricted
to an annulus `a q ≤ dist(z, x) ≤ b q`, with the centre `x ∈ ℝ^d` and the degree `k ≤ p` both
varying. This class has finite pseudo-dimension, bounded explicitly in `d` and `p` only, and hence
polynomial L² covering numbers uniformly over all probability measures; the same holds after
multiplying by finitely many bounded signed arms, forming bounded-coefficient polynomials with a
shared centre, and multiplying by a bounded response residual.

Because every covering statement is uniform over arbitrary probability measures, the bounds remain
valid for atomic laws that charge the moving annulus boundaries.

## Main results

* `radialMonomialClass_hasPseudoDimAtMost` — pseudo-dimension at most `radialPseudoDimBound d p`
  (explicit, non-optimized).
* `radialMonomialClass_hasPolynomialL2Cover` — the uniform polynomial L² cover for the monomials.
* `finiteSignedArmRadial_hasPolynomialL2Cover`, `boundedRadialPolynomialOn_hasPolynomialL2Cover` —
  closure under a finite family of unit-bounded arms and under bounded-coefficient polynomials.
* `radialResidualScore_hasPolynomialL2Cover`, `radialResidualScore_hasUniformPolynomialL2CoverWith`
  — the bounded residual score class, with entropy constants depending only on `d`, `p` and the
  arm type.
* `linearSignClass_hasVCAtMost`, `booleanCombination_hasVCAtMost`, `finiteUnion_hasVCAtMost` — the
  finite-trace VC tools behind these bounds (half-spaces, Boolean combinations, finite unions).
-/

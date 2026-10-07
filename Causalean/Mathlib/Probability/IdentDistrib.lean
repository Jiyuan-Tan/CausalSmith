module
public import Causalean.Mathlib.Probability.IdentDistrib.CenteredSum
public import Causalean.Mathlib.Probability.IdentDistrib.EighthMoment

/-!
# Moment bounds for centered sums of independent identically distributed variables

Two bounds for sums over an i.i.d. sample with product law. Second moment: if the sample
W₁, …, W_s is independent of a σ-algebra A and g(ω, ·) is an A-measurable random function that
is square-integrable under the common law P, then the integral of the square of
s^(−1/2)·Σ_i (g(W_i) − ∫g dP) is at most the integral of ∫g² dP. Eighth moment: for a mark f with
values in [0, 1] and a set S of coordinates, the eighth moment of Σ_{r ∈ S} (f(X_r) − E f) is at
most 8!·((|S|·Var f)⁴ + |S|·Var f).

## Contents

* `IdentDistrib.CenteredSum` — `iid_centered_sum_sq_lintegral_le`, the second-moment bound with
  a random integrand.
* `IdentDistrib.EighthMoment` — `iid_centered_bounded_sum_eighth_moment`, the eighth-moment bound.

This file only gathers the modules above.
-/

module

public import Causalean.Mathlib.Probability.IdentDistrib.EighthMoment.Counting
public import Causalean.Mathlib.Probability.IdentDistrib.EighthMoment.Main
public import Causalean.Mathlib.Probability.IdentDistrib.EighthMoment.Patterns
public import Causalean.Mathlib.Probability.IdentDistrib.EighthMoment.Scalar

/-!
# Eighth moment of a centered sum of bounded i.i.d. variables

Let X_r be i.i.d. and f a measurable function with values in [0, 1]. For every finite set S of
coordinates, the eighth moment of the centered sum Σ_{r ∈ S} (f(X_r) − E f) is at most
8!·((|S|·Var f)⁴ + |S|·Var f). The proof expands the eighth power into index patterns, discards
those in which some coordinate appears exactly once (they integrate to zero), and counts the rest.

## Contents

* `EighthMoment.Scalar` — a centered [0, 1]-valued variable has every centered moment of order at
  least two bounded in absolute value by its variance.
* `EighthMoment.Patterns` — the integral of an eight-fold product factorizes over coordinates and
  vanishes when some coordinate appears once.
* `EighthMoment.Counting` — the variance-weighted count of the surviving index patterns.
* `EighthMoment.Main` — `iid_centered_bounded_sum_eighth_moment`.

This file only gathers the modules above.
-/

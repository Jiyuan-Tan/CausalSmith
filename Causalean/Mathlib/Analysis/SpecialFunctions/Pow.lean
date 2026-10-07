module
public import Causalean.Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Convergence of truncated real powers

For a nonnegative real-valued function f and an exponent s > 0, min(1, f^s) tends to zero along
a filter if and only if f tends to zero (`tendsto_min_one_rpow_zero_iff`). This lets a rate
condition stated for a truncated power be exchanged for plain convergence. The statement lives in
`SpecialFunctions.Pow.Continuity`, which this file gathers.
-/

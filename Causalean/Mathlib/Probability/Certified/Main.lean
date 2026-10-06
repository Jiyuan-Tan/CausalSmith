module
public import Causalean.Mathlib.Probability.Certified.Comparison
public import Causalean.Mathlib.Probability.Certified.NormalCDF

/-!
# Certified finite-state Markov expectations

This is the public aggregation module for exact-rational standard-normal CDF
enclosures, finite interval matrix arithmetic, checked Markov recurrences,
contraction/minorization stationary bounds, and strict stationary-bias
comparisons.  The substrate is generic in the finite state type and contains no
paper-specific transition table, reward, or policy definition.
-/

public section

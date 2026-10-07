/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Discovery.LinearDisentanglement.SimultaneousCongruence.Algebra
public import Causalean.Discovery.LinearDisentanglement.SimultaneousCongruence.Definitions
public import Causalean.Discovery.LinearDisentanglement.SimultaneousCongruence.DefinitionsPairwiseAffine
public import Causalean.Discovery.LinearDisentanglement.SimultaneousCongruence.LocalBranch
public import Causalean.Discovery.LinearDisentanglement.SimultaneousCongruence.Main
public import Causalean.Discovery.LinearDisentanglement.SimultaneousCongruence.PairwiseControl
public import Causalean.Discovery.LinearDisentanglement.SimultaneousCongruence.SmallParameter
public import Causalean.Discovery.LinearDisentanglement.SimultaneousCongruence.Stability

/-!
# Simultaneous-congruence stability and non-uniqueness

Two results on recovering a unit-diagonal matrix B that makes B·Aₑ·Bᵀ diagonal for every
environment e. Stability: if for every pair of coordinates some three environments move the two
diagonal entries in affinely independent directions (a 2×2 determinant of differences is at least
δ > 0), then a unit-diagonal candidate B whose off-diagonal entries of B·Aₑ·Bᵀ are all at most a
small ε, and which lies in an explicit entrywise-L² neighbourhood of an exact invertible
unit-diagonal reference B₀, satisfies ‖B − B₀‖ ≤ C·ε in operator norm with an explicit constant.
Non-uniqueness: if two coordinates of all the diagonal shifts lie on one affine line, then for
every r > 0 there is a deformation with nonzero parameter of size below r that yields a different
invertible unit-diagonal B₁, a positive-definite invariant part and nonnegative shifts
representing exactly the same covariance matrices in every environment.

## Contents

* `DefinitionsPairwiseAffine` — `PairwiseAffineSeparated`, `OffDiagonalApproximateCongruence`, and
  the explicit constants and radii.
* `PairwiseControl`, `LocalBranch` — coordinate bounds for the transition B·B₀⁻¹ and the selection
  of the branch near the identity.
* `Stability` — `opNorm_sub_le_of_pairwise_affine` and its determinant/condition-number
  specialization `opNorm_sub_le_condition_specialization`.
* `Definitions`, `Algebra`, `SmallParameter` — the two-row deformation, its algebraic identities,
  and the choice of a small admissible parameter.
* `Main` — `exists_collinear_simultaneous_congruence_ambiguity`.
-/

public section

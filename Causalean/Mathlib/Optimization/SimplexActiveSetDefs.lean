/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Weighted-simplex active-set SOCP: shared definitions

This file contains the shared definitions for the linear-plus-weighted-norm
second-order cone program
`min_{t ∈ Δ_M} Σ αᵢ tᵢ + κ √(Σ βᵢ tᵢ²)` over the three-point simplex.  It defines
the objective `wsObj`, simplex membership `InSimplex`, KKT support data
`IsAdmissibleSupport`, the induced active-set point `activeSetPoint`, and the
`κ = 0` exposed minimizer face `exposedMinFace`. -/

namespace Causalean.Mathlib.Optimization

open scoped BigOperators

/-- Given [three linear coefficients and three weights](hyp:α,β), [a real
scale](hyp:kappa), and [a three-coordinate allocation](hyp:t), the [weighted-simplex
objective value](goal) is the linear weighted sum of the allocation plus the scale times
the square root of the weighted sum of squared coordinates.

The weighted-simplex objective `Σ αᵢ tᵢ + κ √(Σ βᵢ tᵢ²)` in three coordinates
`(t x, t y, t z)` indexed by `Fin 3`. -/
noncomputable def wsObj (α β : Fin 3 → ℝ) (kappa : ℝ) (t : Fin 3 → ℝ) : ℝ :=
  (∑ i, α i * t i) + kappa * Real.sqrt (∑ i, β i * t i ^ 2)

/-- For [a real total mass](hyp:M) and [a three-coordinate allocation](hyp:t), the
[scaled three-point simplex membership condition](goal) holds exactly when [every coordinate
is nonnegative](step:1) and [the three coordinates sum to the total mass](step:2).

Membership in the scaled 3-point simplex `Δ_M = {t ≥ 0 : Σ tᵢ = M}`. -/
def InSimplex (M : ℝ) (t : Fin 3 → ℝ) : Prop :=
  (∀ i, 0 ≤ t i) ∧ ∑ i, t i = M

/-- Given [three linear coefficients and three weights](hyp:α,β), [a scale](hyp:kappa),
[a set of selected coordinates](hyp:S), and [a real multiplier](hyp:lam), the
[admissible-support condition](goal) holds exactly when [the selected set is nonempty](step:1),
[its summed squared multiplier gaps divided by their weights equal the squared scale](step:2),
[every selected coefficient is strictly below the multiplier](step:3), and [every unselected
coefficient is at least the multiplier](step:4).

KKT-admissible support/multiplier data for the SOCP: a nonempty support
`S ⊆ {x,y,z}` and multiplier `λ` with `Σ_{i∈S} (λ−αᵢ)²/βᵢ = κ²`, the strict
activity `λ > αᵢ` on `S`, and the inactivity `λ ≤ αⱼ` off `S`. -/
def IsAdmissibleSupport (α β : Fin 3 → ℝ) (kappa : ℝ)
    (S : Finset (Fin 3)) (lam : ℝ) : Prop :=
  S.Nonempty ∧
  (∑ i ∈ S, (lam - α i) ^ 2 / β i) = kappa ^ 2 ∧
  (∀ i ∈ S, α i < lam) ∧
  (∀ j ∉ S, lam ≤ α j)

/-- Given [a total mass](hyp:M), [three linear coefficients and three weights](hyp:α,β),
[a selected coordinate set](hyp:S), and [a multiplier](hyp:lam), the [active-set
allocation](goal) [assigns each selected coordinate the total mass times its multiplier
gap divided by its weight and by the sum of those ratios](step:1), and assigns every
unselected coordinate zero.

The active-set coordinate formula
`tᵢ = M ((λ−αᵢ)/βᵢ) / Σ_{h∈S} ((λ−αₕ)/βₕ)` on `S`, and `tᵢ = 0` off `S`. -/
noncomputable def activeSetPoint (M : ℝ) (α β : Fin 3 → ℝ)
    (S : Finset (Fin 3)) (lam : ℝ) : Fin 3 → ℝ :=
  fun i => if i ∈ S then
      M * ((lam - α i) / β i) / (∑ h ∈ S, (lam - α h) / β h) else 0

/-- Given [a total mass](hyp:M) and [three linear coefficients](hyp:α), the [exposed
minimum face](goal) is the set of three-coordinate allocations that [belong to the scaled
simplex](step:1) and have every nonzero coordinate's coefficient no larger than every
coefficient.

The `κ = 0` exposed face `conv{M eᵢ : αᵢ = minⱼ αⱼ}` of `Δ_M`: the simplex
points supported only on the `α`-minimizing coordinates. -/
def exposedMinFace (M : ℝ) (α : Fin 3 → ℝ) : Set (Fin 3 → ℝ) :=
  { t | InSimplex M t ∧ ∀ i, t i ≠ 0 → ∀ j, α i ≤ α j }

end Causalean.Mathlib.Optimization

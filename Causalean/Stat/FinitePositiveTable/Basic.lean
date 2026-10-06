module
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Real.Basic

/-!
# Finite dependent profile spaces and fibre sums

This module provides graph-independent profile spaces and finite-fibre summation for real
tables whose coordinates can have different finite cardinalities.
-/

@[expose] public section

open Finset
open scoped BigOperators

noncomputable section

namespace Causalean.Stat.FinitePositiveTable

universe u uM

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {r : V → ℕ}

/-- The [coordinate cardinalities](hyp:r) determine [the finite dependent profile space](goal) by
[assigning one bounded state to each coordinate](step:1). -/
abbrev ProfileSpace (r : V → ℕ) := ∀ v, Fin (r v)

/-- The [coordinate cardinalities](hyp:r) satisfy [strict positivity of every cardinality](goal)
[when every coordinate has at least one state](step:1). -/
def CardinalitiesPositive (r : V → ℕ) : Prop := ∀ v, 0 < r v

/-- The [coordinate cardinalities](hyp:r) determine [a real-valued kernel on complete
profiles](goal) [as a real-valued function on profiles](step:1). -/
abbrev Kernel (r : V → ℕ) := ProfileSpace r → ℝ

/-- The [coordinate cardinalities](hyp:r) determine a strictly positive normalized real table
whose complete-profile masses are positive and sum to one. -/
structure PositiveTable (r : V → ℕ) where
  /-- The table assigns a real mass to each complete profile. -/
  mass : ProfileSpace r → ℝ
  /-- Every complete profile receives strictly positive mass. -/
  mass_pos : ∀ x, 0 < mass x
  /-- The complete-profile masses sum to one. -/
  sum_mass_eq_one : ∑ x, mass x = 1

/-- The [coordinate set](hyp:S) and [two complete profiles](hyp:x,y) determine [their agreement
on that set](goal) [by equality at every coordinate in the set](step:1). -/
def AgreeOn (S : Finset V) (x y : ProfileSpace r) : Prop :=
  ∀ v ∈ S, x v = y v

/-- The [profile function](hyp:f), [fixed coordinate set](hyp:S), and [reference
profile](hyp:x) determine [the sum over compatible complete profiles](goal) [by retaining exactly
the profiles that agree with the reference on the fixed set](step:1). -/
def fiberSum {M : Type uM} [AddCommMonoid M] (f : ProfileSpace r → M)
    (S : Finset V) (x : ProfileSpace r) : M := by
  classical
  exact ∑ y : ProfileSpace r, if AgreeOn S y x then f y else 0

omit [Fintype V] [DecidableEq V] in
/-- The [two complete profiles](hyp:x,y) [agree on the empty coordinate set](goal). -/
theorem agreeOn_empty (x y : ProfileSpace r) : AgreeOn ∅ x y := by
  simp [AgreeOn]

/-- For [a profile function](hyp:f), [a fixed coordinate set](hyp:S), and [two reference
profiles](hyp:x,x'), [agreement of the reference profiles on the fixed set](hyp:h) makes [their
fibre sums equal](goal). -/
theorem fiberSum_congr_reference {M : Type uM} [AddCommMonoid M]
    (f : ProfileSpace r → M) {S : Finset V} {x x' : ProfileSpace r}
    (h : AgreeOn S x x') : fiberSum f S x = fiberSum f S x' := by
  unfold fiberSum
  apply Finset.sum_congr rfl
  intro y hy
  congr 1
  apply propext
  constructor <;> intro hyAgree
  · exact fun v hv => (hyAgree v hv).trans (h v hv)
  · exact fun v hv => (hyAgree v hv).trans (h v hv).symm

/-- For [a profile function](hyp:f) and [a reference profile](hyp:x), [the unrestricted finite
sum equals the fibre sum with no coordinates fixed](goal). -/
theorem fiberSum_empty {M : Type uM} [AddCommMonoid M]
    (f : ProfileSpace r → M) (x : ProfileSpace r) :
    fiberSum f ∅ x = ∑ y, f y := by
  simp [fiberSum, AgreeOn]

/-- For [a profile function](hyp:f) and [a reference profile](hyp:x), [fixing every coordinate
leaves only that reference profile in the fibre sum](goal). -/
theorem fiberSum_univ {M : Type uM} [AddCommMonoid M]
    (f : ProfileSpace r → M) (x : ProfileSpace r) :
    fiberSum f Finset.univ x = f x := by
  unfold fiberSum
  classical
  simp_rw [show ∀ y, AgreeOn Finset.univ y x ↔ y = x by
    intro y
    constructor
    · intro h
      funext v
      exact h v (Finset.mem_univ v)
    · rintro rfl
      exact fun v hv => rfl]
  simp

/-- For [a profile function](hyp:f), [a fixed coordinate set](hyp:S), [a coordinate outside that
set](hyp:v,hv), [a reference profile](hyp:x), and [a replacement state](hyp:z), [updating the
outside coordinate leaves the fibre sum unchanged](goal). -/
theorem fiberSum_update_of_not_mem {M : Type uM} [AddCommMonoid M]
    (f : ProfileSpace r → M) {S : Finset V} {v : V} (hv : v ∉ S)
    (x : ProfileSpace r) (z : Fin (r v)) :
    fiberSum f S (Function.update x v z) = fiberSum f S x := by
  apply fiberSum_congr_reference f
  intro w hw
  simp only [Function.update_of_ne (ne_of_mem_of_not_mem hw hv)]

/-- For [a profile function](hyp:f), [a fixed coordinate set](hyp:S), [a coordinate outside that
set](hyp:v,hv), and [a reference profile](hyp:x), [partitioning its fibre by the coordinate
value recovers the original fibre sum](goal). -/
theorem sum_fiberSum_insert_update {M : Type uM} [AddCommMonoid M]
    (f : ProfileSpace r → M) {S : Finset V} {v : V} (hv : v ∉ S)
    (x : ProfileSpace r) :
    (∑ z : Fin (r v), fiberSum f (insert v S) (Function.update x v z)) =
      fiberSum f S x := by
  classical
  have hAgree (z : Fin (r v)) (y : ProfileSpace r) :
      AgreeOn (insert v S) y (Function.update x v z) ↔
        AgreeOn S y x ∧ y v = z := by
    constructor
    · intro h
      constructor
      · intro w hw
        have hwy := h w (mem_insert_of_mem hw)
        simpa only [Function.update_of_ne (ne_of_mem_of_not_mem hw hv)] using hwy
      · simpa only [Function.update_self] using h v (mem_insert_self v S)
    · rintro ⟨hS, hyv⟩ w hw
      rcases mem_insert.mp hw with rfl | hw
      · simpa only [Function.update_self] using hyv
      · simpa only [Function.update_of_ne (ne_of_mem_of_not_mem hw hv)] using hS w hw
  unfold fiberSum
  calc
    (∑ z : Fin (r v), ∑ y : ProfileSpace r,
        if AgreeOn (insert v S) y (Function.update x v z) then f y else 0) =
        ∑ z : Fin (r v), ∑ y ∈ Finset.univ with y v = z,
          if AgreeOn S y x then f y else 0 := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y hy
      rw [hAgree z y]
      by_cases hS : AgreeOn S y x <;> by_cases hyv : y v = z <;> simp [hS, hyv]
    _ = ∑ y : ProfileSpace r, if AgreeOn S y x then f y else 0 := by
      exact Finset.sum_fiberwise Finset.univ (fun y : ProfileSpace r => y v)
        (fun y => if AgreeOn S y x then f y else 0)

/-- For [a profile function](hyp:f), [a coordinate](hyp:v), and [a reference profile](hyp:x),
[summing its singleton-coordinate fibres recovers the unrestricted finite sum](goal). -/
theorem sum_fiberSum_singleton_update {M : Type uM} [AddCommMonoid M]
    (f : ProfileSpace r → M) (v : V) (x : ProfileSpace r) :
    (∑ z : Fin (r v), fiberSum f {v} (Function.update x v z)) = ∑ y, f y := by
  simpa [fiberSum_empty] using
    sum_fiberSum_insert_update f (S := ∅) (v := v) (by simp) x

end Causalean.Stat.FinitePositiveTable

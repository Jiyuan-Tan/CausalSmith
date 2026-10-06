module
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Measurability of finite real matrix operations

This module proves entrywise measurability of determinants and nonsingular inverses for
finite real matrices whose entries vary measurably.
-/

public section

namespace Causalean.Mathlib.MeasureTheory

open _root_.MeasureTheory

/-- For [a measurable source and finite index type](hyp:Ω,ι), if [every entry of a finite
real matrix-valued function is measurable](hyp:A,hA), then [its determinant is
measurable](goal). -/
@[fun_prop]
theorem measurable_matrix_det {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] (A : Ω → Matrix ι ι ℝ)
    (hA : ∀ i j, Measurable (fun ω => A ω i j)) :
    Measurable (fun ω => (A ω).det) := by
  simp only [Matrix.det_apply]
  apply Finset.measurable_fun_sum
  intro σ _
  apply measurable_const.smul
  apply Finset.measurable_fun_prod
  intro i _
  exact hA (σ i) i

/-- For [a measurable source and finite index type](hyp:Ω,ι), if [every entry of a finite
real matrix-valued function is measurable](hyp:A,hA), then [the entry at the specified row
and column](hyp:i,j) [of its nonsingular inverse is measurable](goal). -/
@[fun_prop]
theorem measurable_matrix_inv_apply {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι]
    (A : Ω → Matrix ι ι ℝ)
    (hA : ∀ i j, Measurable (fun ω => A ω i j)) (i j : ι) :
    Measurable (fun ω => (A ω)⁻¹ i j) := by
  rw [show (fun ω => (A ω)⁻¹ i j) =
      fun ω => Ring.inverse (A ω).det * (A ω).adjugate i j by
    funext ω
    simp [Matrix.inv_def]]
  simp_rw [Ring.inverse_eq_inv]
  apply (measurable_matrix_det A hA).inv.mul
  rw [show (fun ω => (A ω).adjugate i j) =
      fun ω => ((A ω).updateRow j (Pi.single i 1)).det by
    funext ω
    exact Matrix.adjugate_apply _ _ _]
  apply measurable_matrix_det
  intro a b
  by_cases ha : a = j
  · subst a
    simp [Matrix.updateRow_self]
  · simp [Matrix.updateRow_apply, ha]
    exact hA a b

end Causalean.Mathlib.MeasureTheory

module
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.Definitions
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Balanced pairs of multinomial coordinates

Each latent scalar perturbs two cells in opposite directions, preserving their
combined mass. This module supplies the exact probability vectors and L1
identity used in the large-sample fuzzy construction.
-/

@[expose] public section

namespace Causalean.Stat.Minimax.Multinomial.TwoSampleL1

open scoped BigOperators

/-- The uniform probability vector on `b` pairs of two cells. -/
noncomputable def pairedBaseVector (b : ℕ) (hb : 0 < b) :
    ProbabilitySimplex (b * 2) :=
  ⟨fun _ => 1 / ((b : ℝ) * 2), by
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
    constructor
    · intro i
      positivity
    · simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      push_cast
      field_simp⟩

/-- The probability vector obtained by raising the first cell and lowering
the second cell in each pair by the same scalar amount. Each latent parameter
is in `[-1,1]`, and the common perturbation scale is in `[0,1]`. -/
noncomputable def pairedTiltVector (b : ℕ) (hb : 0 < b)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (u : Fin b → ℝ) (hu : ∀ j, |u j| ≤ 1) :
    ProbabilitySimplex (b * 2) :=
  ⟨fun i =>
    let p := finProdFinEquiv.symm i
    (1 + (if p.2 = 0 then t * u p.1 else -(t * u p.1))) / ((b : ℝ) * 2), by
      have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
      have hden : 0 < (b : ℝ) * 2 := by positivity
      constructor
      · intro i
        let p := (finProdFinEquiv : Fin b × Fin 2 ≃ Fin (b * 2)).symm i
        have hlow := (abs_le.mp (hu p.1)).1
        have hupp := (abs_le.mp (hu p.1)).2
        have htp : -1 ≤ t * u p.1 ∧ t * u p.1 ≤ 1 := by
          constructor
          · nlinarith [mul_nonneg ht (by linarith : 0 ≤ 1 + u p.1)]
          · nlinarith [mul_nonneg ht (by linarith : 0 ≤ 1 - u p.1)]
        change 0 ≤ (1 + (if p.2 = 0 then t * u p.1 else -(t * u p.1))) /
          ((b : ℝ) * 2)
        apply div_nonneg (by split_ifs <;> linarith) (le_of_lt hden)
      · rw [← Equiv.sum_comp (finProdFinEquiv : Fin b × Fin 2 ≃ Fin (b * 2))]
        simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
        simp only [Fin.isValue, Equiv.symm_apply_apply, ↓reduceIte, one_ne_zero]
        calc
          _ = ∑ _x : Fin b, (b : ℝ)⁻¹ := by
            apply Finset.sum_congr rfl
            intro x hx
            field_simp
            ring
          _ = 1 := by simp [hb']⟩

/-- Given [a positive balanced pair count](hyp:b,hb), [a bounded nonnegative tilt](hyp:t,ht,ht1), and [bounded cell directions](hyp:u,hu), [the L1 distance from the balanced base vector equals its coordinatewise absolute tilt total](goal). -/
theorem pairedBase_tilt_l1 (b : ℕ) (hb : 0 < b)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (u : Fin b → ℝ) (hu : ∀ j, |u j| ≤ 1) :
    simplexL1 (pairedBaseVector b hb)
      (pairedTiltVector b hb t ht ht1 u hu) =
        t / (b : ℝ) * ∑ j : Fin b, |u j| := by
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hden : 0 < (b : ℝ) * 2 := by positivity
  unfold simplexL1
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin b × Fin 2 ≃ Fin (b * 2))]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [pairedBaseVector, pairedTiltVector, Subtype.coe_mk,
    Equiv.symm_apply_apply, Fin.isValue, ↓reduceIte, one_ne_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hfirst : 1 / ((b : ℝ) * 2) - (1 + t * u j) / ((b : ℝ) * 2) =
      -(t * u j) / ((b : ℝ) * 2) := by ring
  have hsecond : 1 / ((b : ℝ) * 2) - (1 + -(t * u j)) / ((b : ℝ) * 2) =
      (t * u j) / ((b : ℝ) * 2) := by ring
  rw [hfirst, hsecond, abs_div, abs_div, abs_neg, abs_mul, abs_of_nonneg ht,
    abs_of_pos hden]
  field_simp
  ring

end Causalean.Stat.Minimax.Multinomial.TwoSampleL1

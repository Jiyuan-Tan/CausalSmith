module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BlockPrior
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite Walsh Parseval identities

The Boolean delta kernel, inversion, and squared coefficient norm used in the channel energy proof.
-/

public section

noncomputable section
open scoped BigOperators
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- The sum of products of two sign characters is the Boolean-cube delta kernel.  [For the stated data and conditions](hyp:d,ε,δ), [the stated conclusion holds](goal). -/
-- @node: sign_character_delta_kernel
lemma sign_character_delta_kernel (d : ℕ) (ε δ : Fin d → Bool) :
    (∑ E : Finset (Fin d), (∏ j ∈ E, signOf (δ j)) *
      ∏ j ∈ E, signOf (ε j)) = if δ = ε then (2 : ℝ) ^ d else 0 := by
  have hk : (∑ E : Finset (Fin d), (∏ j ∈ E, signOf (δ j)) *
      ∏ j ∈ E, signOf (ε j)) = ∏ j : Fin d, (signOf (δ j) * signOf (ε j) + 1) := by
    simpa only [Finset.prod_mul_distrib, Finset.prod_const_one, mul_one] using
      (Fintype.prod_add (fun j : Fin d => signOf (δ j) * signOf (ε j)) (fun _ => (1 : ℝ))).symm
  rw [hk]
  by_cases he : δ = ε
  · subst δ
    rw [if_pos rfl]
    have hs (j : Fin d) : signOf (ε j) * signOf (ε j) + 1 = 2 := by
      cases ε j <;> norm_num [signOf]
    simp_rw [hs]
    simp
  · rw [if_neg he]
    obtain ⟨j, hj⟩ : ∃ j, δ j ≠ ε j := by
      by_contra h
      apply he
      funext j
      by_contra hj
      exact h ⟨j, hj⟩
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    cases hd : δ j <;> cases he : ε j <;> simp_all [signOf]

/-- Finite Walsh inversion follows by summing the Boolean delta kernel.  [For the stated data and conditions](hyp:d,F,ε), [the stated conclusion holds](goal). -/
-- @node: finite_walsh_inversion
lemma finite_walsh_inversion (d : ℕ) (F : (Fin d → Bool) → ℝ) (ε : Fin d → Bool) :
    F ε = ∑ E : Finset (Fin d),
      (((2 : ℝ) ^ d)⁻¹ * ∑ δ : Fin d → Bool, F δ * ∏ j ∈ E, signOf (δ j)) *
        ∏ j ∈ E, signOf (ε j) := by
  simp_rw [mul_assoc, Finset.sum_mul, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, sign_character_delta_kernel]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [mul_comm (F ε), ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- The squared Walsh coefficients sum to the uniformly averaged squared response.  [For the stated data and conditions](hyp:d,F), [the stated conclusion holds](goal). -/
-- @node: finite_walsh_parseval
lemma finite_walsh_parseval (d : ℕ) (F : (Fin d → Bool) → ℝ) :
    (∑ E : Finset (Fin d),
      (((2 : ℝ) ^ d)⁻¹ * ∑ ε : Fin d → Bool,
        F ε * ∏ j ∈ E, signOf (ε j)) ^ 2) =
      ((2 : ℝ) ^ d)⁻¹ * ∑ ε : Fin d → Bool, (F ε) ^ 2 := by
  let c : ℝ := ((2 : ℝ) ^ d)⁻¹
  have he (E : Finset (Fin d)) :
      (c * ∑ ε : Fin d → Bool, F ε * ∏ j ∈ E, signOf (ε j)) ^ 2 =
        c ^ 2 * ∑ ε : Fin d → Bool, ∑ δ : Fin d → Bool,
          (F ε * F δ) * ((∏ j ∈ E, signOf (ε j)) * ∏ j ∈ E, signOf (δ j)) := by
    rw [mul_pow]
    congr 1
    rw [pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ε _
    apply Finset.sum_congr rfl
    intro δ _
    ring
  change (∑ E : Finset (Fin d), (c * _) ^ 2) = c * _
  simp_rw [he]
  rw [← Finset.mul_sum]
  have hk : (∑ E : Finset (Fin d), ∑ ε : Fin d → Bool, ∑ δ : Fin d → Bool,
      (F ε * F δ) * ((∏ j ∈ E, signOf (ε j)) * ∏ j ∈ E, signOf (δ j))) =
      (2 : ℝ) ^ d * ∑ ε : Fin d → Bool, (F ε) ^ 2 := by
    rw [Finset.sum_comm]
    conv_lhs =>
      arg 2
      ext ε
      rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sign_character_delta_kernel]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp_rw [← pow_two, mul_comm _ ((2 : ℝ) ^ d)]
    rw [Finset.mul_sum]
  rw [hk]
  dsimp [c]
  have hc : ((2 : ℝ) ^ d) ≠ 0 := by positivity
  field_simp


/-- Flipping one Boolean coordinate negates exactly the characters that contain it.  [For the stated data and conditions](hyp:d,E,ε,j), [the stated conclusion holds](goal). -/
-- @node: sign_character_flip
lemma sign_character_flip (d : ℕ) (E : Finset (Fin d)) (ε : Fin d → Bool)
    (j : Fin d) :
    (∏ i ∈ E, signOf (Function.update ε j (!(ε j)) i)) =
      (if j ∈ E then -1 else 1) * ∏ i ∈ E, signOf (ε i) := by
  by_cases hj : j ∈ E
  · rw [if_pos hj, ← Finset.prod_erase_mul _ _ hj,
      ← Finset.prod_erase_mul _ _ hj]
    have he : (∏ i ∈ E.erase j, signOf (Function.update ε j (!(ε j)) i)) =
        ∏ i ∈ E.erase j, signOf (ε i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
    rw [he, Function.update_self]
    have hn : signOf (!(ε j)) = -signOf (ε j) := by cases ε j <;> norm_num [signOf]
    rw [hn]
    ring
  · rw [if_neg hj, one_mul]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (by intro he; subst i; exact hj hi)]

/-- A coordinate flip multiplies each finite Walsh coefficient by its character sign.  [For the stated data and conditions](hyp:d,F,E,j), [the stated conclusion holds](goal). -/
-- @node: finite_walsh_coefficient_flip
lemma finite_walsh_coefficient_flip (d : ℕ) (F : (Fin d → Bool) → ℝ)
    (E : Finset (Fin d)) (j : Fin d) :
    (∑ ε : Fin d → Bool, F (Function.update ε j (!(ε j))) * ∏ i ∈ E, signOf (ε i)) =
      (if j ∈ E then -1 else 1) * ∑ ε : Fin d → Bool, F ε * ∏ i ∈ E, signOf (ε i) := by
  let flip := fun ε : Fin d → Bool => Function.update ε j (!(ε j))
  have hinv : Function.Involutive flip := by
    intro ε
    funext i
    by_cases hi : i = j
    · subst i; simp [flip]
    · simp [flip, Function.update_of_ne hi]
  let e := hinv.toPerm
  have hc (ε : Fin d → Bool) :
      F (flip ε) * (∏ i ∈ E, signOf (ε i)) =
        (if j ∈ E then -1 else 1) *
          (F (e ε) * ∏ i ∈ E, signOf (e ε i)) := by
    change F (flip ε) * _ = _ * (F (flip ε) * _)
    change F (flip ε) * _ = _ * (F (flip ε) *
      ∏ i ∈ E, signOf (Function.update ε j (!(ε j)) i))
    rw [sign_character_flip]
    split_ifs <;> ring
  change (∑ ε : Fin d → Bool, F (flip ε) * _) = _
  simp_rw [hc]
  rw [← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp e (fun ε => F ε * ∏ i ∈ E, signOf (ε i))

/-- Parseval for a coordinate difference retains only Walsh subsets containing that coordinate.  [For the stated data and conditions](hyp:d,F,j), [the stated conclusion holds](goal). -/
-- @node: finite_walsh_flip_parseval
lemma finite_walsh_flip_parseval (d : ℕ) (F : (Fin d → Bool) → ℝ) (j : Fin d) :
    (∑ E : Finset (Fin d), if j ∈ E then
      (((2 : ℝ) ^ d)⁻¹ * ∑ ε : Fin d → Bool,
        F ε * ∏ i ∈ E, signOf (ε i)) ^ 2 else 0) =
      (1 / 4 : ℝ) * ((2 : ℝ) ^ d)⁻¹ * ∑ ε : Fin d → Bool,
        (F ε - F (Function.update ε j (!(ε j)))) ^ 2 := by
  have hp := finite_walsh_parseval d (fun ε => F ε - F (Function.update ε j (!(ε j))))
  have hc (E : Finset (Fin d)) :
      (((2 : ℝ) ^ d)⁻¹ * ∑ ε : Fin d → Bool,
        (F ε - F (Function.update ε j (!(ε j)))) * ∏ i ∈ E, signOf (ε i)) ^ 2 =
      4 * (if j ∈ E then
        (((2 : ℝ) ^ d)⁻¹ * ∑ ε : Fin d → Bool, F ε * ∏ i ∈ E, signOf (ε i)) ^ 2 else 0) := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, finite_walsh_coefficient_flip]
    split_ifs <;> ring
  simp_rw [hc] at hp
  rw [← Finset.mul_sum] at hp
  linarith

/-- Summing coordinate differences weights each squared coefficient by its subset size.  [For the stated data and conditions](hyp:d,F), [the stated conclusion holds](goal). -/
-- @node: finite_walsh_weighted_parseval
lemma finite_walsh_weighted_parseval (d : ℕ) (F : (Fin d → Bool) → ℝ) :
    (∑ E : Finset (Fin d), (E.card : ℝ) *
      (((2 : ℝ) ^ d)⁻¹ * ∑ ε : Fin d → Bool, F ε * ∏ i ∈ E, signOf (ε i)) ^ 2) =
      (1 / 4 : ℝ) * ∑ j : Fin d,
        ((2 : ℝ) ^ d)⁻¹ * ∑ ε : Fin d → Bool,
          (F ε - F (Function.update ε j (!(ε j)))) ^ 2 := by
  have hc (E : Finset (Fin d)) (a : ℝ) :
      (E.card : ℝ) * a = ∑ j : Fin d, if j ∈ E then a else 0 := by simp
  simp_rw [hc]
  rw [Finset.sum_comm]
  simp_rw [finite_walsh_flip_parseval]
  simp only [Finset.mul_sum, mul_assoc]

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier

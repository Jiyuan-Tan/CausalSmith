module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.ClassicalFactInterfaces
public import Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi.Legendre

/-!
# Exact classical Legendre facts

This module discharges the run's cited Legendre interface from Mathlib's
shifted Legendre polynomials and Causalean's Jacobi and Legendre identities.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace CausalSmith.Stat.RdTruesideNoiseFrontier

open Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi

/-- Given [the displayed inputs and assumptions](hyp:j,k), [the stated mathematical conclusion holds](goal). -/
lemma legendreP_orthogonal_exact (j k : ℕ) :
    (∫ t in (-1 : ℝ)..1, legendreP j t * legendreP k t) =
      if j = k then 2 / (2 * (j : ℝ) + 1) else 0 := by
  let F : ℝ → ℝ := fun t => legendreP j t * legendreP k t
  have h := intervalIntegral.integral_comp_mul_add F
    (a := (0 : ℝ)) (b := 1) (c := (-2 : ℝ)) (by norm_num) 1
  norm_num only [mul_zero, zero_add, mul_one, neg_mul, neg_add_cancel,
    inv_neg, smul_eq_mul] at h
  have hleft : (∫ x in (0 : ℝ)..1, F (-2*x+1)) =
      if j = k then 1 / (2 * (j : ℝ) + 1) else 0 := by
    simpa only [F, legendreP, show ∀ x : ℝ, (1 - (-2*x+1))/2 = x by intro x; ring]
      using shiftedLegendre_orthogonal_unit j k
  have haff : (fun x : ℝ => F (-(2*x)+1)) = fun x => F (-2*x+1) := by
    funext x
    congr 1
    ring
  rw [haff, hleft] at h
  have hsymm : (∫ x in (1 : ℝ)..(-1), F x) =
      -(∫ x in (-1 : ℝ)..1, F x) := intervalIntegral.integral_symm (-1) 1
  rw [hsymm] at h
  split_ifs with hjk
  · simp only [if_pos hjk] at h
    dsimp [F] at h
    have hd : (2*(j:ℝ)+1) ≠ 0 := by positivity
    field_simp [hd] at h ⊢
    linarith
  · simp only [if_neg hjk] at h
    dsimp [F] at h
    linarith

/-- Given [the displayed inputs and assumptions](hyp:j,t), [the stated mathematical conclusion holds](goal). -/
lemma legendreP_reflection_exact (j : ℕ) (t : ℝ) :
    legendreP j (-t) = (-1 : ℝ)^j * legendreP j t := by
  unfold legendreP
  have h := Polynomial.shiftedLegendre_eval_symm j ((1+t)/2 : ℝ)
  convert h using 1 <;> ring

/-- Given [the displayed inputs and assumptions](hyp:j,t,ht), [the stated mathematical conclusion holds](goal). -/
lemma legendreP_abs_le_one_exact (j : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) : |legendreP j t| ≤ 1 := by
  unfold legendreP
  rw [← jacobiShifted_zero_zero_eq_shiftedLegendre]
  apply jacobiShifted_abs_le_one j 0 0 ((1-t)/2)
  · norm_num
  · norm_num
  · norm_num
  · constructor <;> linarith [ht.1, ht.2]

/-- Given [the displayed inputs and assumptions](hyp:j), [the stated mathematical conclusion holds](goal). -/
lemma legendreP_one_exact (j : ℕ) : legendreP j 1 = 1 := by
  unfold legendreP
  rw [show (1-(1:ℝ))/2 = 0 by norm_num,
    ← jacobiShifted_zero_zero_eq_shiftedLegendre,
    jacobiShifted_zero]

/-- Given [the displayed inputs and assumptions](hyp:j), [the stated mathematical conclusion holds](goal). -/
lemma legendreP_neg_one_exact (j : ℕ) :
    legendreP j (-1) = (-1 : ℝ)^j := by
  rw [legendreP_reflection_exact, legendreP_one_exact, mul_one]

/-- The exact cited Legendre interface follows from Mathlib's shifted Legendre
polynomials and Causalean's normalized Jacobi bound and beta calculus. Given the displayed inputs, [the stated mathematical conclusion holds](goal). -/
theorem classicalLegendreFacts_of_mathlib : ClassicalLegendreFacts := by
  intro j k
  exact ⟨legendreP_orthogonal_exact j k,
    legendreP_reflection_exact j,
    legendreP_abs_le_one_exact j,
    legendreP_neg_one_exact j⟩

end CausalSmith.Stat.RdTruesideNoiseFrontier

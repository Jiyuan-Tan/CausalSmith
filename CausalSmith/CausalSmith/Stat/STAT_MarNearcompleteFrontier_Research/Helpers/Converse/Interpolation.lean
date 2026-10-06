module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.PairedPrior

/-! # Lagrange moment cancellation for the paired latent distribution -/

public section
namespace CausalSmith.Stat.MarNearcompleteFrontier
open Polynomial

-- @node: priorK_ge_two
/-- Given [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). -/
lemma priorK_ge_two (n : ℕ) : 2 ≤ priorK n := by
  have he : (Real.exp 1 : ℝ) ≤ Real.exp 1 + n :=
    le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hl : 1 ≤ ell n := by
    unfold ell
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp _).symm
      _ ≤ Real.log (Real.exp 1 + n) := Real.log_le_log (Real.exp_pos _) he
  have hk : 8 * ell n ≤ (priorK n : ℝ) := by
    unfold priorK
    exact Nat.le_ceil _
  exact_mod_cast (show (2 : ℝ) ≤ priorK n by linarith)

-- @node: interpolationNode_injective
/-- Given [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). -/
lemma interpolationNode_injective (n : ℕ) : Function.Injective (interpolationNode n) := by
  intro i j hij
  have hk := priorK_ge_two n
  have hh : priorH n < 1 := by
    unfold priorH
    have hkr : (2 : ℝ) ≤ priorK n := by exact_mod_cast hk
    have hi : (priorK n : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]
      apply (div_le_iff₀ (by linarith : (0 : ℝ) < priorK n)).mpr
      nlinarith
    have hnonneg : (0 : ℝ) ≤ (priorK n : ℝ)⁻¹ := by positivity
    nlinarith
  have hden : (0 : ℝ) < ((priorK n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < priorK n - 1 by omega)
  have hangle (i : Fin (priorK n)) :
      (i : ℝ) * Real.pi / ((priorK n - 1 : ℕ) : ℝ) ∈ Set.Icc 0 Real.pi := by
    constructor
    · positivity
    · have hi : i.val ≤ priorK n - 1 := by omega
      have hir : (i : ℝ) ≤ ((priorK n - 1 : ℕ) : ℝ) := by exact_mod_cast hi
      apply (div_le_iff₀ hden).mpr
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hir Real.pi_nonneg
  have hcos : Real.cos ((i : ℝ) * Real.pi / ((priorK n - 1 : ℕ) : ℝ)) =
      Real.cos ((j : ℝ) * Real.pi / ((priorK n - 1 : ℕ) : ℝ)) := by
    unfold interpolationNode at hij
    have hc : (1 - priorH n) / 2 ≠ 0 := by linarith
    have hm : (1 - priorH n) / 2 * Real.cos
        ((i : ℝ) * Real.pi / ((priorK n - 1 : ℕ) : ℝ)) =
        (1 - priorH n) / 2 * Real.cos
        ((j : ℝ) * Real.pi / ((priorK n - 1 : ℕ) : ℝ)) := by
      exact add_left_cancel hij
    exact mul_left_cancel₀ hc hm
  have ha := Real.injOn_cos (hangle i) (hangle j) hcos
  have hcast : (i : ℝ) = (j : ℝ) := by
    field_simp [ne_of_gt hden, ne_of_gt Real.pi_pos] at ha
    exact ha
  exact Fin.ext (by exact_mod_cast hcast)

/-- For [a positive moment order](hyp:ht) below [the number of interpolation nodes](hyp:hdegree), [the signed interpolation weights have zero moment of that order](goal). -/
lemma signedNodeWeight_moment_zero (n t : ℕ) (ht : 0 < t) (hdegree : t < priorK n) :
    (∑ i : Fin (priorK n), signedNodeWeight n i *
      interpolationNode n i ^ t) = 0 := by
  have hpoly : (Polynomial.X : ℝ[X]) ^ t =
      Lagrange.interpolate Finset.univ (interpolationNode n)
        (fun i => interpolationNode n i ^ t) := by
    have hi : Set.InjOn (interpolationNode n) (Finset.univ : Finset (Fin (priorK n))) := by
      intro i _ j _ hij
      exact interpolationNode_injective n hij
    have hd : ((Polynomial.X : ℝ[X]) ^ t).degree <
        (Finset.univ : Finset (Fin (priorK n))).card := by
      simpa [Polynomial.degree_X_pow] using hdegree
    simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
      (Lagrange.eq_interpolate (f := (Polynomial.X : ℝ[X]) ^ t) hi hd)
  have hsum : (∑ i : Fin (priorK n), lagrangeAtZero n i *
      interpolationNode n i ^ t) = 0 := by
    have heval := congrArg (fun p : ℝ[X] => p.eval 0) hpoly
    simp only [Polynomial.eval_pow, Polynomial.eval_X, zero_pow (Nat.ne_of_gt ht),
      Lagrange.interpolate_apply, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C] at heval
    simpa only [lagrangeAtZero, mul_comm] using heval.symm
  unfold signedNodeWeight
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  simp [hsum]

end CausalSmith.Stat.MarNearcompleteFrontier

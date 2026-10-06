module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.LowerPairBounds
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Whole-line derivative bounds for the lower-pair cutoff

Polynomial representations of the flat exponential glue establish the bounded
one-dimensional derivatives used in steps (1)--(4) of the membership roadmap.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate
open Polynomial

/-- Every nonnegative power times a decaying exponential has a factorial bound. -/
-- @node: pow_mul_exp_neg_le_factorial
lemma pow_mul_exp_neg_le_factorial (n : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    u ^ n * Real.exp (-u) ≤ (n.factorial : ℝ) := by
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hb := Real.pow_div_factorial_le_exp u hu n
  have hb' : u ^ n ≤ (n.factorial : ℝ) * Real.exp u := by
    simpa only [mul_comm] using (div_le_iff₀ hf).mp hb
  calc
    u ^ n * Real.exp (-u) ≤ ((n.factorial : ℝ) * Real.exp u) * Real.exp (-u) :=
      mul_le_mul_of_nonneg_right hb' (Real.exp_pos _).le
    _ = (n.factorial : ℝ) := by rw [mul_assoc, ← Real.exp_add]; simp

/-- Every polynomial-weighted flat glue is bounded on the whole line. -/
-- @node: polynomial_glue_global_bound
lemma polynomial_glue_global_bound (p : ℝ[X]) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, |p.eval x⁻¹ * expNegInvGlue x| ≤ B := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨Bp, hp0, hp⟩ := hp
    obtain ⟨Bq, hq0, hq⟩ := hq
    refine ⟨Bp + Bq, add_nonneg hp0 hq0, fun x => ?_⟩
    simpa only [Polynomial.eval_add, add_mul] using
      (abs_add_le (p.eval x⁻¹ * expNegInvGlue x)
        (q.eval x⁻¹ * expNegInvGlue x)).trans (add_le_add (hp x) (hq x))
  | monomial n a =>
    refine ⟨|a| * (n.factorial : ℝ), by positivity, fun x => ?_⟩
    by_cases hx : x ≤ 0
    · simp only [expNegInvGlue.zero_of_nonpos hx, mul_zero, abs_zero]
      positivity
    · have hi : 0 ≤ x⁻¹ := inv_nonneg.mpr (le_of_not_ge hx)
      simp only [Polynomial.eval_monomial, expNegInvGlue, if_neg hx, abs_mul,
        abs_of_nonneg (pow_nonneg hi n), abs_of_pos (Real.exp_pos _), mul_assoc]
      exact mul_le_mul_of_nonneg_left (pow_mul_exp_neg_le_factorial n x⁻¹ hi)
        (abs_nonneg a)

/-- Each derivative of the paper cutoff is a polynomial-weighted affine flat glue. -/
-- @node: bump1_iteratedDeriv_polynomial
lemma bump1_iteratedDeriv_polynomial (n : ℕ) :
    ∃ p : ℝ[X], iteratedDeriv n bump1 =
      fun t => p.eval (1 - 2 * t)⁻¹ * expNegInvGlue (1 - 2 * t) := by
  induction n with
  | zero =>
    refine ⟨Polynomial.C (Real.exp 1), ?_⟩
    funext t
    simpa using bump1_eq_expNegInvGlue t
  | succ n ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨Polynomial.C (-2) * (Polynomial.X ^ 2 * (p - Polynomial.derivative p)), ?_⟩
    rw [iteratedDeriv_succ, hp]
    funext t
    have hd := (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul p (1 - 2 * t)).comp t
      ((hasDerivAt_const t 1).sub ((hasDerivAt_id t).const_mul 2))
    convert hd.deriv using 1 <;>
      simp [Polynomial.eval_mul, Polynomial.eval_C, Function.comp_def, Pi.sub_apply]; ring

/-- All orders of the cutoff derivative have finite whole-line bounds. -/
-- @node: bump1_iteratedDeriv_bounded
lemma bump1_iteratedDeriv_bounded (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, |iteratedDeriv n bump1 t| ≤ B := by
  obtain ⟨p, hp⟩ := bump1_iteratedDeriv_polynomial n
  obtain ⟨B, hB, hb⟩ := polynomial_glue_global_bound p
  refine ⟨B, hB, fun t => ?_⟩
  rw [hp]
  exact hb (1 - 2 * t)

/-- The next bounded derivative controls increments of every cutoff derivative. -/
-- @node: bump1_iteratedDeriv_lipschitz_bound
lemma bump1_iteratedDeriv_lipschitz_bound (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x y : ℝ,
      |iteratedDeriv n bump1 x - iteratedDeriv n bump1 y| ≤ B * |x - y| := by
  obtain ⟨B, hB, hb⟩ := bump1_iteratedDeriv_bounded (n + 1)
  have hd : Differentiable ℝ (iteratedDeriv n bump1) :=
    ContDiff.differentiable_iteratedDeriv' n bump1_contDiff
  refine ⟨B, hB, fun x y => ?_⟩
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.univ) (fun t _ => hd t)
    (fun t _ => by simpa only [← iteratedDeriv_succ, Real.norm_eq_abs] using hb t)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using h

/-- Boundedness and the mean value bound give every exponent between zero and one. -/
-- @node: bump1_iteratedDeriv_holder_bound
lemma bump1_iteratedDeriv_holder_bound (n : ℕ) (α : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x y : ℝ,
      |iteratedDeriv n bump1 x - iteratedDeriv n bump1 y| ≤ B * |x - y| ^ α := by
  obtain ⟨B0, hB0, hb0⟩ := bump1_iteratedDeriv_bounded n
  obtain ⟨B1, hB1, hb1⟩ := bump1_iteratedDeriv_lipschitz_bound n
  refine ⟨max B1 (2 * B0), hB1.trans (le_max_left _ _), fun x y => ?_⟩
  by_cases hxy : |x - y| ≤ 1
  · have hp : |x - y| ≤ |x - y| ^ α := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg _) hxy hα.le hα1
    exact (hb1 x y).trans (mul_le_mul (le_max_left _ _) hp (abs_nonneg _)
      (hB1.trans (le_max_left _ _)))
  · have hp : 1 ≤ |x - y| ^ α := Real.one_le_rpow (le_of_not_ge hxy) hα.le
    have hb : |iteratedDeriv n bump1 x - iteratedDeriv n bump1 y| ≤ 2 * B0 := by
      exact (abs_sub _ _).trans (by linarith [hb0 x, hb0 y])
    calc
      _ ≤ 2 * B0 := hb
      _ ≤ max B1 (2 * B0) := le_max_right _ _
      _ ≤ max B1 (2 * B0) * |x - y| ^ α :=
        le_mul_of_one_le_right (hB1.trans (le_max_left _ _)) hp

end CausalSmith.Stat.GlobalTailDesignRobustCate

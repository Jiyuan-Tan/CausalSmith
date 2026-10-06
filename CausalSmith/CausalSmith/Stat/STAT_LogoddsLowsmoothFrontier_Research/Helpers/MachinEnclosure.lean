module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.EngineRoutines
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! # The prescribed finite Machin enclosure

Integration of the finite geometric identity bounds the two arctangent remainders.
Machin's identity and the public truncation count certify the rational pi box. -/
public section
noncomputable section
open MeasureTheory
open Causalean.Mathlib.Analysis.IntervalArithmetic
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Finite geometric cancellation leaves precisely the omitted arctangent term.](goal) Under [the stated assumptions](hyp:x). -/
-- @node: machin_geometric_identity
lemma machin_geometric_identity (N : ℕ) (x : ℝ) :
    (1+x^2) * (∑ j ∈ Finset.range N, (-1 : ℝ)^j*x^(2*j)) =
      1-(-1 : ℝ)^N*x^(2*N) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      simp only [pow_succ, Nat.mul_succ]
      ring

/-- [Integrating the finite geometric polynomial gives the literal rational polynomial. [the stated conclusion](goal) holds. -/
-- @node: arctanPolynomial_integral
lemma arctanPolynomial_integral (N : ℕ) (v : ℚ) :
    (arctanPolynomial N v : ℝ) =
      ∫ x in (0 : ℝ)..(v : ℝ), ∑ j ∈ Finset.range N, (-1 : ℝ)^j*x^(2*j) := by
  rw [intervalIntegral.integral_finsetSum]
  · simp only [arctanPolynomial, Rat.cast_sum, Rat.cast_div, Rat.cast_mul,
      Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast,
      intervalIntegral.integral_const_mul, integral_pow, zero_pow (by omega : 2*_+1 ≠ 0),
      sub_zero, Nat.cast_add, Nat.cast_one, Rat.cast_add, Rat.cast_one, mul_div_assoc]
  · intro j hj
    exact (by fun_prop : Continuous (fun x : ℝ => (-1 : ℝ)^j*x^(2*j))).intervalIntegrable _ _

/-- The integrated geometric remainder is bounded uniformly on a positive argument interval. Under the stated assumptions. [The stated hypotheses](hyp:hv) hold, and [the stated conclusion follows](goal). -/
-- @node: arctanPolynomial_error
lemma arctanPolynomial_error (N : ℕ) (v : ℚ) (hv : 0 ≤ v) :
    |Real.arctan (v : ℝ)-(arctanPolynomial N v : ℝ)| ≤ (v : ℝ)^(2*N+1) := by
  have hvR : (0 : ℝ) ≤ v := by exact_mod_cast hv
  have hgeom (x : ℝ) :
      1/(1+x^2)-(∑ j ∈ Finset.range N, (-1 : ℝ)^j*x^(2*j)) =
        (-1 : ℝ)^N*x^(2*N)/(1+x^2) := by
    have h := machin_geometric_identity N x
    have hp : 1+x^2 ≠ 0 := by positivity
    field_simp
    nlinarith [h]
  have hi : (∫ x in (0 : ℝ)..(v : ℝ),
      1/(1+x^2)-(∑ j ∈ Finset.range N, (-1 : ℝ)^j*x^(2*j))) =
        Real.arctan (v : ℝ)-(arctanPolynomial N v : ℝ) := by
    rw [intervalIntegral.integral_sub, integral_one_div_one_add_sq,
      Real.arctan_zero, sub_zero, ← arctanPolynomial_integral]
    · exact (by
        have hn (x : ℝ) : 1+x^2 ≠ 0 := by positivity
        fun_prop : Continuous (fun x : ℝ => 1/(1+x^2))).intervalIntegrable _ _
    · exact (by fun_prop : Continuous (fun x : ℝ => ∑ j ∈ Finset.range N,
        (-1 : ℝ)^j*x^(2*j))).intervalIntegrable _ _
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (v : ℝ)) (C := (v : ℝ)^(2*N))
    (f := fun x => 1/(1+x^2)-(∑ j ∈ Finset.range N, (-1 : ℝ)^j*x^(2*j)))
    (by
      intro x hx
      rw [Set.uIoc_of_le hvR] at hx
      rw [hgeom, Real.norm_eq_abs, abs_div, abs_mul, abs_pow]
      simp only [abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (by positivity : 0 ≤ 1+x^2)]
      rw [abs_of_nonneg (pow_nonneg hx.1.le _)]
      apply (div_le_iff₀ (by positivity)).mpr
      have hp := pow_le_pow_left₀ hx.1.le hx.2 (2*N)
      nlinarith [sq_nonneg x, pow_nonneg hvR (2*N)])
  rw [hi, Real.norm_eq_abs, sub_zero, abs_of_nonneg hvR] at hb
  simpa only [pow_succ, mul_comm] using hb

/-- The fixed public term count controls the sum of both weighted remainders. [the stated conclusion](goal) holds. -/
-- @node: machin_truncation_bound
lemma machin_truncation_bound (q : ℕ) :
    20*(1/5 : ℝ)^(2*(q+7)+1) ≤ 1/(2 : ℝ)^(q+3) := by
  induction q with
  | zero => norm_num
  | succ q ih =>
      have he : 2*(q+1+7)+1 = (2*(q+7)+1)+2 := by omega
      rw [he, pow_add, show q+1+3 = (q+3)+1 by omega,
        show (2 : ℝ)^((q+3)+1) = 2^(q+3)*2 from pow_succ _ _]
      norm_num only [show (1/5 : ℝ)^2 = 1/25 by norm_num]
      have hp : 0 ≤ (1/5 : ℝ)^(2*(q+7)+1) := by positivity
      have ht : 0 < (2 : ℝ)^(q+3) := by positivity
      rw [div_mul_eq_div_div]
      norm_num only [one_div] at ih ⊢
      nlinarith [inv_pos.mpr ht]

/-- Machin's identity bounds the literal rational approximation at every precision. [the stated conclusion](goal) holds. -/
-- @node: paperPi_approximation
lemma paperPi_approximation (q : ℕ) :
    |Real.pi - ((16*arctanPolynomial (q+7) (1/5)-
      4*arctanPolynomial (q+7) (1/239) : ℚ) : ℝ)| ≤ (rationalError (q+3) : ℝ) := by
  have h5 := arctanPolynomial_error (q+7) (1/5) (by norm_num)
  have h239 := arctanPolynomial_error (q+7) (1/239) (by norm_num)
  have hm := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  have hp : (1/239 : ℝ)^(2*(q+7)+1) ≤ (1/5 : ℝ)^(2*(q+7)+1) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have htriangle := abs_add_le
    (16*(Real.arctan (1/5)-(arctanPolynomial (q+7) (1/5) : ℝ)))
    (-(4*(Real.arctan (1/239)-(arctanPolynomial (q+7) (1/239) : ℝ))))
  simp only [abs_neg, ← sub_eq_add_neg] at htriangle
  norm_num only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 16),
    abs_of_pos (by norm_num : (0 : ℝ) < 4)] at htriangle
  have he : Real.pi - ((16*arctanPolynomial (q+7) (1/5)-
      4*arctanPolynomial (q+7) (1/239) : ℚ) : ℝ) =
      16*(Real.arctan (1/5)-(arctanPolynomial (q+7) (1/5) : ℝ))-
      4*(Real.arctan (1/239)-(arctanPolynomial (q+7) (1/239) : ℝ)) := by
    push_cast
    simp only [one_div] at *
    linarith [hm]
  rw [he]
  have hb := machin_truncation_bound q
  simp only [rationalError, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat]
  push_cast at h5 h239
  linarith

/-- Clipping the certified Machin approximation preserves containment and both excess bounds. [the stated conclusion](goal) holds. -/
-- @node: paperPi_contract
lemma paperPi_contract (q : ℕ) :
    (paperPi q).Contains Real.pi ∧
    3 ≤ (paperPi q).lo ∧ (paperPi q).hi ≤ 4 ∧
    Real.pi-(paperPi q).lo ≤ precisionError q ∧
    (paperPi q).hi-Real.pi ≤ precisionError q := by
  let S : ℚ := 16*arctanPolynomial (q+7) (1/5)-4*arctanPolynomial (q+7) (1/239)
  let e : ℚ := rationalError (q+3)
  have happrox : |Real.pi-(S : ℝ)| ≤ (e : ℝ) := paperPi_approximation q
  obtain ⟨hminus, hplus⟩ := abs_le.mp happrox
  have hlo : ((max 3 (S-e) : ℚ) : ℝ) ≤ Real.pi := by
    push_cast
    exact max_le Real.pi_gt_three.le (by linarith)
  have hhi : Real.pi ≤ ((min 4 (S+e) : ℚ) : ℝ) := by
    push_cast
    exact le_min Real.pi_lt_four.le (by linarith)
  have hord : max 3 (S-e) ≤ min 4 (S+e) := by
    exact_mod_cast hlo.trans hhi
  have herr : 2*(e : ℝ) ≤ precisionError q := by
    change 2*(rationalError (q+3) : ℝ) ≤ precisionError q
    simp only [rationalError, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat,
      precisionError, zpow_neg, zpow_natCast]
    rw [pow_add]
    norm_num
    have hp : 0 < (2 : ℝ)^q := by positivity
    field_simp
    nlinarith
  have hbox : paperPi q = rationalBox (max 3 (S-e)) (min 4 (S+e)) := rfl
  rw [hbox]
  simp only [rationalBox, min_eq_left hord, max_eq_right hord, RatInterval.Contains]
  refine ⟨⟨hlo, hhi⟩, le_max_left _ _, min_le_left _ _, ?_, ?_⟩
  · have hl : ((S-e : ℚ) : ℝ) ≤ ((max 3 (S-e) : ℚ) : ℝ) := by
      exact_mod_cast le_max_right (3 : ℚ) (S-e)
    push_cast at hl ⊢
    linarith
  · have hu : ((min 4 (S+e) : ℚ) : ℝ) ≤ ((S+e : ℚ) : ℝ) := by
      exact_mod_cast min_le_right (4 : ℚ) (S+e)
    push_cast at hu ⊢
    linarith

end CausalSmith.Stat.LogoddsLowsmoothFrontier

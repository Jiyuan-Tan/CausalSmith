module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.CubicBiasMoments

/-! # Sample rate of the exact spatial cubic projection bias

The two terms in roadmap (13) have rates n^(-7/10) and n^(-3/4).
Dyadic rounding and exponent comparison give the stated BC n^(-2/3) bound.
-/

public section

open MeasureTheory
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- Convert both resolution powers in the cubic squared-bias bound, keeping
exactly the computable constant BC from roadmap (13).  Under [the displayed assumptions and inputs](hyp:n,hn,C1,C2,A2,hA2), [the stated conclusion holds](goal). -/
-- @node: cubic_bias_resolution_terms_sample_rate
lemma cubic_bias_resolution_terms_sample_rate (n : ℕ) (hn : threshold ≤ n)
    (C1 C2 A2 : ℝ) (hA2 : 0 ≤ A2) :
    let q : ℝ := 1 / (cubicResolution n : ℝ)
    2 * (C1 * (q ^ holderExponent) ^ 2) ^ 2 * (7 : ℝ) ^ 2 *
        (A2 * (n : ℝ) ^ (-(1 / 5 : ℝ))) +
      2 * (C2 * (q ^ holderExponent) ^ 3) ^ 2 ≤
    2 * (C1 ^ 2 * (7 : ℝ) ^ 2 * A2 * (2 : ℝ) ^ (1 / 2 : ℝ) *
      (5 : ℝ) ^ (1 / 2 : ℝ) + C2 ^ 2 * (2 : ℝ) ^ (3 / 4 : ℝ) *
      (5 : ℝ) ^ (3 / 4 : ℝ)) * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  dsimp only
  let q : ℝ := 1 / (cubicResolution n : ℝ)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (show 1 ≤ n by norm_num [threshold] at hn; omega)
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hn1
  have hp4 : (q ^ holderExponent) ^ (4 : ℕ) = q ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq]
    norm_num [holderExponent]
  have hp6 : (q ^ holderExponent) ^ (6 : ℕ) = q ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq]
    norm_num [holderExponent]
  have hhalf : q ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 5 : ℝ)) ≤
      (2 : ℝ) ^ (1 / 2 : ℝ) * (5 : ℝ) ^ (1 / 2 : ℝ) *
        (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
    calc
      _ ≤ ((2 : ℝ) ^ (1 / 2 : ℝ) * (5 : ℝ) ^ (1 / 2 : ℝ) *
          (n : ℝ) ^ (-(1 / 2 : ℝ))) * (n : ℝ) ^ (-(1 / 5 : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (cubicResolution_inverse_rpow_sample_rate n hn (1 / 2) (by norm_num))
          (Real.rpow_nonneg hnpos.le _)
      _ = (2 : ℝ) ^ (1 / 2 : ℝ) * (5 : ℝ) ^ (1 / 2 : ℝ) *
          (n : ℝ) ^ (-(7 / 10 : ℝ)) := by
        rw [mul_assoc, ← Real.rpow_add hnpos]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)) (by positivity)
  have hthree : q ^ (3 / 4 : ℝ) ≤
      (2 : ℝ) ^ (3 / 4 : ℝ) * (5 : ℝ) ^ (3 / 4 : ℝ) *
        (n : ℝ) ^ (-(2 / 3 : ℝ)) :=
    (cubicResolution_inverse_rpow_sample_rate n hn (3 / 4) (by norm_num)).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)) (by positivity))
  calc
    _ = (2 * C1 ^ 2 * (7 : ℝ) ^ 2 * A2) *
        (q ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 5 : ℝ))) +
        (2 * C2 ^ 2) * q ^ (3 / 4 : ℝ) := by
      change 2 * (C1 * (q ^ holderExponent) ^ 2) ^ 2 * (7 : ℝ) ^ 2 *
        (A2 * (n : ℝ) ^ (-(1 / 5 : ℝ))) +
        2 * (C2 * (q ^ holderExponent) ^ 3) ^ 2 = _
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
      norm_num only at *
      rw [hp4, hp6]
      ring
    _ ≤ (2 * C1 ^ 2 * (7 : ℝ) ^ 2 * A2) *
        ((2 : ℝ) ^ (1 / 2 : ℝ) * (5 : ℝ) ^ (1 / 2 : ℝ) *
          (n : ℝ) ^ (-(2 / 3 : ℝ))) +
        (2 * C2 ^ 2) * ((2 : ℝ) ^ (3 / 4 : ℝ) * (5 : ℝ) ^ (3 / 4 : ℝ) *
          (n : ℝ) ^ (-(2 / 3 : ℝ))) := add_le_add
      (mul_le_mul_of_nonneg_left hhalf (by positivity))
      (mul_le_mul_of_nonneg_left hthree (by positivity))
    _ = _ := by ring

/-- The exact spatial cubic Taylor term minus the exact cubic projection
mean has the sample-size bound (13), with the paper's BC constant.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
-- @node: cubic_spatial_projection_bias_integrated_sq_sample_rate
lemma cubic_spatial_projection_bias_integrated_sq_sample_rate
    (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool) :
    let H := 3 * (1 + C_f) * L
    let M := fourthDerivativeEnvelope c_f C_f
    let A2 := 2 * (1 + C_f + C_f ^ 2) * (5 : ℝ) ^ (1 / 5 : ℝ) +
      (2 : ℝ) ^ (5 / 4 : ℝ) * H ^ 2 * (5 : ℝ) ^ (1 / 5 : ℝ)
    let C1 := (M / 2) * (7 : ℝ) ^ 2 * H ^ 2
    let C2 := (M / 6) * (7 : ℝ) ^ 3 * H ^ 3
    let BC := 2 * (C1 ^ 2 * (7 : ℝ) ^ 2 * A2 * (2 : ℝ) ^ (1 / 2 : ℝ) *
      (5 : ℝ) ^ (1 / 2 : ℝ) + C2 ^ 2 * (2 : ℝ) ^ (3 / 4 : ℝ) *
      (5 : ℝ) ^ (3 / 4 : ℝ))
    (∫ ω, ((∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7, ∫ x in covariateSpace,
        (dPhi3 A (pilot c_f C_f ω x) i j k / 6) *
          (markedDensityVector c_f C_f L P n hP x i - pilot c_f C_f ω x i) *
          (markedDensityVector c_f C_f L P n hP x j - pilot c_f C_f ω x j) *
          (markedDensityVector c_f C_f L P n hP x k - pilot c_f C_f ω x k)) -
        cubicProjectionMean c_f C_f L P n hP ω A) ^ 2 ∂dataLaw P n n) ≤
      BC * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  dsimp only
  have hC : 0 ≤ C_f := le_trans (by norm_num) hP.sourceBounds.2.1.le
  have hA2 : 0 ≤ 2 * (1 + C_f + C_f ^ 2) * (5 : ℝ) ^ (1 / 5 : ℝ) +
      (2 : ℝ) ^ (5 / 4 : ℝ) * (3 * (1 + C_f) * L) ^ 2 *
        (5 : ℝ) ^ (1 / 5 : ℝ) := by positivity
  apply (cubic_spatial_projection_bias_integrated_sq_resolution_bound
    c_f C_f L P n hn hP A).trans
  convert cubic_bias_resolution_terms_sample_rate n hn
    ((fourthDerivativeEnvelope c_f C_f / 2) * (7 : ℝ) ^ 2 *
      (3 * (1 + C_f) * L) ^ 2)
    ((fourthDerivativeEnvelope c_f C_f / 6) * (7 : ℝ) ^ 3 *
      (3 * (1 + C_f) * L) ^ 3) _ hA2 using 1 <;> first | rfl | ring

end CausalSmith.Stat.TransportCaceRoughnuisanceLength

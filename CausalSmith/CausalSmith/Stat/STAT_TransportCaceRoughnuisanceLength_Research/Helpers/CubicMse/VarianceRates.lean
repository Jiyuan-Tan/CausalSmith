module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.CubicResolution
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.CubicVariance
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.LinearVariance
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.ResolutionBounds

/-! # Sample-rate bounds for the exact correction variances

The dyadic resolution bounds convert the conditional variance ladders to
roadmap (17)--(19), with the paper's constants. These estimates apply to the
exact held-out sums and retain their conditional centering.
-/

public section

open MeasureTheory
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- The parametric variance rate is bounded by the target MSE rate.  Under [the displayed assumptions and inputs](hyp:n,hn), [the stated conclusion holds](goal). -/
-- @node: inverse_sampleSize_le_mse_rate
lemma inverse_sampleSize_le_mse_rate (n : ℕ) (hn : threshold ≤ n) :
    (n : ℝ) ^ (-1 : ℝ) ≤ (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast (show 1 ≤ n by norm_num [threshold] at hn; omega)
  · norm_num

/-- The quadratic ladder has rate n⁻²ᐟ³ for the actual dyadic resolution.  Under [the displayed assumptions and inputs](hyp:n,hn), [the stated conclusion holds](goal). -/
-- @node: quadratic_variance_ladder_sample_rate
lemma quadratic_variance_ladder_sample_rate (n : ℕ) (hn : threshold ≤ n) :
    (n : ℝ) ^ (-1 : ℝ) + (quadraticResolution n : ℝ) * (n : ℝ) ^ (-2 : ℝ) ≤
      2 * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by norm_num [threshold] at hn; omega)
  have hK : (quadraticResolution n : ℝ) ≤ (n : ℝ) ^ (4 / 3 : ℝ) :=
    (quadraticResolution_power_bounds n hn).2.trans
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (by
        exact_mod_cast blockSize_le_sampleSize n 0) (by norm_num))
  have hterm : (quadraticResolution n : ℝ) * (n : ℝ) ^ (-2 : ℝ) ≤
      (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
    calc
      _ ≤ (n : ℝ) ^ (4 / 3 : ℝ) * (n : ℝ) ^ (-2 : ℝ) :=
        mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hnpos.le _)
      _ = _ := by rw [← Real.rpow_add hnpos]; norm_num
  linarith [inverse_sampleSize_le_mse_rate n hn]

/-- Both higher cubic ladder terms are at most the parametric rate.  Under [the displayed assumptions and inputs](hyp:n,hn), [the stated conclusion holds](goal). -/
-- @node: cubic_variance_ladder_sample_rate
lemma cubic_variance_ladder_sample_rate (n : ℕ) (hn : threshold ≤ n) :
    (n : ℝ) ^ (-1 : ℝ) + (cubicResolution n : ℝ) * (n : ℝ) ^ (-2 : ℝ) +
      (cubicResolution n : ℝ) ^ 2 * (n : ℝ) ^ (-3 : ℝ) ≤
      3 * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by norm_num [threshold] at hn; omega)
  have hK : (cubicResolution n : ℝ) ≤ n := by
    exact_mod_cast cubicResolution_le_n n hn
  have hterm2 : (cubicResolution n : ℝ) * (n : ℝ) ^ (-2 : ℝ) ≤
      (n : ℝ) ^ (-1 : ℝ) := by
    calc
      _ ≤ (n : ℝ) * (n : ℝ) ^ (-2 : ℝ) :=
        mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hnpos.le _)
      _ = _ := by nth_rw 1 [← Real.rpow_one (n : ℝ)]; rw [← Real.rpow_add hnpos]; norm_num
  have hterm3 : (cubicResolution n : ℝ) ^ 2 * (n : ℝ) ^ (-3 : ℝ) ≤
      (n : ℝ) ^ (-1 : ℝ) := by
    calc
      _ ≤ (n : ℝ) ^ (2 : ℕ) * (n : ℝ) ^ (-3 : ℝ) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hK 2)
          (Real.rpow_nonneg hnpos.le _)
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_add hnpos]; norm_num
  linarith [inverse_sampleSize_le_mse_rate n hn]

/-- Roadmap (17), after converting the exact quadratic resolution to sample size.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
-- @node: quadratic_conditional_variance_sample_rate
lemma quadratic_conditional_variance_sample_rate (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool) :
    ∀ᵐ ω ∂dataLaw P n n,
      condExp (trainingSigma n) (dataLaw P n n)
        (fun ξ : TwoSample n n => (quadraticTerm c_f C_f ξ A -
          condExp (trainingSigma n) (dataLaw P n n)
            (fun ζ : TwoSample n n => quadraticTerm c_f C_f ζ A) ξ) ^ 2) ω ≤
        60 * quadVarianceConstant c_f C_f * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  have hB : 0 ≤ quadVarianceConstant c_f C_f := by
    unfold quadVarianceConstant
    dsimp only
    positivity
  filter_upwards [quadratic_conditional_variance c_f C_f L P n hn hP A] with ω hω
  apply hω.trans
  have hb := mul_le_mul_of_nonneg_left (quadratic_variance_ladder_sample_rate n hn) hB
  have hr : 0 ≤ (n : ℝ) ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  nlinarith

/-- Roadmap (18), after converting the exact cubic resolution to sample size.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
-- @node: cubic_conditional_variance_sample_rate
lemma cubic_conditional_variance_sample_rate (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool) :
    ∀ᵐ ω ∂dataLaw P n n,
      condExp (trainingSigma n) (dataLaw P n n)
        (fun ξ : TwoSample n n => (cubicTerm c_f C_f ξ A -
          condExp (trainingSigma n) (dataLaw P n n)
            (fun ζ : TwoSample n n => cubicTerm c_f C_f ζ A) ξ) ^ 2) ω ≤
        310 * cubicVarianceConstant c_f C_f * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  have hB : 0 ≤ cubicVarianceConstant c_f C_f := by
    unfold cubicVarianceConstant
    dsimp only
    have hC : 0 < C_f := lt_trans (by norm_num) hP.sourceBounds.2.1
    positivity
  filter_upwards [cubic_conditional_variance c_f C_f L P n hn hP A] with ω hω
  apply hω.trans
  have hb := mul_le_mul_of_nonneg_left (cubic_variance_ladder_sample_rate n hn) hB
  have hr : 0 ≤ (n : ℝ) ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  nlinarith

/-- Roadmap (19) expressed at the common target MSE rate.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
-- @node: linear_conditional_variance_sample_rate
lemma linear_conditional_variance_sample_rate (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool) :
    ∀ᵐ ω ∂dataLaw P n n,
      condExp (trainingSigma n) (dataLaw P n n)
        (fun ξ : TwoSample n n => (linearTerm c_f C_f ξ A -
          condExp (trainingSigma n) (dataLaw P n n)
            (fun ζ : TwoSample n n => linearTerm c_f C_f ζ A) ξ) ^ 2) ω ≤
        10 * (7 : ℝ) ^ 2 * (fourthDerivativeEnvelope c_f C_f) ^ 2 *
          (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  filter_upwards [linear_conditional_variance c_f C_f L P n hn hP A] with ω hω
  exact hω.trans (mul_le_mul_of_nonneg_left (inverse_sampleSize_le_mse_rate n hn)
    (by positivity))

end CausalSmith.Stat.TransportCaceRoughnuisanceLength

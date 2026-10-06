module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Defs.CalibrationRegularity
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairCellSmoothness
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairCenterSlope
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairEquationContinuity
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairEquationRegularity
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairEquationSmoothness
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairNumeratorSmoothness
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairOpenNeighbourhood
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairRootExistence
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairRootNearZero
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairRootTaylorBounds
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairTaylorDerivatives
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairZeroAmplitude
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairZeroEffect
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedCellSmoothness
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedOpenNeighbourhood
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedRootSmoothness
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.T_ScalarImplicitFunction
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # T ExactCalibrations

Paper-owned scaffold obligations; proofs are filled in Stage 3. -/
@[expose] public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ContDiff
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The normalized branch has the prescribed value on the zero-effect axis. [the stated conclusion](goal) holds. -/
-- @node: normalizedBranch_zero
lemma normalizedBranch_zero (ξ υ : ℝ) :
    normalizedBranch 0 ξ υ = ξ*(1-ξ)*υ*(1-υ) := by
  norm_num [normalizedBranch, dividedExp]

/-- Multiplication by the effect removes the divided difference without excluding zero. [the stated conclusion](goal) holds. -/
-- @node: covarianceBranch_eq_mul_normalizedBranch
lemma covarianceBranch_eq_mul_normalizedBranch (t ξ υ : ℝ) :
    covarianceBranch t ξ υ = t * normalizedBranch t ξ υ := by
  unfold covarianceBranch normalizedBranch
  rw [← dividedExp_mul t]
  ring

/-- Off zero the normalization is exactly division by the effect. Under the stated assumptions. [The stated hypotheses](hyp:ht) hold, and [the stated conclusion follows](goal). -/
-- @node: normalizedBranch_eq_div
lemma normalizedBranch_eq_div (t ξ υ : ℝ) (ht : t ≠ 0) :
    normalizedBranch t ξ υ = covarianceBranch t ξ υ / t := by
  rw [covarianceBranch_eq_mul_normalizedBranch]
  field_simp

/-- [The table retains its first margin for every covariance. [the stated conclusion](goal) holds. -/
-- @node: tableCell_first_margin
lemma tableCell_first_margin (ξ υ c : ℝ) :
    (∑ y : Bool, tableCell ξ υ c true y) = ξ := by
  simp [tableCell]
  ring

/-- The table retains its second margin for every covariance. [the stated conclusion](goal) holds. -/
-- @node: tableCell_second_margin
lemma tableCell_second_margin (ξ υ c : ℝ) :
    (∑ a : Bool, tableCell ξ υ c a true) = υ := by
  simp [tableCell]
  ring

/-- The four cells sum to one for every covariance. [the stated conclusion](goal) holds. -/
-- @node: tableCell_total
lemma tableCell_total (ξ υ c : ℝ) :
    (∑ a : Bool, ∑ y : Bool, tableCell ξ υ c a y) = 1 := by
  simp [tableCell]
  ring

/-- A root of the normalized mixed equation gives exact singleton covariance matching. Under the stated assumptions. [The stated hypotheses](hyp:hq) hold, and [the stated conclusion follows](goal). -/
-- @node: mixedEquation_covariance_matching
lemma mixedEquation_covariance_matching (η ζ u q : ℝ)
    (hq : mixedEquation η ζ u q = 0) :
    signAverage (fun s => covarianceBranch (32*η*ζ)
      (1/2-η*q*localSignField u s) (1/2+ζ*localSignField u s)) = 2*η*ζ*q := by
  simp only [covarianceBranch_eq_mul_normalizedBranch, signAverage,
    ← Finset.mul_sum]
  unfold mixedEquation signAverage at hq
  linear_combination (2*η*ζ) * hq

/-- [The two independent fair signs have zero averaged field. [the stated conclusion](goal) holds. -/
-- @node: localSignField_mean
lemma localSignField_mean (u : ℝ) : signAverage (localSignField u) = 0 := by
  simp [signAverage, Fintype.sum_prod_type, localSignField, signValue]
  ring

/-- The cosine-sine sign interpolation has unit second moment. [the stated conclusion](goal) holds. -/
-- @node: localSignField_second_moment
lemma localSignField_second_moment (u : ℝ) :
    signAverage (fun s => localSignField u s ^ 2) = 1 := by
  simp [signAverage, Fintype.sum_prod_type, localSignField, signValue]
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi*u/2)]

/-- On the zero-propensity-amplitude axis, the equation is affine in the root. [the stated conclusion](goal) holds. -/
-- @node: mixedEquation_zero_left
lemma mixedEquation_zero_left (ζ u q : ℝ) :
    mixedEquation 0 ζ u q = 1-4*ζ^2-q := by
  unfold mixedEquation
  simp only [mul_zero, zero_mul, sub_zero, normalizedBranch_zero]
  unfold signAverage
  simp [Fintype.sum_prod_type, localSignField, signValue]
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi*u/2)]

/-- The prescribed local selector has the exact zero-axis value for small signed amplitudes. Under the stated assumptions. [The stated hypotheses](hyp:hζ) hold, and [the stated conclusion follows](goal). -/
-- @node: mixedRoot_zero_left
lemma mixedRoot_zero_left (ζ u : ℝ) (hζ : |ζ| ≤ 1 / 8) :
    mixedRoot 0 ζ u = 1-4*ζ^2 := by
  have hsq : ζ^2 ≤ (1/8 : ℝ)^2 := by
    nlinarith [sq_abs ζ, abs_nonneg ζ]
  have hex : ∃ q : ℝ, q ∈ Set.Ioo (3 / 4) (5 / 4) ∧ mixedEquation 0 ζ u q = 0 := by
    refine ⟨1-4*ζ^2, ⟨?_, ?_⟩, ?_⟩
    · nlinarith [sq_nonneg ζ]
    · nlinarith [sq_nonneg ζ]
    · rw [mixedEquation_zero_left]
      ring
  unfold mixedRoot
  rw [dif_pos hex]
  have hroot := (Classical.choose_spec hex).2
  rw [mixedEquation_zero_left] at hroot
  linarith

/-- [At either cell endpoint the finite sign average gives the same root equation. [the stated conclusion](goal) holds. -/
-- @node: mixedEquation_endpoints
lemma mixedEquation_endpoints (η ζ q : ℝ) :
    mixedEquation η ζ 0 q = mixedEquation η ζ 1 q := by
  simp [mixedEquation, signAverage, Fintype.sum_prod_type, localSignField,
    signValue, Real.cos_pi_div_two, Real.sin_pi_div_two]
  ring

/-- The literal selectors agree at cell endpoints because their equations agree. [the stated conclusion](goal) holds. -/
-- @node: mixedRoot_endpoints
lemma mixedRoot_endpoints (η ζ : ℝ) : mixedRoot η ζ 0 = mixedRoot η ζ 1 := by
  have he : mixedEquation η ζ 0 = mixedEquation η ζ 1 :=
    funext (mixedEquation_endpoints η ζ)
  unfold mixedRoot
  rw [he]

/-- An existing bracket root makes the totalized selector a genuine bracket root. [the stated conclusion](goal) holds. Under [the stated assumptions](hyp:h). -/
-- @node: mixedRoot_spec
lemma mixedRoot_spec (η ζ u : ℝ)
    (h : ∃ q : ℝ, q ∈ Set.Ioo (3 / 4) (5 / 4) ∧ mixedEquation η ζ u q = 0) :
    mixedRoot η ζ u ∈ Set.Ioo (3 / 4) (5 / 4) ∧
      mixedEquation η ζ u (mixedRoot η ζ u) = 0 := by
  unfold mixedRoot
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- On the other zero-amplitude axis the mixed equation reduces to the stated quadratic. [the stated conclusion](goal) holds. -/
-- @node: mixedEquation_zero_right
lemma mixedEquation_zero_right (η u q : ℝ) :
    mixedEquation η 0 u q = 1-4*η^2*q^2-q := by
  unfold mixedEquation
  simp only [mul_zero, zero_mul, add_zero, normalizedBranch_zero]
  unfold signAverage
  simp [Fintype.sum_prod_type, localSignField, signValue]
  linear_combination (-4*η^2*q^2) * Real.sin_sq_add_cos_sq (Real.pi*u/2)

/-- The zero-prognosis-amplitude quadratic has a bracket root by the intermediate value theorem. Under the stated assumptions. [The stated hypotheses](hyp:hη) hold, and [the stated conclusion follows](goal). -/
-- @node: mixedEquation_zero_right_exists
lemma mixedEquation_zero_right_exists (η u : ℝ) (hη : |η| ≤ 1 / 8) :
    ∃ q : ℝ, q ∈ Set.Ioo (3 / 4) (5 / 4) ∧ mixedEquation η 0 u q = 0 := by
  have hsq : η^2 ≤ (1/8 : ℝ)^2 := by
    nlinarith [sq_abs η, abs_nonneg η]
  have hcont : ContinuousOn (fun q : ℝ => 1-4*η^2*q^2-q) (Set.Icc (7/8) 1) := by
    fun_prop
  obtain ⟨q, hq, heq⟩ := intermediate_value_Icc' (by norm_num : (7/8 : ℝ) ≤ 1) hcont
    (show (0 : ℝ) ∈ Set.Icc (1-4*η^2*1^2-1) (1-4*η^2*(7/8)^2-7/8) by
      constructor <;> nlinarith [sq_nonneg η])
  refine ⟨q, ⟨?_, ?_⟩, ?_⟩
  · linarith [hq.1]
  · linarith [hq.2]
  · rw [mixedEquation_zero_right]
    exact heq

/-- [The actual selected root satisfies the zero-axis quadratic, including signed amplitudes.](goal) Under [the stated assumptions](hyp:hη). -/
-- @node: mixedRoot_zero_right
lemma mixedRoot_zero_right (η u : ℝ) (hη : |η| ≤ 1 / 8) :
    mixedRoot η 0 u+4*η^2*(mixedRoot η 0 u)^2 = 1 := by
  have heq := (mixedRoot_spec η 0 u (mixedEquation_zero_right_exists η u hη)).2
  rw [mixedEquation_zero_right] at heq
  linarith

/-- [Small effects have a uniformly small exponential increment.](goal) Under [the stated assumptions](hyp:ht). -/
-- @node: calibration_exp_increment_bound
lemma calibration_exp_increment_bound (t : ℝ) (ht : |t| ≤ 1 / 8) :
    |Real.exp t - 1| ≤ 1 / 4 := by
  have h := Real.abs_exp_sub_one_le (show |t| ≤ 1 by linarith)
  linarith

/-- [The rationalized branch has a positive denominator and small covariance.](goal) Under [the stated assumptions](hyp:ht,hξ,hυ). -/
-- @node: covarianceBranch_local_bounds
lemma covarianceBranch_local_bounds (t ξ υ : ℝ)
    (ht : |t| ≤ 1 / 8) (hξ : |ξ - 1 / 2| ≤ 1 / 8) (hυ : |υ - 1 / 2| ≤ 1 / 8) :
    let d := Real.exp t - 1
    let v := ξ * (1 - ξ) * υ * (1 - υ)
    let L := 1 + d * (ξ * (1 - υ) + (1 - ξ) * υ)
    3 / 4 ≤ L ∧ 0 ≤ L ^ 2 - 4 * d ^ 2 * v ∧ |covarianceBranch t ξ υ| ≤ 1 / 24 := by
  dsimp only
  obtain ⟨hdlo, hdhi⟩ := abs_le.mp (calibration_exp_increment_bound t ht)
  obtain ⟨hξlo, hξhi⟩ := abs_le.mp hξ
  obtain ⟨hυlo, hυhi⟩ := abs_le.mp hυ
  let d := Real.exp t - 1
  let v := ξ * (1 - ξ) * υ * (1 - υ)
  let L := 1 + d * (ξ * (1 - υ) + (1 - ξ) * υ)
  have hx : 0 ≤ ξ * (1 - ξ) := mul_nonneg (by linarith) (by linarith)
  have hy : 0 ≤ υ * (1 - υ) := mul_nonneg (by linarith) (by linarith)
  have hxhi : ξ * (1 - ξ) ≤ 1 / 4 := by nlinarith [sq_nonneg (ξ - 1 / 2)]
  have hyhi : υ * (1 - υ) ≤ 1 / 4 := by nlinarith [sq_nonneg (υ - 1 / 2)]
  have hv : 0 ≤ v := by dsimp [v]; exact mul_nonneg (mul_nonneg hx (by linarith)) (by linarith)
  have hvhi : v ≤ 1 / 16 := by
    dsimp [v]
    nlinarith [mul_nonneg (sub_nonneg.mpr hxhi) hy]
  have hs : 0 ≤ ξ * (1 - υ) + (1 - ξ) * υ := by
    exact add_nonneg (mul_nonneg (by linarith) (by linarith))
      (mul_nonneg (by linarith) (by linarith))
  have hshi : ξ * (1 - υ) + (1 - ξ) * υ ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ ξ by linarith) (show 0 ≤ υ by linarith),
      mul_nonneg (show 0 ≤ 1 - ξ by linarith) (show 0 ≤ 1 - υ by linarith)]
  have hL : 3 / 4 ≤ L := by
    dsimp [L, d]
    nlinarith [mul_nonneg (show 0 ≤ Real.exp t - 1 + 1 / 4 by linarith) hs]
  have hd2 : d ^ 2 ≤ 1 / 16 := by dsimp [d]; nlinarith
  have hrad : 0 ≤ L ^ 2 - 4 * d ^ 2 * v := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hd2) hv, sq_nonneg (L - 3 / 4)]
  have hden : 3 / 4 ≤ L + Real.sqrt (L ^ 2 - 4 * d ^ 2 * v) :=
    le_trans hL (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  have hc : |covarianceBranch t ξ υ| * (L + Real.sqrt (L ^ 2 - 4 * d ^ 2 * v)) = 2 * |d| * v := by
    unfold covarianceBranch
    change |2 * d * v / (L + Real.sqrt (L ^ 2 - 4 * d ^ 2 * v))| * _ = _
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      abs_of_nonneg hv, abs_of_pos (by linarith : 0 < L + Real.sqrt (L ^ 2 - 4 * d ^ 2 * v))]
    exact div_mul_cancel₀ _ (by linarith)
  refine ⟨hL, hrad, ?_⟩
  have hdabs : |d| ≤ 1 / 4 := calibration_exp_increment_bound t ht
  nlinarith [mul_nonneg (sub_nonneg.mpr hdabs) hv,
    mul_nonneg (abs_nonneg (covarianceBranch t ξ υ)) (sub_nonneg.mpr hden)]

/-- [Every centered product is separated from zero on the chosen margin neighbourhood.](goal) Under [the stated assumptions](hyp:x,hx,hy). -/
-- @node: calibration_product_lower
lemma calibration_product_lower (x y : ℝ) (hx : 3 / 8 ≤ x) (hy : 3 / 8 ≤ y) :
    (9 / 64 : ℝ) ≤ x * y := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]

/-- [All four actual cells are positive throughout a fixed absolute neighbourhood.](goal) Under [the stated assumptions](hyp:ht,hξ,hυ). -/
-- @node: covarianceBranch_table_positive
lemma covarianceBranch_table_positive (t ξ υ : ℝ)
    (ht : |t| ≤ 1 / 8) (hξ : |ξ - 1 / 2| ≤ 1 / 8) (hυ : |υ - 1 / 2| ≤ 1 / 8) :
    ∀ a y, 0 < tableCell ξ υ (covarianceBranch t ξ υ) a y := by
  have hc := (covarianceBranch_local_bounds t ξ υ ht hξ hυ).2.2
  obtain ⟨hclo, hchi⟩ := abs_le.mp hc
  obtain ⟨hxlo, hxhi⟩ := abs_le.mp hξ
  obtain ⟨hylo, hyhi⟩ := abs_le.mp hυ
  have h1 := calibration_product_lower ξ υ (by linarith) (by linarith)
  have h2 := calibration_product_lower ξ (1 - υ) (by linarith) (by linarith)
  have h3 := calibration_product_lower (1 - ξ) υ (by linarith) (by linarith)
  have h4 := calibration_product_lower (1 - ξ) (1 - υ) (by linarith) (by linarith)
  intro a y
  cases a <;> cases y <;> simp only [tableCell, Bool.false_eq_true, ↓reduceIte] <;> linarith

/-- [Rationalizing the small quadratic root preserves its defining polynomial at zero.](goal) Under [the stated assumptions](hyp:hrad). Under [the stated assumptions](hyp:hden). -/
-- @node: calibration_rationalized_quadratic
lemma calibration_rationalized_quadratic (d v L : ℝ)
    (hrad : 0 ≤ L ^ 2 - 4 * d ^ 2 * v) (hden : L + Real.sqrt (L ^ 2 - 4 * d ^ 2 * v) ≠ 0) :
    d * (2 * d * v / (L + Real.sqrt (L ^ 2 - 4 * d ^ 2 * v))) ^ 2 - 
      L * (2 * d * v / (L + Real.sqrt (L ^ 2 - 4 * d ^ 2 * v))) + d * v = 0 := by
  have hs := Real.sq_sqrt hrad
  generalize Real.sqrt (L ^ 2 - 4 * d ^ 2 * v) = s at * 
  field_simp [hden]
  linear_combination (d * v) * hs

/-- [The covariance branch solves the odds-ratio quadratic on the absolute neighbourhood.](goal) Under [the stated assumptions](hyp:ht,hξ,hυ). -/
-- @node: covarianceBranch_quadratic
lemma covarianceBranch_quadratic (t ξ υ : ℝ)
    (ht : |t| ≤ 1 / 8) (hξ : |ξ - 1 / 2| ≤ 1 / 8) (hυ : |υ - 1 / 2| ≤ 1 / 8) :
    let d := Real.exp t - 1
    let c := covarianceBranch t ξ υ
    d * c ^ 2 - (1 + d * (ξ * (1 - υ) + (1 - ξ) * υ)) * c + d * (ξ * (1 - ξ) * υ * (1 - υ)) = 0 := by
  have hb := covarianceBranch_local_bounds t ξ υ ht hξ hυ
  unfold covarianceBranch
  dsimp only
  apply calibration_rationalized_quadratic _ _ _ hb.2.1
  have hs := Real.sqrt_nonneg
    ((1 + (Real.exp t - 1) * (ξ * (1 - υ) + (1 - ξ) * υ)) ^ 2 - 
      4 * (Real.exp t - 1) ^ 2 * (ξ * (1 - ξ) * υ * (1 - υ)))
  linarith [hb.1]

/-- [The determinant identity turns the solved quadratic into the exact odds ratio.](goal) Under [the stated assumptions](hyp:ht,hξ,hυ). -/
-- @node: covarianceBranch_odds_ratio
lemma covarianceBranch_odds_ratio (t ξ υ : ℝ)
    (ht : |t| ≤ 1 / 8) (hξ : |ξ - 1 / 2| ≤ 1 / 8) (hυ : |υ - 1 / 2| ≤ 1 / 8) :
    let c := covarianceBranch t ξ υ
    tableCell ξ υ c true true * tableCell ξ υ c false false / 
      (tableCell ξ υ c true false * tableCell ξ υ c false true) = Real.exp t := by
  dsimp only
  have hp := covarianceBranch_table_positive t ξ υ ht hξ hυ
  apply (div_eq_iff (ne_of_gt (mul_pos (hp true false) (hp false true)))).mpr
  have hq := covarianceBranch_quadratic t ξ υ ht hξ hυ
  dsimp only at hq
  simp only [tableCell, Bool.false_eq_true, ↓reduceIte]
  linear_combination - hq

/-- [Reversing the effect scales its smooth exponential divided difference. [the stated conclusion](goal) holds. -/
-- @node: dividedExp_neg
lemma dividedExp_neg (t : ℝ) : dividedExp (-t) = dividedExp t / Real.exp t := by
  by_cases ht : t = 0
  · subst t
    simp
  have hpos := Real.exp_pos t
  have hp := dividedExp_mul t
  have hn := dividedExp_mul (-t)
  rw [Real.exp_neg] at hn
  field_simp at hn ⊢
  apply mul_left_cancel₀ ht
  linear_combination -hn -hp

/-- Scaling the quadratic coefficients by a positive factor preserves the normalized branch. Under the stated assumptions. [The stated hypotheses](hyp:hE) hold, and [the stated conclusion follows](goal). -/
-- @node: calibration_normalized_scale
lemma calibration_normalized_scale (D d v L E : ℝ) (hE : 0 < E) :
    2*(D/E)*v/(L/E+Real.sqrt ((L/E)^2-4*(-d/E)^2*v)) =
      2*D*v/(L+Real.sqrt (L^2-4*d^2*v)) := by
  have hrad : (L/E)^2-4*(-d/E)^2*v = (L^2-4*d^2*v)/E^2 := by ring
  rw [hrad, Real.sqrt_div' _ (sq_nonneg E), Real.sqrt_sq hE.le, ← add_div]
  by_cases hden : L+Real.sqrt (L^2-4*d^2*v) = 0
  · simp [hden]
  · field_simp

/-- Complementing the first binary margin reverses the effect in the normalized branch. [the stated conclusion](goal) holds. -/
-- @node: normalizedBranch_complement_left
lemma normalizedBranch_complement_left (t ξ υ : ℝ) :
    normalizedBranch (-t) (1-ξ) υ = normalizedBranch t ξ υ := by
  have hE := Real.exp_pos t
  have hv : (1-ξ)*(1-(1-ξ))*υ*(1-υ) = ξ*(1-ξ)*υ*(1-υ) := by ring
  have hL : 1+(Real.exp (-t)-1)*((1-ξ)*(1-υ)+(1-(1-ξ))*υ) =
      (1+(Real.exp t-1)*(ξ*(1-υ)+(1-ξ)*υ))/Real.exp t := by
    rw [Real.exp_neg]
    field_simp
    ring
  have hd : Real.exp (-t)-1 = -(Real.exp t-1)/Real.exp t := by
    rw [Real.exp_neg]
    field_simp
    ring
  unfold normalizedBranch
  dsimp only
  rw [hv, hL, hd, dividedExp_neg]
  exact calibration_normalized_scale _ _ _ _ _ hE

/-- Exchanging the two margins preserves the normalized covariance branch. [the stated conclusion](goal) holds. -/
-- @node: normalizedBranch_swap
lemma normalizedBranch_swap (t ξ υ : ℝ) :
    normalizedBranch t ξ υ = normalizedBranch t υ ξ := by
  unfold normalizedBranch
  have hv : ξ*(1-ξ)*υ*(1-υ) = υ*(1-υ)*ξ*(1-ξ) := by ring
  have hL : ξ*(1-υ)+(1-ξ)*υ = υ*(1-ξ)+(1-υ)*ξ := by ring
  dsimp only
  rw [hv, hL]

/-- Complementing the second binary margin also reverses the effect. [the stated conclusion](goal) holds. -/
-- @node: normalizedBranch_complement_right
lemma normalizedBranch_complement_right (t ξ υ : ℝ) :
    normalizedBranch (-t) ξ (1-υ) = normalizedBranch t ξ υ := by
  rw [normalizedBranch_swap (-t), normalizedBranch_complement_left, normalizedBranch_swap t]

/-- The mixed root equation is even in its propensity amplitude. [the stated conclusion](goal) holds. -/
-- @node: mixedEquation_even_left
lemma mixedEquation_even_left (η ζ u q : ℝ) :
    mixedEquation (-η) ζ u q = mixedEquation η ζ u q := by
  unfold mixedEquation
  congr 2
  apply congrArg signAverage
  funext s
  have ht : 32*(-η)*ζ = -(32*η*ζ) := by ring
  have hx : 1/2-(-η)*q*localSignField u s = 1-(1/2-η*q*localSignField u s) := by ring
  rw [ht, hx, normalizedBranch_complement_left]

/-- The mixed root equation is even in its prognosis amplitude. [the stated conclusion](goal) holds. -/
-- @node: mixedEquation_even_right
lemma mixedEquation_even_right (η ζ u q : ℝ) :
    mixedEquation η (-ζ) u q = mixedEquation η ζ u q := by
  unfold mixedEquation
  congr 2
  apply congrArg signAverage
  funext s
  have ht : 32*η*(-ζ) = -(32*η*ζ) := by ring
  have hy : 1/2+(-ζ)*localSignField u s = 1-(1/2+ζ*localSignField u s) := by ring
  rw [ht, hy, normalizedBranch_complement_right]

/-- Identical equations give identical literal mixed-root selectors. [the stated conclusion](goal) holds. -/
-- @node: mixedRoot_even_left
lemma mixedRoot_even_left (η ζ u : ℝ) : mixedRoot (-η) ζ u = mixedRoot η ζ u := by
  have he : mixedEquation (-η) ζ u = mixedEquation η ζ u :=
    funext (mixedEquation_even_left η ζ u)
  unfold mixedRoot
  rw [he]

/-- The literal mixed-root selector is even in the prognosis amplitude. [the stated conclusion](goal) holds. -/
-- @node: mixedRoot_even_right
lemma mixedRoot_even_right (η ζ u : ℝ) : mixedRoot η (-ζ) u = mixedRoot η ζ u := by
  have he : mixedEquation η (-ζ) u = mixedEquation η ζ u :=
    funext (mixedEquation_even_right η ζ u)
  unfold mixedRoot
  rw [he]

/-- Existing uniform uniqueness, confinement, and pointwise smoothness supply
one common signed branch certificate with explicit ambient open neighborhoods,
including the fair equation's removable extension on the full centered bracket. [the documented result](goal) -/
-- @node: calibration_branch_neighbourhood_exists
lemma calibration_branch_neighbourhood_exists :
    ∃ ε : ℝ, 0 < ε ∧ CalibrationBranchNeighbourhood ε := by
  obtain ⟨Rmix, U, hRmix, hU, hmU, hmZero, hmSmooth, hmCells⟩ :=
    mixed_calibration_open_neighbourhood
  obtain ⟨Rfair₀, V, hRfair₀, hV, hfV₀, hfZero, hfSmooth, hfCells⟩ :=
    fair_calibration_open_neighbourhood
  let Rfair := min Rfair₀ (1/100)
  have hRfair : 0 < Rfair := lt_min hRfair₀ (by norm_num)
  have hFairSmall : Rfair ≤ 1/100 := min_le_right _ _
  have hfV : fairParameterRegion Rfair ⊆ V := by
    intro v hv
    exact hfV₀ ⟨hv.1, hv.2.1.trans (min_le_left _ _), hv.2.2⟩
  let W : Set (Fin 4 → ℝ) := interior {w | ContDiffAt ℝ ∞
    (fun z : Fin 4 → ℝ => fairEquation (z 0) (z 1) (z 2) (z 3)) w}
  have hWCore :
      {w : Fin 4 → ℝ | w 0 ∈ Set.Icc (0 : ℝ) (1/4) ∧ |w 1| ≤ Rfair ∧
        w 2 ∈ Set.Ioo ((2/5 : ℝ)-1/20) (2/5+1/20) ∧
        w 3 ∈ Set.Icc (0 : ℝ) 1} ⊆ W := by
    intro w hw
    have hTaylor : w ∈ fairTaylorParameterRegion :=
      (fairTaylorParameterRegion_mem w).mpr ⟨hw.1, hw.2.1.trans hFairSmall,
        ⟨by linarith [hw.2.2.1.1], by linarith [hw.2.2.1.2]⟩, hw.2.2.2⟩
    -- Compactness of both Taylor integration coordinates gives one neighborhood
    -- on which every finite smoothness order holds simultaneously.
    exact mem_interior_iff_mem_nhds.mpr
      (fairEquation_eventually_contDiffAt w hTaylor)
  have hWSmooth : ContDiffOn ℝ ∞ (fun w : Fin 4 → ℝ =>
      fairEquation (w 0) (w 1) (w 2) (w 3)) W := by
    intro w hw
    have hAt : ContDiffAt ℝ ∞ (fun z : Fin 4 → ℝ =>
        fairEquation (z 0) (z 1) (z 2) (z 3)) w := interior_subset hw
    exact hAt.contDiffWithinAt
  have hDiv : ∀ t δ ξ u : ℝ, t ∈ Set.Icc (0 : ℝ) (1/4) → |δ| ≤ Rfair →
      ξ ∈ Set.Ioo ((2/5 : ℝ)-1/20) (2/5+1/20) → u ∈ Set.Icc (0 : ℝ) 1 →
      t*δ ≠ 0 → fairEquation t δ ξ u = fairNumerator t δ ξ u/(t*δ^2) := by
    intro t δ ξ u ht hδ hξ _hu hne
    exact fairEquation_eq_div t δ ξ u ht (hδ.trans hFairSmall)
      ⟨by linarith [hξ.1], by linarith [hξ.2]⟩ hne
  let ε := min Rmix Rfair / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεmix : ε < Rmix := by
    have h := min_le_left Rmix Rfair
    dsimp [ε]
    linarith
  have hεfair : ε < Rfair := by
    have h := min_le_right Rmix Rfair
    dsimp [ε]
    linarith
  exact ⟨ε, hε, Rmix, Rfair, 1/20, U, V, hRmix, hεmix, hRfair, hεfair,
    by norm_num, by norm_num, hU, hV, hmU, hfV, hmZero, hfZero, hmSmooth, hfSmooth,
    hmCells, hfCells, W, isOpen_interior, hWCore, hWSmooth, hDiv⟩

-- @node: lem:exact-calibrations
/-- Exact signed singleton matching, unique selected branches on fixed brackets,
open smooth neighborhoods, smooth zero-axis extensions, and the effect separation. [the documented result](goal) -/
lemma exact_calibrations : ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧
  CalibrationSmooth ε ∧ (CalibrationDerivativeBounds ε ∧ CalibrationBranchNeighbourhood ε) ∧
  (∀ t ξ υ : ℝ, |t| ≤ ε → |ξ-1/2| ≤ ε → |υ-1/2| ≤ ε →
    let c := covarianceBranch t ξ υ
    (∀ a y, 0 < tableCell ξ υ c a y) ∧
    (∑ y : Bool, tableCell ξ υ c true y) = ξ ∧
    (∑ a : Bool, tableCell ξ υ c a true) = υ ∧
    (∑ a : Bool, ∑ y : Bool, tableCell ξ υ c a y) = 1 ∧
    tableCell ξ υ c true true*tableCell ξ υ c false false /
      (tableCell ξ υ c true false*tableCell ξ υ c false true) = Real.exp t ∧
    (t ≠ 0 → normalizedBranch t ξ υ = c/t) ∧
    normalizedBranch 0 ξ υ = ξ*(1-ξ)*υ*(1-υ)) ∧
  (∀ η ζ u : ℝ, |η| ≤ ε → |ζ| ≤ ε → u ∈ Set.Icc (0 : ℝ) 1 →
    let q := mixedRoot η ζ u
    3/4 < q ∧ q < 5/4 ∧
    mixedEquation η ζ u q = 0 ∧
    mixedRoot η ζ 0 = mixedRoot η ζ 1 ∧
    signAverage (fun s => covarianceBranch (32*η*ζ)
      (1/2-η*q*localSignField u s) (1/2+ζ*localSignField u s)) = 2*η*ζ*q ∧
    mixedRoot (-η) ζ u = q ∧ mixedRoot η (-ζ) u = q ∧
    mixedRoot 0 ζ u = 1-4*ζ^2 ∧
    mixedRoot η 0 u+4*η^2*(mixedRoot η 0 u)^2 = 1) ∧
  (∀ t δ u : ℝ, t ∈ Set.Icc (0 : ℝ) (1/4) → |δ| ≤ ε → u ∈ Set.Icc (0 : ℝ) 1 →
    let p := fairRoot t δ u
    fairRoot t δ 0 = 2/5 ∧ fairRoot t δ 1 = 2/5 ∧
    fairRoot t 0 u = 2/5 ∧ fairRoot 0 δ u = 2/5 ∧
    fairRoot t (-δ) u = p ∧ fairEquation t δ p u = 0 ∧
    (t*δ ≠ 0 → fairEquation t δ p u = fairNumerator t δ p u/(t*δ^2)) ∧
    signAverage (fun s => riskShift t (p+δ*localSignField u s)) = riskShift (comparatorEffect t δ) p ∧
    |p-2/5|+|deriv (fairRoot t δ) u| ≤ M*δ^2 ∧
    3*t*δ^2 ≤ t-comparatorEffect t δ ∧ t-comparatorEffect t δ ≤ 6*t*δ^2 ∧
    t/2 ≤ comparatorEffect t δ ∧ comparatorEffect t δ ≤ t) := by
  obtain ⟨εroot, hεroot, hroots⟩ := mixedEquation_uniform_existsUnique
  obtain ⟨εmix, hεmix, hMixAt, hMixBounds⟩ := mixedRoot_uniform_smooth_derivative_bounds
  obtain ⟨εcell, hεcell, hCellAt, hCellBounds⟩ := localMixedCell_uniform_smooth_derivative_bounds
  obtain ⟨εfair, hεfair, hfairSmall, hfairExists⟩ := fairEquation_uniform_exists
  obtain ⟨εpre, hεpre, hfairSmallPre, hεmixPre, hεcellPre, hFairAtPre⟩ :
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/100 ∧ ε ≤ εmix ∧ ε ≤ εcell ∧
        ∀ v ∈ fairParameterRegion ε,
          ContDiffAt ℝ ∞ (fun w : Fin 3 → ℝ => fairRoot (w 0) (w 1) (w 2)) v := by
    obtain ⟨εsmooth,hεsmooth,hsmallSmooth,hSmoothFair⟩ := fairRoot_uniform_contDiffAt
    let ε := min εsmooth (min εmix εcell)
    have heSmooth : ε ≤ εsmooth := min_le_left _ _
    have heMix : ε ≤ εmix := (min_le_right _ _).trans (min_le_left _ _)
    have heCell : ε ≤ εcell := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨ε,lt_min hεsmooth (lt_min hεmix hεcell),
      heSmooth.trans hsmallSmooth,heMix,heCell,?_⟩
    intro v hv
    exact hSmoothFair v ⟨hv.1,hv.2.1.trans heSmooth,hv.2.2⟩
  let ε₀ := min εpre εfair
  have hε₀ : 0 < ε₀ := lt_min hεpre hεfair
  have hfairSmall₀ : ε₀ ≤ 1/100 := (min_le_left _ _).trans hfairSmallPre
  have hεmix₀ : ε₀ ≤ εmix := (min_le_left _ _).trans hεmixPre
  have hεcell₀ : ε₀ ≤ εcell := (min_le_left _ _).trans hεcellPre
  have hFairAt₀ : ∀ v ∈ fairParameterRegion ε₀,
      ContDiffAt ℝ ∞ (fun w : Fin 3 → ℝ => fairRoot (w 0) (w 1) (w 2)) v := by
    intro v hv
    exact hFairAtPre v ⟨hv.1,hv.2.1.trans (min_le_left _ _),hv.2.2⟩
  have hFairRoots₀ : ∀ t δ u : ℝ,
      t ∈ Set.Icc (0 : ℝ) (1/4) → |δ| ≤ ε₀ → u ∈ Set.Icc (0 : ℝ) 1 →
      fairRoot t δ 0 = 2/5 ∧ fairRoot t 0 u = 2/5 ∧ fairRoot 0 δ u = 2/5 ∧
      (∃ p ∈ Set.Ioo (3/10 : ℝ) (1/2), fairEquation t δ p u = 0) := by
    intro t δ u ht hδ hu
    exact ⟨fairRoot_endpoint_center t δ 0 ht (hδ.trans hfairSmall₀) (Or.inl rfl),
      fairRoot_zero_amplitude t u ht hu,
      fairRoot_zero_effect δ u (hδ.trans hfairSmall₀) hu,
      hfairExists t δ u ht (hδ.trans (min_le_right _ _)) hu⟩
  obtain ⟨M, hM, hFairQuadratic⟩ := fairRoot_quadratic_bound_of_smooth ε₀ hε₀.le hFairAt₀
    (fun t u ht hu => (hFairRoots₀ t 0 u ht (by simpa using hε₀.le) hu).2.1)
  have hsmall₀ : ε₀ ≤ 1/8 := hfairSmall₀.trans (by norm_num)
  have hFairSmooth₀ : ContDiffOn ℝ ∞
      (fun v : Fin 3 → ℝ => fairRoot (v 0) (v 1) (v 2)) (fairParameterRegion ε₀) :=
    fun v hv => (hFairAt₀ v hv).contDiffWithinAt
  obtain ⟨hFairCells₀, hFairBounds⟩ :=
    localFairCell_smooth_derivative_bounds_of_root ε₀ hfairSmall₀ hFairAt₀
  have hCellRegion : mixedParameterRegion ε₀ ⊆ mixedParameterRegion εcell := by
    rintro v ⟨hη, hζ, hu⟩
    exact ⟨hη.trans hεcell₀, hζ.trans hεcell₀, hu⟩
  have hMixCells₀ : ∀ b s a y,
      ContDiffOn ℝ ⊤ (localMixedCell b s a y) (mixedParameterRegion ε₀) := by
    intro b s a y v hv
    exact (hCellAt v (hCellRegion hv) b s a y).contDiffWithinAt
  have hRemainingBounds : ∀ m : ℕ, ∃ B : ℝ, 0 < B ∧
      (∀ v ∈ mixedParameterRegion ε₀, ∀ b s a y,
        ‖iteratedFDeriv ℝ m (localMixedCell b s a y) v‖ ≤ B) ∧
      (∀ v ∈ fairParameterRegion ε₀,
        ‖iteratedFDeriv ℝ m (fun w : Fin 3 → ℝ => fairRoot (w 0) (w 1) (w 2)) v‖ ≤ B ∧
        ∀ b s a y, ‖iteratedFDeriv ℝ m (localFairCell b s a y) v‖ ≤ B) := by
    intro m
    obtain ⟨Bm, hBm, hm⟩ := hCellBounds m
    obtain ⟨Bf, hBf, hf⟩ := hFairBounds m
    refine ⟨max Bm Bf, lt_of_lt_of_le hBm (le_max_left _ _), ?_, ?_⟩
    · intro v hv b s a y
      exact (hm v (hCellRegion hv) b s a y).trans (le_max_left _ _)
    · intro v hv
      exact ⟨(hf v hv).1.trans (le_max_right _ _),
        fun b s a y => ((hf v hv).2 b s a y).trans (le_max_right _ _)⟩
  have hSmooth₀ : CalibrationSmooth ε₀ := by
    refine ⟨?_, hFairSmooth₀,
      fun b s a y => (hMixCells₀ b s a y).of_le le_top,
      fun b s a y => hFairCells₀ b s a y⟩
    intro v hv
    exact (hMixAt v (hv.1.trans hεmix₀) (hv.2.1.trans hεmix₀) hv.2.2).of_le le_top |>.contDiffWithinAt
  have hDerivatives₀ : CalibrationDerivativeBounds ε₀ := by
    intro m
    obtain ⟨Bq, hBq, hq⟩ := hMixBounds m
    obtain ⟨Bc, hBc, hmc, hfc⟩ := hRemainingBounds m
    refine ⟨max Bq Bc, lt_of_lt_of_le hBq (le_max_left _ _), ?_, ?_⟩
    · intro v hv
      refine ⟨(hq v (hv.1.trans hεmix₀) (hv.2.1.trans hεmix₀) hv.2.2).trans
        (le_max_left _ _), ?_⟩
      intro b s a y
      exact (hmc v hv b s a y).trans (le_max_right _ _)
    · intro v hv
      exact ⟨(hfc v hv).1.trans (le_max_right _ _),
        fun b s a y => ((hfc v hv).2 b s a y).trans (le_max_right _ _)⟩
  obtain ⟨εbranch, hεbranch, hBranchNeighbourhood⟩ := calibration_branch_neighbourhood_exists
  let ε := min ε₀ (min εroot (min (1/100) εbranch))
  have hε : 0 < ε := lt_min hε₀ (lt_min hεroot (lt_min (by norm_num) hεbranch))
  have hsmall : ε ≤ 1/8 := (min_le_left _ _).trans hsmall₀
  have hMixed : mixedParameterRegion ε ⊆ mixedParameterRegion ε₀ := by
    rintro v ⟨hη, hζ, hu⟩
    exact ⟨hη.trans (min_le_left _ _), hζ.trans (min_le_left _ _), hu⟩
  have hFair : fairParameterRegion ε ⊆ fairParameterRegion ε₀ := by
    rintro v ⟨ht, hδ, hu⟩
    exact ⟨ht, hδ.trans (min_le_left _ _), hu⟩
  have hSmooth : CalibrationSmooth ε :=
    ⟨hSmooth₀.1.mono hMixed, hSmooth₀.2.1.mono hFair,
      fun b s a y => (hSmooth₀.2.2.1 b s a y).mono hMixed,
      fun b s a y => (hSmooth₀.2.2.2 b s a y).mono hFair⟩
  have hDerivatives : CalibrationDerivativeBounds ε := by
    intro m
    obtain ⟨B, hB, hMix, hF⟩ := hDerivatives₀ m
    exact ⟨B, hB, fun v hv => hMix v (hMixed hv), fun v hv => hF v (hFair hv)⟩
  have hBranchNeighbourhoodε : CalibrationBranchNeighbourhood ε := by
    obtain ⟨εmix, εfair, b, U, V, hm, hem, hf, hef, hb, hbsmall, hRest⟩ := hBranchNeighbourhood
    have he : ε ≤ εbranch :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    exact ⟨εmix, εfair, b, U, V, hm, he.trans_lt hem, hf, he.trans_lt hef, hb, hbsmall, hRest⟩
  refine ⟨ε, M, hε, hM, hSmooth, ⟨hDerivatives, hBranchNeighbourhoodε⟩, ?_, ?_, ?_⟩
  · intro t ξ υ ht hξ hυ
    dsimp only
    refine ⟨?_, tableCell_first_margin _ _ _, tableCell_second_margin _ _ _,
      tableCell_total _ _ _, ?_, normalizedBranch_eq_div _ _ _, normalizedBranch_zero _ _⟩
    · exact covarianceBranch_table_positive t ξ υ (ht.trans hsmall)
        (hξ.trans hsmall) (hυ.trans hsmall)
    · exact covarianceBranch_odds_ratio t ξ υ (ht.trans hsmall)
        (hξ.trans hsmall) (hυ.trans hsmall)
  · intro η ζ u hη hζ hu
    dsimp only
    have hExists : ∃ q : ℝ, q ∈ Set.Ioo (3 / 4) (5 / 4) ∧ mixedEquation η ζ u q = 0 := by
      exact (hroots η ζ u ((hη.trans (min_le_right _ _)).trans (min_le_left _ _))
        ((hζ.trans (min_le_right _ _)).trans (min_le_left _ _)) hu).exists
    obtain ⟨hBracket, hEquation⟩ := mixedRoot_spec η ζ u hExists
    refine ⟨hBracket.1, hBracket.2, hEquation, mixedRoot_endpoints η ζ,
      mixedEquation_covariance_matching η ζ u _ hEquation, ?_, ?_,
      mixedRoot_zero_left ζ u (hζ.trans hsmall),
      mixedRoot_zero_right η u (hη.trans hsmall)⟩
    · exact mixedRoot_even_left η ζ u
    · exact mixedRoot_even_right η ζ u
  · intro t δ u ht hδ hu
    dsimp only
    have hδsmall : |δ| ≤ 1/100 :=
      (hδ.trans (min_le_right _ _)).trans ((min_le_right _ _).trans (min_le_left _ _))
    obtain ⟨hLower, hUpper⟩ := comparatorEffect_gap_bounds t δ ht hδsmall
    obtain ⟨hHalf, hLe⟩ := comparatorEffect_range_bounds t δ ht hδsmall
    obtain ⟨h0, hδ0, ht0, hExists⟩ :=
      hFairRoots₀ t δ u ht (hδ.trans (min_le_left _ _)) hu
    have hBound := hFairQuadratic t δ u ht (hδ.trans (min_le_left _ _)) hu
    have hBracket := fairRoot_mem_bracket t δ u
    have hDiv : t*δ ≠ 0 → fairEquation t δ (fairRoot t δ u) u =
        fairNumerator t δ (fairRoot t δ u) u/(t*δ^2) :=
      fun hne => fairEquation_eq_div t δ (fairRoot t δ u) u ht hδsmall
        ⟨hBracket.1.le, hBracket.2.le⟩ hne
    have hEq : fairEquation t δ (fairRoot t δ u) u = 0 := by
      by_cases hδzero : δ = 0
      · subst δ
        exact (fairRoot_zero_amplitude_spec t u ht).2
      by_cases huEnd : u = 0 ∨ u = 1
      · exact (fairRoot_endpoint_spec t δ u ht hδsmall huEnd).2
      · exact (fairRoot_spec t δ u hExists).2
    have hMatch := fair_matching_of_equation t δ (fairRoot t δ u) u ht hδsmall
      ⟨hBracket.1.le, hBracket.2.le⟩ hEq
    exact ⟨h0, (fairRoot_endpoints t δ).symm.trans h0, hδ0, ht0, fairRoot_even t δ u, hEq, hDiv, hMatch,
      hBound, hLower, hUpper, hHalf, hLe⟩
end CausalSmith.Stat.LogoddsLowsmoothFrontier

module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.ExactBiasAssembly
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.ResolutionBounds

/-! # Summed quadratic projection bias

The exact cell cancellation identity gives the deterministic quadratic bias
bound. Dyadic rounding and the block-size lower bound give its squared
sample-size rate, with the constant BQ in roadmap (11).
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- The quadratic Taylor projection error, summed over all marked coordinates
and cells with the pilot frozen at each cell midpoint.  For [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hP,A), [the stated object is defined](goal). -/
-- @node: quadraticCellProjectionBias
noncomputable def quadraticCellProjectionBias (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hP : ModelClass c_f C_f L P n)
    (ω : TwoSample n n) (A : Bool) : ℝ :=
  ∑ i : Fin 7, ∑ j : Fin 7, ∑ l : Fin K,
    ∫ x in cell K l,
      (dPhi2 A (pilot c_f C_f ω (midpoint K l)) i j / 2) *
        ((markedDensityVector c_f C_f L P n hP x i -
            pilot c_f C_f ω (midpoint K l) i) *
          (markedDensityVector c_f C_f L P n hP x j -
            pilot c_f C_f ω (midpoint K l) j) -
          (cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l -
            pilot c_f C_f ω (midpoint K l) i) *
          (cellAverage (fun y => markedDensityVector c_f C_f L P n hP y j) K l -
            pilot c_f C_f ω (midpoint K l) j))

/-- Exact cancellation of the single-residual terms bounds the total quadratic
projection bias by half the coordinate count squared times the derivative
and squared Hölder envelopes.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hn,hP,hK,A), [the stated conclusion holds](goal). -/
-- @node: quadraticCellProjectionBias_abs_le
lemma quadraticCellProjectionBias_abs_le (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K)
    (ω : TwoSample n n) (A : Bool) :
    |quadraticCellProjectionBias c_f C_f L P n K hP ω A| ≤
      ((7 : ℝ) ^ 2 / 2) * fourthDerivativeEnvelope c_f C_f *
        (3 * (1 + C_f) * L * (1 / (K : ℝ)) ^ holderExponent) ^ 2 := by
  classical
  let B := 3 * (1 + C_f) * L * (1 / (K : ℝ)) ^ holderExponent
  let M := fourthDerivativeEnvelope c_f C_f
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hM : 0 ≤ M := by
    have hc := hP.sourceBounds.1.1
    dsimp [M, fourthDerivativeEnvelope]
    positivity
  have hc (i j : Fin 7) (l : Fin K) :
      |dPhi2 A (pilot c_f C_f ω (midpoint K l)) i j / 2| ≤ M / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right
      (dPhi2_abs_le c_f C_f hP.sourceBounds.1 hP.sourceBounds.2.1 A _
        (pilot_mem_clippingRectangle c_f C_f L P n hn hP ω (midpoint K l)) i j)
      (by norm_num)
  unfold quadraticCellProjectionBias
  calc
    _ ≤ ∑ i : Fin 7, ∑ j : Fin 7, ∑ l : Fin K, M / 2 * B ^ 2 / (K : ℝ) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro l hl
      exact (markedDensity_quadratic_cell_projection_abs_le
        c_f C_f L P n K hP hK l i j
        (pilot c_f C_f ω (midpoint K l) i)
        (pilot c_f C_f ω (midpoint K l) j)
        (dPhi2 A (pilot c_f C_f ω (midpoint K l)) i j / 2)).trans
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hc i j l) (sq_nonneg B)) hKr.le)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp [M, B]
      field_simp

/-- The inverse quadratic resolution has the explicit rate required by the
quadratic projection bias, including the factor lost to dyadic rounding.  Under [the displayed assumptions and inputs](hyp:n,hn), [the stated conclusion holds](goal). -/
-- @node: quadraticResolution_inverse_half_rate
lemma quadraticResolution_inverse_half_rate (n : ℕ) (hn : threshold ≤ n) :
    (1 / (quadraticResolution n : ℝ)) ^ (1 / 2 : ℝ) ≤
      (2 : ℝ) ^ (1 / 2 : ℝ) * (5 : ℝ) ^ (2 / 3 : ℝ) *
        (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by norm_num [threshold] at hn; omega)
  have hm := Real.rpow_le_rpow (div_pos hnpos (by norm_num)).le
    (block_size_lower n hn 0) (by norm_num : (0 : ℝ) ≤ 4 / 3)
  have hlow := (quadraticResolution_power_bounds n hn).1
  have hl : ((n : ℝ) / 5) ^ (4 / 3 : ℝ) / 2 ≤
      (quadraticResolution n : ℝ) := (div_le_div_of_nonneg_right hm (by norm_num)).trans hlow
  have hbase : 0 < ((n : ℝ) / 5) ^ (4 / 3 : ℝ) / 2 := by positivity
  have h := Real.rpow_le_rpow_of_nonpos hbase hl (by norm_num : -(1 / 2 : ℝ) ≤ 0)
  calc
    _ = (quadraticResolution n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [Real.div_rpow (by norm_num) (by positivity), Real.one_rpow,
        Real.rpow_neg (by positivity)]
      simp only [one_div]
    _ ≤ (((n : ℝ) / 5) ^ (4 / 3 : ℝ) / 2) ^ (-(1 / 2 : ℝ)) := h
    _ = _ := by
      rw [Real.div_rpow (by positivity) (by norm_num),
        ← Real.rpow_mul (by positivity)]
      norm_num
      rw [Real.div_rpow hnpos.le (by norm_num),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 5),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp

/-- The squared exact cellwise quadratic projection bias obeys roadmap (11)
with the computable constant used in the MSE envelope.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
-- @node: quadraticCellProjectionBias_sq_sample_rate
lemma quadraticCellProjectionBias_sq_sample_rate (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (ω : TwoSample n n) (A : Bool) :
    (quadraticCellProjectionBias c_f C_f L P n (quadraticResolution n) hP ω A) ^ 2 ≤
      (7 : ℝ) ^ 4 * (fourthDerivativeEnvelope c_f C_f) ^ 2 *
        (3 * (1 + C_f) * L) ^ 4 * (2 : ℝ) ^ (1 / 2 : ℝ) *
        (5 : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  have hK : 0 < quadraticResolution n := by
    unfold quadraticResolution dyadicResolution
    split_ifs <;> positivity
  let H := 3 * (1 + C_f) * L
  let M := fourthDerivativeEnvelope c_f C_f
  let q : ℝ := 1 / (quadraticResolution n : ℝ)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hM : 0 ≤ M := by
    have hc := hP.sourceBounds.1.1
    dsimp [M, fourthDerivativeEnvelope]
    positivity
  have hH : 0 ≤ H := by
    have hC := hP.sourceBounds.2.1
    have hL := hP.sourceHolder.1
    dsimp [H]
    positivity
  have habs := quadraticCellProjectionBias_abs_le c_f C_f L P n
    (quadraticResolution n) hn hP hK ω A
  have hs := pow_le_pow_left₀ (abs_nonneg _) habs 2
  rw [sq_abs] at hs
  have hp : (q ^ holderExponent) ^ (4 : ℕ) = q ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq]
    norm_num [holderExponent]
  have heq : (((7 : ℝ) ^ 2 / 2) * M * (H * q ^ holderExponent) ^ 2) ^ 2 =
      ((7 : ℝ) ^ 4 * M ^ 2 * H ^ 4 / 4) * q ^ (1 / 2 : ℝ) := by
    calc
      _ = ((7 : ℝ) ^ 4 * M ^ 2 * H ^ 4 / 4) *
          (q ^ holderExponent) ^ (4 : ℕ) := by ring
      _ = _ := by rw [hp]
  change _ ≤ (((7 : ℝ) ^ 2 / 2) * M * (H * q ^ holderExponent) ^ 2) ^ 2 at hs
  rw [heq] at hs
  have hr := quadraticResolution_inverse_half_rate n hn
  change q ^ (1 / 2 : ℝ) ≤ _ at hr
  calc
    _ ≤ ((7 : ℝ) ^ 4 * M ^ 2 * H ^ 4 / 4) * q ^ (1 / 2 : ℝ) := hs
    _ ≤ ((7 : ℝ) ^ 4 * M ^ 2 * H ^ 4 / 4) *
        ((2 : ℝ) ^ (1 / 2 : ℝ) * (5 : ℝ) ^ (2 / 3 : ℝ) *
          (n : ℝ) ^ (-(2 / 3 : ℝ))) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ ≤ _ := by
      change _ ≤ (7 : ℝ) ^ 4 * M ^ 2 * H ^ 4 *
        (2 : ℝ) ^ (1 / 2 : ℝ) * (5 : ℝ) ^ (2 / 3 : ℝ) *
          (n : ℝ) ^ (-(2 / 3 : ℝ))
      have ht : 0 ≤ (7 : ℝ) ^ 4 * M ^ 2 * H ^ 4 *
        (2 : ℝ) ^ (1 / 2 : ℝ) * (5 : ℝ) ^ (2 / 3 : ℝ) *
          (n : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
      nlinarith

/-- The summed cell bias is exactly the midpoint-frozen quadratic Taylor
integral minus the projection polynomial that is the statistic's conditional
mean. This identity keeps the exact coefficient and all seven coordinates.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP,A), [the stated conclusion holds](goal). -/
-- @node: quadraticCellProjectionBias_eq_sub_projectionMean
lemma quadraticCellProjectionBias_eq_sub_projectionMean (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hP : ModelClass c_f C_f L P n)
    (ω : TwoSample n n) (A : Bool) :
    quadraticCellProjectionBias c_f C_f L P n (quadraticResolution n) hP ω A =
      (∑ i : Fin 7, ∑ j : Fin 7, ∑ l : Fin (quadraticResolution n),
        ∫ x in cell (quadraticResolution n) l,
          (dPhi2 A (pilot c_f C_f ω (midpoint (quadraticResolution n) l)) i j / 2) *
            (markedDensityVector c_f C_f L P n hP x i -
              pilot c_f C_f ω (midpoint (quadraticResolution n) l) i) *
            (markedDensityVector c_f C_f L P n hP x j -
              pilot c_f C_f ω (midpoint (quadraticResolution n) l) j)) -
        quadraticProjectionMean c_f C_f L P n hP ω A := by
  classical
  let K := quadraticResolution n
  have hK : 0 < K := by
    dsimp [K]
    unfold quadraticResolution dyadicResolution
    split_ifs <;> positivity
  have hcell (i j : Fin 7) (l : Fin K) (ti tj c : ℝ) :
      (∫ x in cell K l, c *
        ((markedDensityVector c_f C_f L P n hP x i - ti) *
          (markedDensityVector c_f C_f L P n hP x j - tj) -
          (cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l - ti) *
          (cellAverage (fun y => markedDensityVector c_f C_f L P n hP y j) K l - tj))) =
      (∫ x in cell K l, c *
        (markedDensityVector c_f C_f L P n hP x i - ti) *
        (markedDensityVector c_f C_f L P n hP x j - tj)) -
      (K : ℝ)⁻¹ * (c *
        (cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l - ti) *
        (cellAverage (fun y => markedDensityVector c_f C_f L P n hP y j) K l - tj)) := by
    have hi := markedDensityVector_continuousOn c_f C_f L P n hP i
    have hj := markedDensityVector_continuousOn c_f C_f L P n hP j
    have hint : IntegrableOn (fun x => c *
        (markedDensityVector c_f C_f L P n hP x i - ti) *
        (markedDensityVector c_f C_f L P n hP x j - tj)) (cell K l) :=
      (show ContinuousOn _ covariateSpace by fun_prop).integrableOn_Icc.mono_set
        (cell_subset_covariateSpace hK l)
    have hfinite : volume (cell K l) ≠ ⊤ := by
      rw [volume_cell hK l]
      exact ENNReal.ofReal_ne_top
    conv_lhs => arg 2; ext x; rw [mul_sub, ← mul_assoc, ← mul_assoc]
    rw [integral_sub hint (integrableOn_const hfinite), setIntegral_const,
      Measure.real, volume_cell hK l, ENNReal.toReal_ofReal (by positivity)]
    simp only [smul_eq_mul, one_div]
  dsimp only [K] at hcell
  rw [quadraticProjectionMean_eq]
  unfold quadraticCellProjectionBias
  dsimp only
  simp_rw [hcell, Finset.sum_sub_distrib, ← Finset.mul_sum]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  ring

/-- The deterministic quadratic bias bound also holds after averaging over
training data, without any extra regularity premise.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
-- @node: quadraticCellProjectionBias_integrated_sq_sample_rate
lemma quadraticCellProjectionBias_integrated_sq_sample_rate (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool) :
    (∫ ω, (quadraticCellProjectionBias c_f C_f L P n (quadraticResolution n) hP ω A) ^ 2
      ∂dataLaw P n n) ≤
      (7 : ℝ) ^ 4 * (fourthDerivativeEnvelope c_f C_f) ^ 2 *
        (3 * (1 + C_f) * L) ^ 4 * (2 : ℝ) ^ (1 / 2 : ℝ) *
        (5 : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  let : IsProbabilityMeasure (sourceObsLaw P) :=
    sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  let : IsProbabilityMeasure (targetXLaw P) :=
    targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  let : IsProbabilityMeasure (dataLaw P n n) := by
    rw [dataLaw_eq_source_target_pi c_f C_f L P n hP]
    infer_instance
  calc
    _ ≤ ∫ _ω : TwoSample n n,
        (7 : ℝ) ^ 4 * (fourthDerivativeEnvelope c_f C_f) ^ 2 *
          (3 * (1 + C_f) * L) ^ 4 * (2 : ℝ) ^ (1 / 2 : ℝ) *
          (5 : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (-(2 / 3 : ℝ)) ∂dataLaw P n n := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun ω => sq_nonneg _) (integrable_const _)
      exact Filter.Eventually.of_forall fun ω =>
        quadraticCellProjectionBias_sq_sample_rate c_f C_f L P n hn hP ω A
    _ = _ := by simp

end CausalSmith.Stat.TransportCaceRoughnuisanceLength

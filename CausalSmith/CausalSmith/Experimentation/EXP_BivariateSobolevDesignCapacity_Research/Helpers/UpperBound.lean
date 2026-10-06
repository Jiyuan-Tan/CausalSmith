module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.PublishedClass
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionTransfer
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.SpectralCounting
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.SpectralRisk
public import Mathlib.Analysis.Real.Pi.Bounds

/-! # Spectral upper-bound proof subsystem

The single design is fair and outcome independent. The scalar spectral estimate
converts its frequencywise minimum bound into the simultaneous fractional rate;
the Fourier-row assembly and both design branches have proved risk bounds.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ The spectral construction is an admissible design for every sample size and dimension.](goal) -/
-- @node: piStar_designClass
lemma piStar_designClass (n d : ℕ) : DesignClass n d (piStar n d) := by
  refine ⟨Filter.Eventually.of_forall (piStar_pointwise_fair n d), ?_⟩
  exact outcomeIndependent_of_covariate_kernel (piStar n d)

/-- A truncated linear weight is bounded by every fractional power through exponent one. Under [the stated conditions](hyp:hx,hs,hs1), [the asserted mathematical result follows](goal). -/
-- @node: spectral_min_one_le_rpow
lemma spectral_min_one_le_rpow {x s : ℝ} (hx : 0 ≤ x) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    min 1 x ≤ x ^ s := by
  by_cases hx1 : x ≤ 1
  · rw [min_eq_right hx1]
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge' hx hx1 hs hs1)
  · rw [min_eq_left (le_of_not_ge hx1)]
    exact Real.one_le_rpow (le_of_not_ge hx1) hs

/-- [ The frequencywise minimum is dominated by the pooled Sobolev weight times the
minimum rate, including the endpoint exponent one.](goal) Under [the stated conditions](hyp:hr,hu,huq,hq,hs,hs1). -/
-- @node: spectral_min_rate_weight
lemma spectral_min_rate_weight {r u q s : ℝ} (hr : 0 ≤ r) (hu : 0 ≤ u)
    (huq : u ≤ q) (hq : 1 ≤ q) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    min 1 (r * u) ≤ min 1 (r ^ s) * q ^ s := by
  have hqpow : 1 ≤ q ^ s := Real.one_le_rpow hq hs
  have hfrac : min 1 (r * u) ≤ r ^ s * q ^ s := by
    calc
      min 1 (r * u) ≤ (r * u) ^ s :=
        spectral_min_one_le_rpow (mul_nonneg hr hu) hs hs1
      _ = r ^ s * u ^ s := Real.mul_rpow hr hu
      _ ≤ r ^ s * q ^ s :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hu huq hs) (Real.rpow_nonneg hr s)
  by_cases hrpow : r ^ s ≤ 1
  · simpa only [min_eq_right hrpow] using hfrac
  · rw [min_eq_left (le_of_not_ge hrpow), one_mul]
    exact (min_le_left _ _).trans hqpow

/-- Odd feature rows are the normalized real parts of the indexed characters. [The asserted mathematical result follows](goal). -/
-- @node: features_odd_eq_re
lemma features_odd_eq_re (d j : ℕ) (y : Torus d) :
    features d (2 * j + 1) y = Real.sqrt 2 * (ek (featureFrequency d j) y).re := by
  have hsub : 2 * j + 1 - 1 = 2 * j := by omega
  have hdiv : 2 * j / 2 = j := by omega
  have hmod : 2 * j % 2 = 0 := by omega
  simp only [features, hsub, hdiv, hmod, ite_true]

/-- [ Even feature rows are the normalized imaginary parts of the same indexed characters.](goal) -/
-- @node: features_even_eq_im
lemma features_even_eq_im (d j : ℕ) (y : Torus d) :
    features d (2 * j + 2) y = Real.sqrt 2 * (ek (featureFrequency d j) y).im := by
  have hsub : 2 * j + 2 - 1 = 2 * j + 1 := by omega
  have hdiv : (2 * j + 1) / 2 = j := by omega
  have hmod : (2 * j + 1) % 2 = 1 := by omega
  simp only [features, hsub, hdiv, hmod, Nat.one_ne_zero, if_false]

/-- [ The squared character imbalance is exactly half the sum of its two real-row squares,
for every deterministic sample and every real coefficient vector.](goal) -/
-- @node: character_imbalance_eq_real_rows
lemma character_imbalance_eq_real_rows (n d j : ℕ) (w : Fin n → Torus d)
    (a : Fin n → ℝ) :
    ‖∑ i, (a i : ℂ) * ek (featureFrequency d j) (w i)‖ ^ 2 =
      ((∑ i, a i * features d (2 * j + 1) (w i)) ^ 2 +
       (∑ i, a i * features d (2 * j + 2) (w i)) ^ 2) / 2 := by
  let z : ℂ := ∑ i, (a i : ℂ) * ek (featureFrequency d j) (w i)
  have hre : ∑ i, a i * features d (2 * j + 1) (w i) = Real.sqrt 2 * z.re := by
    simp only [features_odd_eq_re, z, Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have him : ∑ i, a i * features d (2 * j + 2) (w i) = Real.sqrt 2 * z.im := by
    simp only [features_even_eq_im, z, Complex.im_sum, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hre, him]
  change ‖z‖ ^ 2 = _
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [hsqrt]

/-- The scalar rate bound applies to the precise angular Sobolev normalization. Under [the stated conditions](hyp:hr,hu,hs,hs1), [the asserted mathematical result follows](goal). -/
-- @node: spectral_min_rate_angular
lemma spectral_min_rate_angular {r u s : ℝ} (hr : 0 ≤ r) (hu : 0 ≤ u)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    min 1 (r * u) ≤ min 1 (r ^ s) * (1 + Real.pi ^ 2 * u) ^ s := by
  have hpi : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  apply spectral_min_rate_weight hr hu _ _ hs hs1
  · nlinarith [mul_nonneg (sub_nonneg.mpr hpi) hu]
  · nlinarith [mul_nonneg (sq_nonneg Real.pi) hu]

/-- [ The exact pooled budget controls the entire truncated spectral sum at the
minimum rate, without a frequency-scale sum or logarithmic loss.](goal) Under [the stated conditions](hyp:hd,hs,hs1,hm). -/
-- @node: sobolev_truncated_spectral_sum_le_scale
lemma sobolev_truncated_spectral_sum_le_scale
    (n d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1)
    (m : CenteredL2Fn d) (hm : SobolevClass d s m) :
    (∑' k : Fin d → ℤ,
      if 1 ≤ (frequencySupport k).card ∧ (frequencySupport k).card ≤ 2 then
        ENNReal.ofReal (‖Fhat m.val k‖ ^ 2 *
          min 1 (((pairCount d : ℝ) / n) * frequencyComplexity k))
      else 0) ≤ ENNReal.ofReal (aScale n d s) := by
  classical
  have hr : 0 ≤ (pairCount d : ℝ) / n := by positivity
  have ha : 0 ≤ aScale n d s :=
    le_min zero_le_one (Real.rpow_nonneg hr s)
  have hpoint (k : Fin d → ℤ) :
      (if 1 ≤ (frequencySupport k).card ∧ (frequencySupport k).card ≤ 2 then
        ENNReal.ofReal (‖Fhat m.val k‖ ^ 2 *
          min 1 (((pairCount d : ℝ) / n) * frequencyComplexity k)) else 0) ≤
      ENNReal.ofReal (aScale n d s) *
        (if 1 ≤ (frequencySupport k).card ∧ (frequencySupport k).card ≤ 2 then
          ENNReal.ofReal ((1 + Real.pi ^ 2 * frequencyComplexity k) ^ s *
            ‖Fhat m.val k‖ ^ 2) else 0) := by
    by_cases hk : 1 ≤ (frequencySupport k).card ∧ (frequencySupport k).card ≤ 2
    · rw [if_pos hk, if_pos hk, ← ENNReal.ofReal_mul ha]
      apply ENNReal.ofReal_le_ofReal
      have hu : 0 ≤ frequencyComplexity k := by
        unfold frequencyComplexity frequencySq
        positivity
      have hscalar := spectral_min_rate_angular hr hu hs.le hs1
      have hmul := mul_le_mul_of_nonneg_left hscalar (sq_nonneg ‖Fhat m.val k‖)
      simpa only [aScale, mul_comm, mul_left_comm, mul_assoc] using hmul
    · simp only [if_neg hk, mul_zero, le_refl]
  calc
    _ ≤ ∑' k : Fin d → ℤ, ENNReal.ofReal (aScale n d s) *
        (if 1 ≤ (frequencySupport k).card ∧ (frequencySupport k).card ≤ 2 then
          ENNReal.ofReal ((1 + Real.pi ^ 2 * frequencyComplexity k) ^ s *
            ‖Fhat m.val k‖ ^ 2) else 0) := ENNReal.tsum_le_tsum hpoint
    _ = ENNReal.ofReal (aScale n d s) * reflectedBudget s m.val :=
      ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (aScale n d s) * 1 := by
      gcongr
      exact (exact_reflection_budget.2 d s hd hs hs1 m hm).2.2.1
    _ = ENNReal.ofReal (aScale n d s) := mul_one _

/-- Every terminal spectral sign has a finite second moment under the rounding seeds. [The asserted mathematical result follows](goal). -/
-- @node: spectral_rounding_sign_memLp
lemma spectral_rounding_sign_memLp (n d : ℕ) (w : Fin n → Torus d) (i : Fin n) :
    MeasureTheory.MemLp (fun seeds =>
      sgn (orderedBoundaryRounding n (spectralRows w) seeds i)) 2 (roundingSeedLaw n) := by
  have : MeasureTheory.IsFiniteMeasure (roundingSeedLaw n) := by
    unfold roundingSeedLaw cubeMeasure
    infer_instance
  have hm : Measurable (fun seeds => orderedBoundaryRounding n (spectralRows w) seeds) :=
    (orderedBoundaryRounding_measurable n).comp (measurable_const.prodMk measurable_id)
  have hs : Measurable (fun seeds =>
      sgn (orderedBoundaryRounding n (spectralRows w) seeds i)) := by
    fun_prop
  apply MeasureTheory.MemLp.of_bound hs.aestronglyMeasurable 1
  filter_upwards [] with seeds
  cases orderedBoundaryRounding n (spectralRows w) seeds i <;> norm_num [sgn]

/-- [ The square of any deterministic test row is integrable under the actual spectral rounding.](goal) -/
-- @node: spectral_rounding_row_sq_integrable
lemma spectral_rounding_row_sq_integrable (n d : ℕ) (w : Fin n → Torus d)
    (a : Fin n → ℝ) :
    MeasureTheory.Integrable (fun seeds =>
      (∑ i, a i * sgn (orderedBoundaryRounding n (spectralRows w) seeds i)) ^ 2)
      (roundingSeedLaw n) := by
  have h : MeasureTheory.MemLp (fun seeds =>
      ∑ i, a i * sgn (orderedBoundaryRounding n (spectralRows w) seeds i))
      2 (roundingSeedLaw n) :=
    MeasureTheory.memLp_finsetSum _ (fun i _ =>
      (spectral_rounding_sign_memLp n d w i).const_mul (a i))
  exact h.integrable_sq

/-- The proved ordered-rounding theorem controls each actual spectral test row,
including rows beyond the supplied prefix. Under [the stated conditions](hyp:hh), [the asserted mathematical result follows](goal). -/
-- @node: spectral_rounding_row_second_moment
lemma spectral_rounding_row_second_moment (n d h : ℕ) (w : Fin n → Torus d)
    (hh : 1 ≤ h) :
    (∫ seeds, (∑ i, features d h (w i) *
      sgn (orderedBoundaryRounding n (spectralRows w) seeds i)) ^ 2
      ∂roundingSeedLaw n) ≤ 64 * (min h n : ℕ) := by
  have hb := (ordered_prefix_rounding n (fun h i => features d h (w i))
    (Real.sqrt 2) (fun h i _ => features_abs_le d h (w i))).2.2.2 h hh
  have hp : rowPrefix (n := n) (fun h i => features d h (w i)) = spectralRows w := rfl
  rw [hp] at hb
  simpa only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    show (32 : ℝ) * 2 = 64 by norm_num] using hb

/-- A character inherits the average of its two real-row moment bounds. [The asserted mathematical result follows](goal). -/
-- @node: spectral_rounding_character_second_moment
lemma spectral_rounding_character_second_moment (n d j : ℕ) (w : Fin n → Torus d) :
    (∫ seeds, ‖∑ i, (sgn (orderedBoundaryRounding n (spectralRows w) seeds i) : ℂ) *
      ek (featureFrequency d j) (w i)‖ ^ 2 ∂roundingSeedLaw n) ≤
      64 * (min (2 * j + 2) n : ℕ) := by
  have hodd := spectral_rounding_row_second_moment n d (2 * j + 1) w (by omega)
  have heven := spectral_rounding_row_second_moment n d (2 * j + 2) w (by omega)
  have hi₁ := spectral_rounding_row_sq_integrable n d w
    (fun i => features d (2 * j + 1) (w i))
  have hi₂ := spectral_rounding_row_sq_integrable n d w
    (fun i => features d (2 * j + 2) (w i))
  have heq : (∫ seeds, ‖∑ i,
      (sgn (orderedBoundaryRounding n (spectralRows w) seeds i) : ℂ) *
        ek (featureFrequency d j) (w i)‖ ^ 2 ∂roundingSeedLaw n) =
      ((∫ seeds, (∑ i, features d (2 * j + 1) (w i) *
        sgn (orderedBoundaryRounding n (spectralRows w) seeds i)) ^ 2 ∂roundingSeedLaw n) +
       (∫ seeds, (∑ i, features d (2 * j + 2) (w i) *
        sgn (orderedBoundaryRounding n (spectralRows w) seeds i)) ^ 2 ∂roundingSeedLaw n)) / 2 := by
    calc
      _ = ∫ seeds,
          ((∑ i, features d (2 * j + 1) (w i) *
            sgn (orderedBoundaryRounding n (spectralRows w) seeds i)) ^ 2 +
           (∑ i, features d (2 * j + 2) (w i) *
            sgn (orderedBoundaryRounding n (spectralRows w) seeds i)) ^ 2) / 2
          ∂roundingSeedLaw n := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with seeds
        simpa only [mul_comm] using character_imbalance_eq_real_rows n d j w
          (fun i => sgn (orderedBoundaryRounding n (spectralRows w) seeds i))
      _ = _ := by integral_linearity
  rw [heq]
  have hmin : ((min (2 * j + 1) n : ℕ) : ℝ) ≤ (min (2 * j + 2) n : ℕ) := by
    exact_mod_cast min_le_min_right n (by omega : 2 * j + 1 ≤ 2 * j + 2)
  linarith

/-- [ Real signs make the imbalances at opposite frequencies complex conjugates,
so their squared moduli coincide pointwise.](goal) -/
-- @node: character_imbalance_neg_eq
lemma character_imbalance_neg_eq (n d : ℕ) (k : Fin d → ℤ)
    (w : Fin n → Torus d) (a : Fin n → ℝ) :
    ‖∑ i, (a i : ℂ) * ek (-k) (w i)‖ ^ 2 =
      ‖∑ i, (a i : ℂ) * ek k (w i)‖ ^ 2 := by
  have heq : (∑ i, (a i : ℂ) * ek (-k) (w i)) =
      star (∑ i, (a i : ℂ) * ek k (w i)) := by
    simp only [ek, UnitAddTorus.mFourier_neg, map_sum, map_mul,
      Complex.conj_ofReal, RCLike.star_def]
  rw [heq, norm_star]

/-- [ The same ordered-row moment estimate holds for the other member of each
conjugate frequency pair.](goal) -/
-- @node: spectral_rounding_neg_character_second_moment
lemma spectral_rounding_neg_character_second_moment (n d j : ℕ)
    (w : Fin n → Torus d) :
    (∫ seeds, ‖∑ i, (sgn (orderedBoundaryRounding n (spectralRows w) seeds i) : ℂ) *
      ek (-featureFrequency d j) (w i)‖ ^ 2 ∂roundingSeedLaw n) ≤
      64 * (min (2 * j + 2) n : ℕ) := by
  simp_rw [character_imbalance_neg_eq]
  exact spectral_rounding_character_second_moment n d j w

/-- [ Character squared imbalance is integrable, by its exact real-row decomposition.](goal) -/
-- @node: spectral_rounding_character_sq_integrable
lemma spectral_rounding_character_sq_integrable (n d j : ℕ)
    (w : Fin n → Torus d) :
    MeasureTheory.Integrable (fun seeds =>
      ‖∑ i, (sgn (orderedBoundaryRounding n (spectralRows w) seeds i) : ℂ) *
        ek (featureFrequency d j) (w i)‖ ^ 2) (roundingSeedLaw n) := by
  have hi₁ := spectral_rounding_row_sq_integrable n d w
    (fun i => features d (2 * j + 1) (w i))
  have hi₂ := spectral_rounding_row_sq_integrable n d w
    (fun i => features d (2 * j + 2) (w i))
  apply (hi₁.add hi₂).div_const 2 |>.congr
  filter_upwards [] with seeds
  simpa only [Pi.add_apply, mul_comm] using
    (character_imbalance_eq_real_rows n d j w
      (fun i => sgn (orderedBoundaryRounding n (spectralRows w) seeds i))).symm

/-- [ The conditional character bound in the nonnegative integral form needed
for Tonelli and the reflected Fourier loss identity.](goal) -/
-- @node: spectral_rounding_character_lintegral_le
lemma spectral_rounding_character_lintegral_le (n d j : ℕ)
    (w : Fin n → Torus d) :
    (∫⁻ seeds, ENNReal.ofReal (‖∑ i,
      (sgn (orderedBoundaryRounding n (spectralRows w) seeds i) : ℂ) *
        ek (featureFrequency d j) (w i)‖ ^ 2) ∂roundingSeedLaw n) ≤
      ENNReal.ofReal (64 * (min (2 * j + 2) n : ℕ)) := by
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (spectral_rounding_character_sq_integrable n d j w)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (spectral_rounding_character_second_moment n d j w)

/-- The explicit frequency count converts the indexed rounding bound to its spectral minimum. Under [the stated conditions](hyp:hd), [the asserted mathematical result follows](goal). -/
-- @node: spectral_rounding_character_min_bound
lemma spectral_rounding_character_min_bound (n d i : ℕ) (hd : 2 ≤ d)
    (w : Fin n → Torus d) :
    (∫ seeds, ‖∑ j, (sgn (orderedBoundaryRounding n (spectralRows w) seeds j) : ℂ) *
      ek (featureFrequency d i) (w j)‖ ^ 2 ∂roundingSeedLaw n) ≤
      768 * min (n : ℝ) ((pairCount d : ℝ) *
        frequencyComplexity (featureFrequency d i)) := by
  have hmoment := spectral_rounding_character_second_moment n d i w
  have hindex := featureFrequency_real_rows_le_complexity (i := i) hd
  have hmidx : ((min (2 * i + 2) n : ℕ) : ℝ) ≤ (2 * i + 2 : ℝ) := by
    exact_mod_cast min_le_left (2 * i + 2) n
  have hmn : ((min (2 * i + 2) n : ℕ) : ℝ) ≤ n := by
    exact_mod_cast min_le_right (2 * i + 2) n
  by_cases hb : (pairCount d : ℝ) * frequencyComplexity (featureFrequency d i) ≤ n
  · rw [min_eq_right hb]
    linarith
  · rw [min_eq_left (le_of_not_ge hb)]
    have hn : (0 : ℝ) ≤ n := by positivity
    linarith

/-- [ Every nonzero frequency of support one or two obeys the same conditional minimum bound,
regardless of its conjugate orientation.](goal) Under [the stated conditions](hyp:hd,hk). -/
-- @node: spectral_rounding_supported_second_moment
lemma spectral_rounding_supported_second_moment (n d : ℕ) (hd : 2 ≤ d)
    (k : Fin d → ℤ)
    (hk : 1 ≤ (frequencySupport k).card ∧ (frequencySupport k).card ≤ 2)
    (w : Fin n → Torus d) :
    (∫ seeds, ‖∑ i, (sgn (orderedBoundaryRounding n (spectralRows w) seeds i) : ℂ) *
      ek k (w i)‖ ^ 2 ∂roundingSeedLaw n) ≤
      768 * min (n : ℝ) ((pairCount d : ℝ) * frequencyComplexity k) := by
  rcases supported_frequency_eq_feature_or_neg hd k hk with ⟨j, rfl | rfl⟩
  · exact spectral_rounding_character_min_bound n d j hd w
  · simp_rw [character_imbalance_neg_eq, frequencyComplexity_neg]
    exact spectral_rounding_character_min_bound n d j hd w

/-- [ The supported conditional character estimate in the nonnegative integral form for Tonelli.](goal) Under [the stated conditions](hyp:hd,hk). -/
-- @node: spectral_rounding_supported_lintegral_le
lemma spectral_rounding_supported_lintegral_le (n d : ℕ) (hd : 2 ≤ d)
    (k : Fin d → ℤ)
    (hk : 1 ≤ (frequencySupport k).card ∧ (frequencySupport k).card ≤ 2)
    (w : Fin n → Torus d) :
    (∫⁻ seeds, ENNReal.ofReal (‖∑ i,
      (sgn (orderedBoundaryRounding n (spectralRows w) seeds i) : ℂ) *
        ek k (w i)‖ ^ 2) ∂roundingSeedLaw n) ≤
      ENNReal.ofReal (768 * min (n : ℝ) ((pairCount d : ℝ) * frequencyComplexity k)) := by
  have hi : MeasureTheory.Integrable (fun seeds =>
      ‖∑ i, (sgn (orderedBoundaryRounding n (spectralRows w) seeds i) : ℂ) *
        ek k (w i)‖ ^ 2) (roundingSeedLaw n) := by
    rcases supported_frequency_eq_feature_or_neg hd k hk with ⟨j, rfl | rfl⟩
    · exact spectral_rounding_character_sq_integrable n d j w
    · simp_rw [character_imbalance_neg_eq]
      exact spectral_rounding_character_sq_integrable n d j w
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (spectral_rounding_supported_second_moment n d hd k hk w)

/-- [ Scaling the conditional minimum gives the normalized loss weight exactly.](goal) Under [the stated conditions](hyp:hn). -/
-- @node: spectral_min_loss_normalization
lemma spectral_min_loss_normalization {n : ℕ} (hn : 0 < n) (v : ℝ) :
    (4 / (n : ℝ)) * (768 * min (n : ℝ) v) =
      CUpper * min 1 (v / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hv : v ≤ n
  · rw [min_eq_right hv, min_eq_right ((div_le_one hnR).mpr hv)]
    unfold CUpper
    field_simp
    <;> ring
  · rw [min_eq_left (le_of_not_ge hv),
      min_eq_left ((one_le_div hnR).mpr (le_of_not_ge hv))]
    unfold CUpper
    field_simp
    <;> ring

/-- [ Fourier coefficients outside the nonzero order-two support vanish.](goal) Under [the stated conditions](hyp:hd,hs,hs1,hm,hk). -/
-- @node: sobolev_Fhat_eq_zero_outside_support
lemma sobolev_Fhat_eq_zero_outside_support {d : ℕ} {s : ℝ} (hd : 2 ≤ d)
    (hs : 0 < s) (hs1 : s ≤ 1) (m : CenteredL2Fn d) (hm : SobolevClass d s m)
    (k : Fin d → ℤ)
    (hk : ¬ (1 ≤ (frequencySupport k).card ∧ (frequencySupport k).card ≤ 2)) :
    Fhat m.val k = 0 := by
  have hbudget := exact_reflection_budget.2 d s hd hs hs1 m hm
  by_cases hc : (frequencySupport k).card = 0
  · have he : frequencySupport k = ∅ := Finset.card_eq_zero.mp hc
    have hk0 : k = 0 := by
      ext j
      have hj : j ∉ frequencySupport k := by rw [he]; simp
      simpa [frequencySupport] using hj
    rw [hk0]
    exact hbudget.1
  · exact hbudget.2.1 k (by omega)

/-- [ The original spectral branch obeys the truncated Fourier risk estimate.](goal) Under [the stated conditions](hyp:hn,hd,hs,hs1,hm). -/
-- @node: spectralRounding_loss_le_truncated
lemma spectralRounding_loss_le_truncated
    (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d) (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1)
    (m : CenteredL2Fn d) (hm : SobolevClass d s m) :
    loss ⟨spectralRoundingKernel n d, spectralRoundingKernel_markov n d⟩ m.val ≤
      ENNReal.ofReal CUpper * ∑' k : Fin d → ℤ,
        if 1 ≤ (frequencySupport k).card ∧ (frequencySupport k).card ≤ 2 then
          ENNReal.ofReal (‖Fhat m.val k‖ ^ 2 *
            min 1 (((pairCount d : ℝ) / n) * frequencyComplexity k)) else 0 := by
  classical
  rw [spectralRounding_loss_fourier n d (by omega) m,
    ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases hk : 1 ≤ (frequencySupport k).card ∧ (frequencySupport k).card ≤ 2
  · rw [if_pos hk]
    have hmoment : (∫⁻ w, ∫⁻ seeds, ENNReal.ofReal ‖∑ i,
        (sgn (orderedBoundaryRounding n (spectralRows w) seeds i) : ℂ) * ek k (w i)‖ ^ 2
          ∂roundingSeedLaw n ∂Measure.pi (fun _ : Fin n => torusMeasure d)) ≤
        ENNReal.ofReal (768 * min (n : ℝ) ((pairCount d : ℝ) * frequencyComplexity k)) := by
      calc
        _ ≤ ∫⁻ _w : Fin n → Torus d,
          ENNReal.ofReal (768 * min (n : ℝ) ((pairCount d : ℝ) * frequencyComplexity k))
            ∂Measure.pi (fun _ : Fin n => torusMeasure d) := by
              apply lintegral_mono
              intro w
              simpa only [← ENNReal.ofReal_pow (norm_nonneg _) 2] using
                spectral_rounding_supported_lintegral_le n d hd k hk w
        _ = _ := by simp
    calc
      _ ≤ ENNReal.ofReal (4 / (n : ℝ)) * (ENNReal.ofReal ‖Fhat m.val k‖ ^ 2 *
          ENNReal.ofReal (768 * min (n : ℝ) ((pairCount d : ℝ) * frequencyComplexity k))) :=
        by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_pow (norm_nonneg _) 2,
          ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by norm_num [CUpper])]
        congr 1
        have hnorm := spectral_min_loss_normalization (n := n) (by omega)
          ((pairCount d : ℝ) * frequencyComplexity k)
        have hdiv : ((pairCount d : ℝ) * frequencyComplexity k) / n =
            ((pairCount d : ℝ) / n) * frequencyComplexity k := by ring
        rw [hdiv] at hnorm
        nlinarith [hnorm]
  · rw [if_neg hk, sobolev_Fhat_eq_zero_outside_support hd hs hs1 m hm k hk]
    simp

/-- Independent fair signs cancel the real-valued off-diagonal terms. [The asserted mathematical result follows](goal). -/
-- @node: fairSigns_real_second_moment
lemma fairSigns_real_second_moment (n : ℕ) (a : Fin n → ℝ) :
    (∫ z, (∑ i, sgn (z i) * a i) ^ 2 ∂fairSigns n) = ∑ i, a i ^ 2 := by
  classical
  letI := fairSigns_probability n
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  rw [Finset.sum_eq_single i]
  · have hdiag (z : Signs n) : sgn (z i) * a i * (sgn (z i) * a i) = a i * a i := by
      cases z i <;> simp [sgn]
    simp_rw [hdiag]
    simp
  · intro j _ hij
    have hprod (z : Signs n) : sgn (z i) * a i * (sgn (z j) * a j) =
        sgn (z i) * sgn (z j) * (a i * a j) := by ring
    simp_rw [hprod]
    rw [integral_mul_const, fairSigns_distinct_product_mean_zero n i j (Ne.symm hij), zero_mul]
  · simp

/-- The independent-sign branch's loss is exactly four times the cube second moment. Under [the stated conditions](hyp:hn), [the asserted mathematical result follows](goal). -/
-- @node: fairSignKernel_loss_eq
lemma fairSignKernel_loss_eq (n d : ℕ) (hn : 0 < n) (m : CenteredL2Fn d) :
    loss (fairSignKernel n d) m.val =
      ENNReal.ofReal 4 * ∫⁻ x, ENNReal.ofReal (m.val x ^ 2) ∂cubeMeasure d := by
  classical
  letI := fairSigns_probability n
  have hm := m.property.1
  have hpoint (x : Covariates n d) :
      (∫⁻ z, ENNReal.ofReal ((∑ i, sgn (z i) * m.val (x i)) ^ 2) ∂fairSigns n) =
        ∑ i, ENNReal.ofReal (m.val (x i) ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.of_finite)
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _)),
      fairSigns_real_second_moment, ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  unfold loss
  simp only [fairSignKernel, Kernel.const_apply, hpoint]
  rw [lintegral_finsetSum _ (fun i _ => (by fun_prop :
    Measurable (fun x : Covariates n d => ENNReal.ofReal (m.val (x i) ^ 2))))]
  have heval (i : Fin n) :
      (∫⁻ x, ENNReal.ofReal (m.val (x i) ^ 2) ∂covLaw n d) =
        ∫⁻ x, ENNReal.ofReal (m.val x ^ 2) ∂cubeMeasure d := by
    have hpres := measurePreserving_eval (fun _ : Fin n => cubeMeasure d) i
    exact hpres.lintegral_comp (by fun_prop :
      Measurable (fun x : Cube d => ENNReal.ofReal (m.val x ^ 2)))
  simp_rw [heval]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [div_mul_cancel₀ 4 hnR]

/-- [ The cube Sobolev budget bounds independent-sign loss by four.](goal) Under [the stated conditions](hyp:hn,hd,hs,hs1,hm). -/
-- @node: fairSignKernel_loss_le_four
lemma fairSignKernel_loss_le_four (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1)
    (m : CenteredL2Fn d) (hm : SobolevClass d s m) :
    loss (fairSignKernel n d) m.val ≤ ENNReal.ofReal 4 := by
  rw [fairSignKernel_loss_eq n d (by omega) m]
  have hi : Integrable (fun x => m.val x ^ 2) (cubeMeasure d) :=
    (memLp_two_iff_integrable_sq m.property.1.aestronglyMeasurable).mp m.property.2.1
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
  calc
    _ ≤ ENNReal.ofReal 4 * ENNReal.ofReal 1 := by
      gcongr
      exact sobolev_cube_second_moment_le_one hd hs hs1 m hm
    _ = _ := by simp

/-- [ The concrete spectral design is fair, outcome independent, and has the stated upper risk.](goal) Under [the stated conditions](hyp:hn,hd). -/
-- @node: spectral_design_upper
lemma spectral_design_upper
    (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d) :
    DesignClass n d (piStar n d) ∧ ∀ s : ℝ, 0 < s → s ≤ 1 →
      worstLoss (piStar n d) s ≤ ENNReal.ofReal (CUpper * aScale n d s) := by
  refine ⟨piStar_designClass n d, ?_⟩
  intro s hs hs1
  unfold worstLoss
  refine iSup_le fun m => ?_
  by_cases hb : n ≤ pairCount d
  · have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have ha : aScale n d s = 1 := by
      unfold aScale
      apply min_eq_left
      apply Real.one_le_rpow _ hs.le
      apply (one_le_div hnR).mpr
      exact_mod_cast hb
    rw [ha, mul_one]
    have hfour := fairSignKernel_loss_le_four n d hn hd s hs hs1 m.val m.property
    simpa only [piStar, if_pos hb] using
      hfour.trans (ENNReal.ofReal_le_ofReal (by norm_num [CUpper]))
  · let S : ℝ≥0∞ := ∑' k : Fin d → ℤ,
      if 1 ≤ (frequencySupport k).card ∧ (frequencySupport k).card ≤ 2 then
        ENNReal.ofReal (‖Fhat m.val.val k‖ ^ 2 *
          min 1 (((pairCount d : ℝ) / n) * frequencyComplexity k)) else 0
    calc
      loss (piStar n d) m.val.val ≤ ENNReal.ofReal CUpper * S := by
        simpa only [piStar, if_neg hb] using
          spectralRounding_loss_le_truncated n d hn hd s hs hs1 m.val m.property
      _ ≤ ENNReal.ofReal CUpper * ENNReal.ofReal (aScale n d s) := by
        gcongr
        exact sobolev_truncated_spectral_sum_le_scale n d hd s hs hs1 m.val m.property
      _ = ENNReal.ofReal (CUpper * aScale n d s) := by
        rw [ENNReal.ofReal_mul (by norm_num [CUpper])]

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity

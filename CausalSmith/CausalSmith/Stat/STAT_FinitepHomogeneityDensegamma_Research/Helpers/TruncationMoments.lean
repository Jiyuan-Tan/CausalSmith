module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.Scores

/-! Finite-moment homogeneity testing: Helpers/TruncationMoments. -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- Clipping preserves an observation inside its symmetric cutoff interval. This statement assumes [the hy condition](hyp:hy). [This is the stated conclusion](goal). -/
-- @node: clipY_eq_of_abs_le
lemma clipY_eq_of_abs_le (T y : ℝ) (hy : |y| ≤ T) : clipY T y = y := by
  obtain ⟨hl, hu⟩ := abs_le.mp hy
  simp only [clipY, min_eq_left hu, max_eq_right hl]

/-- A nonnegative clipping cutoff bounds the absolute clipped observation. This statement assumes [the hT condition](hyp:hT). [This is the stated conclusion](goal). -/
-- @node: clipY_abs_le
lemma clipY_abs_le (T y : ℝ) (hT : 0 ≤ T) : |clipY T y| ≤ T := by
  apply abs_le.mpr
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_right _ _)

/-- The clipping remainder never exceeds the magnitude of the original observation. This statement assumes [the hT condition](hyp:hT). [This is the stated conclusion](goal). -/
-- @node: clipY_remainder_abs_le
lemma clipY_remainder_abs_le (T y : ℝ) (hT : 0 ≤ T) : |y-clipY T y| ≤ |y| := by
  by_cases hl : y < -T
  · have hy : y ≤ 0 := by linarith
    simp only [clipY, min_eq_left (show y ≤ T by linarith),
      max_eq_left hl.le, abs_of_nonpos hy,
      abs_of_nonpos (show y - -T ≤ 0 by linarith)]
    linarith
  · by_cases hu : T < y
    · simp only [clipY, min_eq_right hu.le,
        max_eq_right (show -T ≤ T by linarith),
        abs_of_nonneg (show 0 ≤ y by linarith),
        abs_of_nonneg (show 0 ≤ y-T by linarith)]
      linarith
    · rw [clipY_eq_of_abs_le T y (abs_le.mpr ⟨by linarith, by linarith⟩)]
      simp

/-- The moment envelope dominates the clipping bias and clipped second moment pointwise. This statement assumes [the hp condition](hyp:hp), [the hp2 condition](hyp:hp2), [the hT condition](hyp:hT). [This is the stated conclusion](goal). -/
-- @node: clipY_moment_domination
lemma clipY_moment_domination (p T y : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hT : 0 < T) :
    |y-clipY T y| ≤ |y|^p*T^(1-p) ∧
    clipY T y^2 ≤ |y|^p*T^(2-p) := by
  have hpow : 0 ≤ |y|^p := Real.rpow_nonneg (abs_nonneg y) _
  by_cases hy : |y| ≤ T
  · constructor
    · rw [clipY_eq_of_abs_le T y hy]
      simpa using mul_nonneg hpow (Real.rpow_nonneg hT.le (1-p))
    · rw [clipY_eq_of_abs_le T y hy]
      have he : |y|^p*|y|^(2-p) = y^2 := by
        rw [← Real.rpow_add' (abs_nonneg y) (by linarith : p+(2-p) ≠ 0)]
        rw [show p+(2-p)=2 by ring, Real.rpow_two, sq_abs]
      rw [← he]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (abs_nonneg y) hy (by linarith)) hpow
  · have hyt : T ≤ |y| := (lt_of_not_ge hy).le
    have hyp : 0 < |y| := hT.trans_le hyt
    constructor
    · calc
        |y-clipY T y| ≤ |y| := clipY_remainder_abs_le T y hT.le
        _ = |y|^p*|y|^(1-p) := by
          rw [← Real.rpow_add hyp, show p+(1-p)=1 by ring, Real.rpow_one]
        _ ≤ |y|^p*T^(1-p) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hT hyt (by linarith)) hpow
    · calc
        clipY T y^2 ≤ T^2 := by
          have hb := abs_le.mp (clipY_abs_le T y hT.le)
          nlinarith [hb.1, hb.2]
        _ = T^p*T^(2-p) := by
          rw [← Real.rpow_add hT, show p+(2-p)=2 by ring, Real.rpow_two]
        _ ≤ |y|^p*T^(2-p) := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hT.le hyt (by linarith))
          (Real.rpow_nonneg hT.le _)

/-- A finite raw moment envelope yields an integrable power and an integrable original outcome. This statement assumes [the hp condition](hyp:hp), [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: integrable_outcome_of_raw_moment
lemma integrable_outcome_of_raw_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : 1 ≤ p)
    (hm : ∫⁻ y, ENNReal.ofReal (|y|^p) ∂μ ≤ 10) :
    Integrable (fun y : ℝ => |y|^p) μ ∧ Integrable (fun y : ℝ => y) μ ∧
    (∫ y, |y|^p ∂μ) ≤ 10 := by
  have hp0 : 0 ≤ p := by linarith
  have hn : ∀ᵐ y ∂μ, 0 ≤ |y|^p := Filter.Eventually.of_forall
    (fun y => Real.rpow_nonneg (abs_nonneg y) p)
  have hi : Integrable (fun y : ℝ => |y|^p) μ := by
    refine ⟨by fun_prop, (hasFiniteIntegral_iff_ofReal hn).mpr ?_⟩
    exact hm.trans_lt (by norm_num)
  have hid : Integrable (fun y : ℝ => y) μ := by
    apply ((integrable_const (1:ℝ)).add hi).mono' (by fun_prop)
    apply Filter.Eventually.of_forall
    intro y
    change |y| ≤ 1+|y|^p
    by_cases hy : |y| ≤ 1
    · linarith [Real.rpow_nonneg (abs_nonneg y) p]
    · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hy) hp
      rw [Real.rpow_one] at h
      linarith
  refine ⟨hi, hid, ?_⟩
  have hreal : ENNReal.ofReal (∫ y, |y|^p ∂μ) ≤ ENNReal.ofReal 10 := by
    rw [ofReal_integral_eq_lintegral_ofReal hi hn]
    simpa only [ENNReal.ofReal_ofNat] using hm
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hreal

/-- Conditional truncation moments: the displayed mathematical construction or bound. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hT condition](hyp:hT). [This is the stated conclusion](goal). -/
-- @node: conditional_truncation_moments
lemma conditional_truncation_moments (v : Params) (hv : v.Valid) (law : ObservedLaw)
    (hm : RawMoment v law) (T : ℝ) (hT : 1 ≤ T) :
    ∀ a : Bool, ∀ᵐ x ∂design,
      Integrable (fun y : ℝ => y) (law.Q a x) ∧
      |∫ y, y-clipY T y ∂law.Q a x| ≤ 10*T^(1-v.p) ∧
      (∫ y, clipY T y^2 ∂law.Q a x) ≤ 10*T^(2-v.p) := by
  intro a
  filter_upwards [hm a] with x hx
  obtain ⟨hpow, hid, hbound⟩ := integrable_outcome_of_raw_moment
    (law.Q a x) v.p (by linarith [hv.1.1]) hx
  have hTp : 0 < T := by linarith
  have hclip : Integrable (fun y => clipY T y) (law.Q a x) := by
    apply (integrable_const T).mono' (by unfold clipY; fun_prop)
    exact Filter.Eventually.of_forall (fun y => by
      simpa only [Real.norm_eq_abs] using clipY_abs_le T y hTp.le)
  have hsq : Integrable (fun y => clipY T y^2) (law.Q a x) := by
    apply (hpow.mul_const (T^(2-v.p))).mono' (by unfold clipY; fun_prop)
    apply Filter.Eventually.of_forall
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (clipY_moment_domination v.p T y (by linarith [hv.1.1]) hv.1.2 hTp).2
  refine ⟨hid, ?_, ?_⟩
  · calc
      |∫ y, y-clipY T y ∂law.Q a x| ≤ ∫ y, |y-clipY T y| ∂law.Q a x := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun y => y-clipY T y)
      _ ≤ ∫ y, |y|^v.p*T^(1-v.p) ∂law.Q a x :=
        integral_mono_ae (hid.sub hclip).abs (hpow.mul_const _) (Filter.Eventually.of_forall
          (fun y => (clipY_moment_domination v.p T y (by linarith [hv.1.1]) hv.1.2 hTp).1))
      _ = (∫ y, |y|^v.p ∂law.Q a x)*T^(1-v.p) := integral_mul_const _ _
      _ ≤ 10*T^(1-v.p) := mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg hTp.le _)
  · calc
      (∫ y, clipY T y^2 ∂law.Q a x) ≤ ∫ y, |y|^v.p*T^(2-v.p) ∂law.Q a x :=
        integral_mono_ae hsq (hpow.mul_const _) (Filter.Eventually.of_forall
          (fun y => (clipY_moment_domination v.p T y (by linarith [hv.1.1]) hv.1.2 hTp).2))
      _ = (∫ y, |y|^v.p ∂law.Q a x)*T^(2-v.p) := integral_mul_const _ _
      _ ≤ 10*T^(2-v.p) := mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg hTp.le _)


end CausalSmith.Stat.FinitepHomogeneityDensegamma

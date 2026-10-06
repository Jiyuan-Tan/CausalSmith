module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Witnesses
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.LowerPairDesign
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Risk
public import Causalean.Mathlib.InformationTheory.ProductKLLeCam
public import Causalean.Mathlib.Probability.SignedTwoPoint
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! # Smoothness, bounds, and conditional information for the binary witnesses -/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory InformationTheory
open scoped ENNReal

-- @node: bump1_unit_interval
/-- The one-sided cutoff stays between zero and one on nonnegative inputs. -/
lemma bump1_unit_interval (t : ℝ) (ht : 0 ≤ t) : bump1 t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold bump1
  split_ifs with h
  · constructor
    · exact (Real.exp_pos _).le
    · apply Real.exp_le_one_iff.mpr
      have : 0 < (1 / 2 : ℝ) - t := by linarith
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) this.le
  · exact ⟨le_rfl, by norm_num⟩

-- @node: witnessBump_unit_interval
/-- The tensor cutoff is bounded by one throughout the nonnegative orthant. -/
lemma witnessBump_unit_interval (d : ℕ) (x : Fin d → ℝ)
    (hx : ∀ i, 0 ≤ x i) : witnessBump d x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold witnessBump
  constructor
  · exact Finset.prod_nonneg (fun i _ => (bump1_unit_interval (x i) (hx i)).1)
  · exact Finset.prod_le_one (fun i _ => (bump1_unit_interval (x i) (hx i)).1)
      (fun i _ => (bump1_unit_interval (x i) (hx i)).2)

-- @node: witnessBump_zero
/-- The witness cutoff attains its maximum at the lower cube corner. -/
lemma witnessBump_zero (d : ℕ) : witnessBump d (fun _ => 0) = 1 := by
  simp [witnessBump, bump1]

-- @node: witnessMean_supLoss
/-- The two signs attain their maximum regression gap at the cube corner. -/
lemma witnessMean_supLoss (d : ℕ) (β δ h : ℝ) (hδ : 0 ≤ δ) (hh : 0 < h) :
    supLoss (witnessMean d β δ h true) (witnessMean d β δ h false) =
      ENNReal.ofReal (2 * δ * h ^ β) := by
  have hbase : 0 ≤ 2 * δ * h ^ β := by positivity
  have hpoint (x : Fin d → ℝ) :
      witnessMean d β δ h true x - witnessMean d β δ h false x =
        2 * δ * h ^ β * witnessBump d (fun i => x i / h) := by
    simp [witnessMean]
    ring
  have hupper : supLoss (witnessMean d β δ h true)
      (witnessMean d β δ h false) ≤ ENNReal.ofReal (2 * δ * h ^ β) := by
    unfold supLoss
    apply iSup_le
    intro x
    apply ENNReal.ofReal_le_ofReal
    rw [hpoint]
    have hb := witnessBump_unit_interval d (fun i => x.val i / h)
      (by intro i; exact div_nonneg (x.property i (Set.mem_univ i)).1 hh.le)
    rw [abs_of_nonneg (mul_nonneg hbase hb.1)]
    exact mul_le_of_le_one_right hbase hb.2
  have hzero : (fun _ : Fin d => (0 : ℝ)) ∈ cube d := by
    intro i hi
    exact ⟨le_rfl, by norm_num⟩
  have hlower : ENNReal.ofReal (2 * δ * h ^ β) ≤
      supLoss (witnessMean d β δ h true) (witnessMean d β δ h false) := by
    unfold supLoss
    have := le_iSup (fun x : cube d =>
      ENNReal.ofReal |witnessMean d β δ h true x - witnessMean d β δ h false x|)
      ⟨fun _ => 0, hzero⟩
    simpa [hpoint, witnessBump_zero, abs_of_nonneg hbase] using this
  exact le_antisymm hupper hlower

-- @node: lowerPair_supLoss
/-- The regression components of the constructed laws have the exact separation. -/
lemma lowerPair_supLoss (d : ℕ) (β q h δ M : ℝ) (hδ : 0 ≤ δ) (hh : 0 < h) :
    supLoss (lowerPair d β q h δ M true).mu1
      (lowerPair d β q h δ M false).mu1 = ENNReal.ofReal (2 * δ * h ^ β) := by
  exact witnessMean_supLoss d β δ h hδ hh

-- @node: witnessMean_abs_le_delta_on_cube
/-- The signed bump stays within its amplitude on the covariate cube. -/
lemma witnessMean_abs_le_delta_on_cube (d : ℕ) (β δ h : ℝ)
    (hβ : 0 < β) (hδ : 0 ≤ δ) (hh : 0 < h) (hh1 : h ≤ 1)
    (sign : Bool) (x : Fin d → ℝ) (hx : x ∈ cube d) :
    |witnessMean d β δ h sign x| ≤ δ := by
  have hb := witnessBump_unit_interval d (fun i => x i / h)
    (by intro i; exact div_nonneg (hx i (Set.mem_univ i)).1 hh.le)
  have hp : 0 ≤ h ^ β := Real.rpow_nonneg hh.le _
  have hp1 : h ^ β ≤ 1 := Real.rpow_le_one hh.le hh1 hβ.le
  have hprod : 0 ≤ δ * h ^ β * witnessBump d (fun i => x i / h) := by
    exact mul_nonneg (mul_nonneg hδ hp) hb.1
  have hle : δ * h ^ β * witnessBump d (fun i => x i / h) ≤ δ := by
    calc
      δ * h ^ β * witnessBump d (fun i => x i / h) ≤ δ * h ^ β := by
        exact mul_le_of_le_one_right (mul_nonneg hδ hp) hb.2
      _ ≤ δ := by nlinarith
  cases sign <;> simpa [witnessMean, abs_mul, abs_of_nonneg hδ,
    abs_of_nonneg hp, abs_of_nonneg hb.1, mul_assoc] using hle

-- @node: treatedPlusProbability_quarter_bounds
/-- Small bump amplitude keeps both binary probabilities away from zero. -/
lemma treatedPlusProbability_quarter_bounds (d : ℕ) (β δ h M : ℝ)
    (hβ : 0 < β) (hδ : 0 ≤ δ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (sign : Bool) (x : Fin d → ℝ) (hx : x ∈ cube d) :
    treatedPlusProbability d β δ h M sign x ∈ Set.Icc (1 / 4 : ℝ) (3 / 4) := by
  have habs := witnessMean_abs_le_delta_on_cube d β δ h hβ hδ hh hh1 sign x hx
  have hbounds : -δ ≤ witnessMean d β δ h sign x ∧
      witnessMean d β δ h sign x ≤ δ := abs_le.mp habs
  have hratio : -(1 / 2 : ℝ) ≤ 2 * witnessMean d β δ h sign x / M ∧
      2 * witnessMean d β δ h sign x / M ≤ 1 / 2 := by
    constructor
    · apply (le_div_iff₀ hM).2
      nlinarith [hbounds.1]
    · apply (div_le_iff₀ hM).2
      nlinarith [hbounds.2]
  unfold treatedPlusProbability
  constructor <;> linarith [hratio.1, hratio.2]

-- @node: witnessMean_opposite_sign
/-- The two regressions in the binary witness have opposite signs pointwise. -/
lemma witnessMean_opposite_sign (d : ℕ) (β δ h : ℝ) (x : Fin d → ℝ) :
    witnessMean d β δ h false x = -witnessMean d β δ h true x := by
  simp [witnessMean]

-- @node: treatedPlusProbability_complement
/-- The two treated outcome probabilities are complementary. -/
lemma treatedPlusProbability_complement (d : ℕ) (β δ h M : ℝ)
    (x : Fin d → ℝ) :
    treatedPlusProbability d β δ h M false x =
      1 - treatedPlusProbability d β δ h M true x := by
  rw [treatedPlusProbability, treatedPlusProbability,
    witnessMean_opposite_sign]
  ring

-- @node: binaryLogRatio_quadratic_bound
/-- The symmetric binary log likelihood has a quadratic bound in its mean shift. -/
lemma binaryLogRatio_quadratic_bound (z : ℝ)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 2) :
    z * Real.log ((1 + z) / (1 - z)) ≤ 4 * z ^ 2 := by
  have hden : 0 < 1 - z := by linarith
  have hnum : 0 < 1 + z := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hnum hden)
  have hratio : (1 + z) / (1 - z) - 1 ≤ 4 * z := by
    have hquot : (1 + z) / (1 - z) ≤ 1 + 4 * z := by
      apply (div_le_iff₀ hden).2
      nlinarith [mul_nonneg hz0 (by linarith : 0 ≤ 1 - 2 * z)]
    linarith
  nlinarith [mul_le_mul_of_nonneg_left (hlog.trans hratio) hz0]

-- @node: witnessBump_support_on_cube
/-- A nonzero tensor cutoff on the nonnegative orthant lies in the lower half-cube. -/
lemma witnessBump_support_on_cube (d : ℕ) (x : Fin d → ℝ)
    (hb : witnessBump d x ≠ 0) :
    ∀ i, x i < 1 / 2 := by
  intro i
  by_contra hi
  have hxi : 1 / 2 ≤ x i := le_of_not_gt hi
  have hbi : bump1 (x i) = 0 := by
    have hnot : ¬ x i < (2 : ℝ)⁻¹ := by simpa only [one_div] using hi
    simp [bump1, hnot]
  exact hb (Finset.prod_eq_zero (Finset.mem_univ i) hbi)

-- @node: witnessMean_support_on_cube
/-- On the covariate cube, a nonzero signed mean is confined to a cube of width `h/2`. -/
lemma witnessMean_support_on_cube (d : ℕ) (β δ h : ℝ) (sign : Bool)
    (hh : 0 < h) (x : Fin d → ℝ)
    (hm : witnessMean d β δ h sign x ≠ 0) :
    ∀ i, x i < h / 2 := by
  have hb : witnessBump d (fun i => x i / h) ≠ 0 := by
    intro hzero
    exact hm (by simp [witnessMean, hzero])
  have hs := witnessBump_support_on_cube d (fun i => x i / h) hb
  intro i
  have hi := hs i
  exact (div_lt_iff₀ hh).mp hi |>.trans_eq (by ring)

-- @node: witnessMean_zero_outside_lower_cube
/-- Beyond the lower half-cube, both witness regressions vanish. -/
lemma witnessMean_zero_outside_lower_cube (d : ℕ) (β δ h : ℝ) (sign : Bool)
    (hh : 0 < h) (x : Fin d → ℝ)
    (i : Fin d) (hi : h / 2 ≤ x i) :
    witnessMean d β δ h sign x = 0 := by
  by_contra hm
  have hs := witnessMean_support_on_cube d β δ h sign hh x hm i
  linarith

-- @node: treatedPlusProbability_off_support
/-- Outside the witness cube, the treated binary outcome has its common fair-coin law. -/
lemma treatedPlusProbability_off_support (d : ℕ) (β δ h M : ℝ) (sign : Bool)
    (hh : 0 < h) (x : Fin d → ℝ) (i : Fin d) (hi : h / 2 ≤ x i) :
    treatedPlusProbability d β δ h M sign x = 1 / 2 := by
  have hzero := witnessMean_zero_outside_lower_cube d β δ h sign hh x i hi
  simp [treatedPlusProbability, hzero]

/-- Binary outcome weights normalize whenever the plus probability lies in `[0,1]`. -/
-- @node: binaryMeasure_isProbabilityMeasure
lemma binaryMeasure_isProbabilityMeasure (M p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (binaryMeasure M p) := by
  apply isProbabilityMeasure_iff.mpr
  simp only [binaryMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hp.1 (sub_nonneg.mpr hp.2)]
  norm_num

/-- The two-atom outcome law has the weighted mean of its signed support points. -/
-- @node: binaryMeasure_integral_id
lemma binaryMeasure_integral_id (M p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    (∫ y, y ∂binaryMeasure M p) = (2 * p - 1) * M / 2 := by
  have hi (a c : ℝ) : Integrable (fun y : ℝ => y)
      (ENNReal.ofReal c • Measure.dirac a) := by
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [binaryMeasure, integral_add_measure (hi _ _) (hi _ _)]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hp.1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hp.2), smul_eq_mul]
  ring

/-- The chosen binary probabilities give precisely the signed treated bump mean. -/
-- @node: binaryMeasure_treated_mean
lemma binaryMeasure_treated_mean (d : ℕ) (β δ h M : ℝ)
    (hβ : 0 < β) (hδ : 0 ≤ δ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (sign : Bool) (x : Fin d → ℝ) (hx : x ∈ cube d) :
    (∫ y, y ∂binaryMeasure M (treatedPlusProbability d β δ h M sign x)) =
      witnessMean d β δ h sign x := by
  have hp := treatedPlusProbability_quarter_bounds d β δ h M
    hβ hδ hh hh1 hM hsmall sign x hx
  rw [binaryMeasure_integral_id M _ ⟨by linarith [hp.1], by linarith [hp.2]⟩]
  unfold treatedPlusProbability
  field_simp
  ring

/-- Every binary outcome is in the prescribed outcome range, regardless of its weights. -/
-- @node: binaryMeasure_ae_bounded
lemma binaryMeasure_ae_bounded (M p : ℝ) (hM : 0 ≤ M) :
    ∀ᵐ y ∂binaryMeasure M p, |y| ≤ M := by
  have hplus : ∀ᵐ y ∂Measure.dirac (M / 2), |y| ≤ M := by
    simp only [ae_dirac_eq, Filter.eventually_pure, abs_of_nonneg (by positivity : 0 ≤ M / 2)]
    linarith
  have hminus : ∀ᵐ y ∂Measure.dirac (-M / 2), |y| ≤ M := by
    simp only [ae_dirac_eq, Filter.eventually_pure, neg_div, abs_neg,
      abs_of_nonneg (by positivity : 0 ≤ M / 2)]
    linarith
  exact ae_add_measure_iff.mpr
    ⟨Measure.ae_smul_measure hplus _, Measure.ae_smul_measure hminus _⟩

/-- The recorded observation and observed law of either witness satisfy consistency
by construction. -/
-- @node: lowerPair_consistency
lemma lowerPair_consistency (d : ℕ) (β q h δ M : ℝ) (sign : Bool) :
    Consistency (lowerPair d β q h δ M sign) := by
  constructor
  · exact Filter.Eventually.of_forall (fun _ => rfl)
  · rfl

/-- The paper's one-sided cutoff is an affine rescaling of the standard flat glue. -/
-- @node: bump1_eq_expNegInvGlue
lemma bump1_eq_expNegInvGlue (t : ℝ) :
    bump1 t = Real.exp 1 * expNegInvGlue (1 - 2 * t) := by
  by_cases ht : t < 1 / 2
  · have hpos : 0 < 1 - 2 * t := by linarith
    have hden : (1 / 2 : ℝ) - t ≠ 0 := by linarith
    rw [bump1, if_pos ht, expNegInvGlue, if_neg (not_le.mpr hpos),
      ← Real.exp_add]
    congr 1
    have hden2 : 1 - t * 2 ≠ 0 := by nlinarith
    field_simp [hden, hden2]
    ring
  · have hnonpos : 1 - 2 * t ≤ 0 := by linarith
    rw [bump1, if_neg ht, expNegInvGlue.zero_of_nonpos hnonpos, mul_zero]

/-- The cutoff is smooth on the whole real line, including its flat upper boundary. -/
-- @node: bump1_contDiff
lemma bump1_contDiff {n : ℕ∞} : ContDiff ℝ n bump1 := by
  have heq : bump1 = fun t => Real.exp 1 * expNegInvGlue (1 - 2 * t) :=
    funext bump1_eq_expNegInvGlue
  rw [heq]
  exact contDiff_const.mul (expNegInvGlue.contDiff.comp
    (contDiff_const.sub (contDiff_const.mul contDiff_id)))

/-- The tensor witness is smooth on the entire ambient covariate space. -/
-- @node: witnessBump_contDiff
lemma witnessBump_contDiff (d : ℕ) {n : ℕ∞} : ContDiff ℝ n (witnessBump d) := by
  unfold witnessBump
  apply contDiff_prod
  intro i hi
  exact bump1_contDiff.comp (contDiff_apply ℝ ℝ i)

/-- Both scaled signed witness means have smooth whole-space extensions. -/
-- @node: witnessMean_contDiff
lemma witnessMean_contDiff (d : ℕ) (β δ h : ℝ) (sign : Bool) {n : ℕ∞} :
    ContDiff ℝ n (witnessMean d β δ h sign) := by
  unfold witnessMean
  apply contDiff_const.mul
  apply (witnessBump_contDiff d).comp
  apply contDiff_pi.mpr
  intro i
  exact (contDiff_apply ℝ ℝ i).div_const h

/-- The cutoff is globally bounded even on the negative half-line where it is nonzero. -/
-- @node: bump1_global_bound
lemma bump1_global_bound (t : ℝ) : bump1 t ∈ Set.Icc (0 : ℝ) (Real.exp 1) := by
  rw [bump1_eq_expNegInvGlue]
  constructor
  · exact mul_nonneg (Real.exp_pos 1).le (expNegInvGlue.nonneg _)
  · apply mul_le_of_le_one_right (Real.exp_pos 1).le
    by_cases ht : 1 - 2 * t ≤ 0
    · rw [expNegInvGlue.zero_of_nonpos ht]
      norm_num
    · rw [expNegInvGlue, if_neg ht]
      apply Real.exp_le_one_iff.mpr
      exact neg_nonpos.mpr (inv_nonneg.mpr (le_of_not_ge ht))

/-- The ambient tensor cutoff has a finite global value bound depending only on dimension. -/
-- @node: witnessBump_global_bound
lemma witnessBump_global_bound (d : ℕ) (x : Fin d → ℝ) :
    witnessBump d x ∈ Set.Icc (0 : ℝ) ((Real.exp 1) ^ d) := by
  unfold witnessBump
  constructor
  · exact Finset.prod_nonneg (fun i _ => (bump1_global_bound (x i)).1)
  · calc
      (∏ i : Fin d, bump1 (x i)) ≤ ∏ _i : Fin d, Real.exp 1 :=
        Finset.prod_le_prod (fun i _ => (bump1_global_bound (x i)).1)
          (fun i _ => (bump1_global_bound (x i)).2)
      _ = (Real.exp 1) ^ d := by simp

/-- Smoothness supplies the measurable witness regression required by its conditional law. -/
-- @node: witnessMean_measurable
@[fun_prop] lemma witnessMean_measurable (d : ℕ) (β δ h : ℝ) (sign : Bool) :
    Measurable (witnessMean d β δ h sign) := by
  exact (witnessMean_contDiff d β δ h sign (n := 0)).continuous.measurable

/-- The treated binary probability is measurable on the whole covariate space. -/
-- @node: treatedPlusProbability_measurable
@[fun_prop] lemma treatedPlusProbability_measurable (d : ℕ) (β δ h M : ℝ)
    (sign : Bool) : Measurable (treatedPlusProbability d β δ h M sign) := by
  unfold treatedPlusProbability
  fun_prop

/-- The witness outcome law is exactly the library's signed mean channel. -/
-- @node: binaryMeasure_eq_twoPointMean
lemma binaryMeasure_eq_twoPointMean (M u : ℝ) :
    binaryMeasure M ((1 + 2 * u / M) / 2) =
      Causalean.Mathlib.Probability.twoPointMean (M / 2) u := by
  unfold binaryMeasure Causalean.Mathlib.Probability.twoPointMean
  have hratio : u / (M / 2) = 2 * u / M := by ring
  rw [hratio]
  congr 2 <;> congr 1 <;> ring

/-- The cube-wise witness bound retains the bandwidth amplitude needed in KL estimates. -/
-- @node: witnessMean_abs_le_amplitude
lemma witnessMean_abs_le_amplitude (d : ℕ) (β δ h : ℝ)
    (hδ : 0 ≤ δ) (hh : 0 < h) (sign : Bool)
    (x : Fin d → ℝ) (hx : x ∈ cube d) :
    |witnessMean d β δ h sign x| ≤ δ * h ^ β := by
  have hb := witnessBump_unit_interval d (fun i => x i / h)
    (by intro i; exact div_nonneg (hx i (Set.mem_univ i)).1 hh.le)
  have hamp : 0 ≤ δ * h ^ β := mul_nonneg hδ (Real.rpow_nonneg hh.le β)
  have hle := mul_le_of_le_one_right hamp hb.2
  cases sign <;> simpa [witnessMean, abs_mul, abs_of_nonneg hδ,
    abs_of_nonneg (Real.rpow_nonneg hh.le β), abs_of_nonneg hb.1,
    mul_assoc] using hle

/-- The conditional treated binary laws have quadratic divergence in the actual bump value. -/
-- @node: treatedBinary_klDiv_le_mean_sq
lemma treatedBinary_klDiv_le_mean_sq (d : ℕ) (β δ h M : ℝ)
    (hβ : 0 < β) (hδ : 0 ≤ δ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (x : Fin d → ℝ) (hx : x ∈ cube d) :
    klDiv (binaryMeasure M (treatedPlusProbability d β δ h M true x))
      (binaryMeasure M (treatedPlusProbability d β δ h M false x)) ≤
      ENNReal.ofReal (16 * (witnessMean d β δ h true x) ^ 2 / M ^ 2) := by
  have hp := witnessMean_abs_le_delta_on_cube d β δ h hβ hδ hh hh1 true x hx
  have hm := witnessMean_abs_le_delta_on_cube d β δ h hβ hδ hh hh1 false x hx
  have hp' : |witnessMean d β δ h true x| ≤ (M / 2) / 2 := by linarith
  have hm' : |witnessMean d β δ h false x| ≤ (M / 2) / 2 := by linarith
  unfold treatedPlusProbability
  rw [binaryMeasure_eq_twoPointMean, binaryMeasure_eq_twoPointMean]
  have hkl := Causalean.Mathlib.Probability.bernoulli_mean_channel_kl (M / 2)
    (witnessMean d β δ h true x) (witnessMean d β δ h false x)
    (by positivity) hp' hm'
  rw [witnessMean_opposite_sign] at hkl ⊢
  convert hkl using 1
  congr 1
  ring

/-- Uniformly on the cube, conditional treated KL is at most a constant times `h^(2β)`. -/
-- @node: treatedBinary_klDiv_le_amplitude_sq
lemma treatedBinary_klDiv_le_amplitude_sq (d : ℕ) (β δ h M : ℝ)
    (hβ : 0 < β) (hδ : 0 ≤ δ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (x : Fin d → ℝ) (hx : x ∈ cube d) :
    klDiv (binaryMeasure M (treatedPlusProbability d β δ h M true x))
      (binaryMeasure M (treatedPlusProbability d β δ h M false x)) ≤
      ENNReal.ofReal (16 * δ ^ 2 / M ^ 2 * h ^ (2 * β)) := by
  apply (treatedBinary_klDiv_le_mean_sq d β δ h M
    hβ hδ hh hh1 hM hsmall x hx).trans
  apply ENNReal.ofReal_le_ofReal
  have habs := witnessMean_abs_le_amplitude d β δ h hδ hh true x hx
  have hamp : 0 ≤ δ * h ^ β := by positivity
  have hsq : (witnessMean d β δ h true x) ^ 2 ≤ (δ * h ^ β) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) hamp).mpr habs
  have hpow : (h ^ β) ^ 2 = h ^ (2 * β) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]
    congr 1
    ring
  calc
    16 * (witnessMean d β δ h true x) ^ 2 / M ^ 2 ≤
        16 * (δ * h ^ β) ^ 2 / M ^ 2 := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num))
        (sq_nonneg M)
    _ = 16 * δ ^ 2 / M ^ 2 * h ^ (2 * β) := by rw [mul_pow, hpow]; ring

/-- Outside the lower witness cube the two treated channels coincide, so their KL vanishes. -/
-- @node: treatedBinary_klDiv_zero_off_support
lemma treatedBinary_klDiv_zero_off_support (d : ℕ) (β δ h M : ℝ)
    (hh : 0 < h) (x : Fin d → ℝ) (i : Fin d) (hi : h / 2 ≤ x i) :
    klDiv (binaryMeasure M (treatedPlusProbability d β δ h M true x))
      (binaryMeasure M (treatedPlusProbability d β δ h M false x)) = 0 := by
  rw [treatedPlusProbability_off_support d β δ h M true hh x i hi,
    treatedPlusProbability_off_support d β δ h M false hh x i hi]
  have := binaryMeasure_isProbabilityMeasure M (1 / 2) (by norm_num)
  exact klDiv_self _

/-- In a lower cube of width `h`, the baseline propensity is bounded by `h^(d/q)`. -/
-- @node: baselinePropensity_le_on_lower_cube
lemma baselinePropensity_le_on_lower_cube (d : ℕ) (q h : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (x : Fin d → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) h) :
    baselinePropensity d q x ≤ h ^ ((d : ℝ) / q) := by
  have hbounded : BddAbove (Set.range x) :=
    ⟨h, by rintro y ⟨i, rfl⟩; exact (hx i).2⟩
  have hmax0 : 0 ≤ maxCoordinate x := by
    exact (hx ⟨0, hd⟩).1.trans (le_csSup hbounded ⟨⟨0, hd⟩, rfl⟩)
  have hmaxh : maxCoordinate x ≤ h := by
    exact csSup_le ⟨x ⟨0, hd⟩, ⟨⟨0, hd⟩, rfl⟩⟩
      (by rintro y ⟨i, rfl⟩; exact (hx i).2)
  exact Real.rpow_le_rpow hmax0 hmaxh (by positivity)

/-- The integrated treated-channel divergence has the localized exponent `2β + D`.
This is the information term in the one-observation KL chain rule; the enclosing
observed-law disintegration is a separate step. -/
-- @node: treatedBinary_integrated_klDiv_le
lemma treatedBinary_integrated_klDiv_le (d : ℕ) (β γ δ h M : ℝ)
    (hd : 1 ≤ d) (hβ : 0 < β) (hγ : 1 < γ) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4) :
    (∫⁻ x in cube d, ENNReal.ofReal (baselinePropensity d (tailExponent γ) x) *
      klDiv (binaryMeasure M (treatedPlusProbability d β δ h M true x))
        (binaryMeasure M (treatedPlusProbability d β δ h M false x))) ≤
      ENNReal.ofReal (16 * δ ^ 2 / M ^ 2 * h ^ (2 * β + effectiveDimension d γ)) := by
  classical
  let B : Set (Fin d → ℝ) := Set.univ.pi (fun _ => Set.Icc (0 : ℝ) h)
  let T : ℝ := h ^ ((d : ℝ) / tailExponent γ) *
    (16 * δ ^ 2 / M ^ 2 * h ^ (2 * β))
  have hq : 0 < tailExponent γ := by unfold tailExponent; linarith
  have hBmeas : MeasurableSet B := by dsimp [B]; simp
  have hBcube : B ⊆ cube d := by
    intro x hx i hi
    exact ⟨(hx i hi).1, (hx i hi).2.trans hh1⟩
  have hpoint : ∀ x ∈ cube d,
      ENNReal.ofReal (baselinePropensity d (tailExponent γ) x) *
        klDiv (binaryMeasure M (treatedPlusProbability d β δ h M true x))
          (binaryMeasure M (treatedPlusProbability d β δ h M false x)) ≤
      B.indicator (fun _ => ENNReal.ofReal T) x := by
    intro x hx
    by_cases hxB : x ∈ B
    · rw [Set.indicator_of_mem hxB]
      have he := baselinePropensity_le_on_lower_cube d (tailExponent γ) h hd hq x
        (fun i => hxB i (Set.mem_univ i))
      have hk := treatedBinary_klDiv_le_amplitude_sq d β δ h M
        hβ hδ hh hh1 hM hsmall x hx
      calc
        _ ≤ ENNReal.ofReal (h ^ ((d : ℝ) / tailExponent γ)) *
            ENNReal.ofReal (16 * δ ^ 2 / M ^ 2 * h ^ (2 * β)) :=
          mul_le_mul (ENNReal.ofReal_le_ofReal he) hk (by positivity) (by positivity)
        _ = ENNReal.ofReal T := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hh.le _)]
    · have hex : ∃ i, h < x i := by
        by_contra hnot
        apply hxB
        intro i hi
        exact ⟨(hx i hi).1, le_of_not_gt (fun hlt => hnot ⟨i, hlt⟩)⟩
      obtain ⟨i, hi⟩ := hex
      have hzero := treatedBinary_klDiv_zero_off_support d β δ h M hh x i
        (by linarith)
      rw [hzero, mul_zero]
      exact bot_le
  calc
    _ ≤ ∫⁻ x in cube d, B.indicator (fun _ => ENNReal.ofReal T) x := by
      apply setLIntegral_mono' (by simp [cube])
      exact hpoint
    _ = ENNReal.ofReal T * volume B := by
      rw [lintegral_indicator_const hBmeas, Measure.restrict_apply hBmeas,
        Set.inter_eq_left.mpr hBcube]
    _ = ENNReal.ofReal (T * h ^ d) := by
      have hvol : volume B = ENNReal.ofReal (h ^ d) := by
        dsimp [B]
        rw [show Set.univ.pi (fun _ : Fin d => Set.Icc (0 : ℝ) h) =
          Set.Icc (fun _ => (0 : ℝ)) (fun _ => h) by ext x; simp]
        rw [Real.volume_Icc_pi]
        simp only [sub_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact (ENNReal.ofReal_pow hh.le d).symm
      rw [hvol, ← ENNReal.ofReal_mul (by dsimp [T]; positivity)]
    _ = ENNReal.ofReal (16 * δ ^ 2 / M ^ 2 *
        h ^ (2 * β + effectiveDimension d γ)) := by
      congr 1
      have hD : effectiveDimension d γ = (d : ℝ) / tailExponent γ + d := by
        unfold effectiveDimension tailExponent
        have hne : γ - 1 ≠ 0 := by linarith
        field_simp [hne]
        ring
      rw [hD, ← Real.rpow_natCast h d]
      dsimp [T]
      rw [mul_comm (h ^ ((d : ℝ) / tailExponent γ)), mul_assoc,
        ← Real.rpow_add hh, mul_assoc, ← Real.rpow_add hh]

/-- A measurable almost-everywhere property propagates through a bound measure.
The inequality version also works when the measure-valued map is not measurable. -/
-- @node: ae_bind_of_ae_fibres
lemma ae_bind_of_ae_fibres {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    (μ : Measure α) (κ : α → Measure Ω) (p : Ω → Prop)
    (hp : MeasurableSet {z | p z}) (h : ∀ᵐ x ∂μ, ∀ᵐ z ∂κ x, p z) :
    ∀ᵐ z ∂μ.bind κ, p z := by
  have hz : ∀ᵐ x ∂μ, κ x {z | ¬ p z} = 0 :=
    h.mono (fun x hx => ae_iff.mp hx)
  rw [ae_iff]
  apply le_antisymm _ bot_le
  calc
    _ ≤ ∫⁻ x, κ x {z | ¬ p z} ∂μ := Measure.bind_apply_le κ hp.compl
    _ = 0 := by
      rw [lintegral_congr_ae hz]
      simp

/-- The full witness construction preserves the bounded support of both binary
potential outcomes through all three conditional sampling steps. -/
-- @node: lowerPair_boundedOutcomes
lemma lowerPair_boundedOutcomes (d : ℕ) (β q h δ M : ℝ)
    (hM : 0 ≤ M) (sign : Bool) :
    BoundedOutcomes (lowerPair d β q h δ M sign) M := by
  unfold BoundedOutcomes lowerPair
  dsimp only
  have hset : MeasurableSet {u : Full d | |u.2.2.1| ≤ M ∧ |u.2.2.2| ≤ M} := by
    measurability
  apply ae_bind_of_ae_fibres _ _ _ hset
  apply Filter.Eventually.of_forall
  intro x
  apply ae_bind_of_ae_fibres _ _ _ hset
  apply Filter.Eventually.of_forall
  intro a
  apply ae_bind_of_ae_fibres _ _ _ hset
  filter_upwards [binaryMeasure_ae_bounded M (1 / 2) hM] with y0 hy0
  apply (ae_map_iff (by fun_prop) hset).mpr
  filter_upwards [binaryMeasure_ae_bounded M
    (treatedPlusProbability d β δ h M sign x) hM] with y1 hy1
  exact ⟨hy0, hy1⟩

/-- Consistency transfers the bounded potential outcomes to the observed response. -/
-- @node: lowerPair_observed_bounded
lemma lowerPair_observed_bounded (d : ℕ) (β q h δ M : ℝ)
    (hM : 0 ≤ M) (sign : Bool) :
    ∀ᵐ z ∂(lowerPair d β q h δ M sign).obs, |z.2.2| ≤ M := by
  rw [(lowerPair_consistency d β q h δ M sign).2]
  have ho : Measurable (observe (d := d)) := by
    unfold observe
    apply Measurable.prodMk (by fun_prop)
    apply Measurable.prodMk (by fun_prop)
    apply Measurable.ite _ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton true).preimage (by fun_prop)
  apply (ae_map_iff ho.aemeasurable
    (by measurability : MeasurableSet {z : Obs d | |z.2.2| ≤ M})).mpr
  filter_upwards [lowerPair_boundedOutcomes d β q h δ M hM sign] with u hu
  change |if u.2.1 then u.2.2.2 else u.2.2.1| ≤ M
  split_ifs
  · exact hu.2
  · exact hu.1

end CausalSmith.Stat.GlobalTailDesignRobustCate

module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BlockPrior
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Square-root baseline derivative and translation energy

The compactly supported cosine square root has a supported sine derivative.
Its integral representation, interval Cauchy–Schwarz, and Fubini yield the sharp
quadratic translation bound used by the block-testing construction.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Clamping to the support interval expresses the square-root density as a cosine,
including its zero endpoint values.  [For the stated data and conditions](hyp:w), [the stated conclusion holds](goal). -/
-- @node: sqrt_cosSqDensity_eq_clamped_cos
lemma sqrt_cosSqDensity_eq_clamped_cos (w : ℝ) :
    Real.sqrt (cosSqDensity w) =
      2 * Real.cos (2 * Real.pi * max (-1 / 4) (min (1 / 4) w)) := by
  by_cases hw : |w| ≤ 1 / 4
  · have hb := abs_le.mp hw
    rw [min_eq_right hb.2, max_eq_right (by linarith : (-1 / 4 : ℝ) ≤ w), cosSqDensity, if_pos hw]
    have hc : 0 ≤ Real.cos (2 * Real.pi * w) := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor <;> nlinarith [Real.pi_pos]
    have hs : 4 * Real.cos (2 * Real.pi * w) ^ 2 =
        (2 * Real.cos (2 * Real.pi * w)) ^ 2 := by ring
    rw [hs, Real.sqrt_sq (mul_nonneg (by norm_num) hc)]
  · rw [cosSqDensity, if_neg hw, Real.sqrt_zero]
    rcases lt_or_ge w (-1 / 4) with hlow | hlow
    · rw [min_eq_right (by linarith : w ≤ (1 / 4 : ℝ)), max_eq_left hlow.le]
      have he : 2 * Real.pi * (-1 / 4 : ℝ) = -(Real.pi / 2) := by ring
      rw [he, Real.cos_neg, Real.cos_pi_div_two, mul_zero]
    · have hhigh : (1 / 4 : ℝ) ≤ w := by
        by_contra hh
        exact hw (abs_le.mpr ⟨by linarith, le_of_not_ge hh⟩)
      rw [min_eq_left hhigh, max_eq_right (by norm_num : (-1 / 4 : ℝ) ≤ 1 / 4)]
      have he : 2 * Real.pi * (1 / 4 : ℝ) = Real.pi / 2 := by ring
      rw [he, Real.cos_pi_div_two, mul_zero]

/-- The square-root baseline is globally four-pi Lipschitz, including across the
boundary of its compact support.  [the stated conclusion holds](goal). -/
-- @node: baseline_sqrt_lipschitz
lemma baseline_sqrt_lipschitz :
    LipschitzWith ((4 * Real.pi).toNNReal) (fun w => Real.sqrt (cosSqDensity w)) := by
  have hclamp : LipschitzWith 1 (fun w : ℝ => max (-1 / 4) (min (1 / 4) w)) :=
    (LipschitzWith.id.const_min (1 / 4)).const_max (-1 / 4)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [sqrt_cosSqDensity_eq_clamped_cos, sqrt_cosSqDensity_eq_clamped_cos,
    Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
  have hc := hclamp.dist_le_mul x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hc
  calc
    |2 * Real.cos (2 * Real.pi * max (-1 / 4) (min (1 / 4) x)) -
        2 * Real.cos (2 * Real.pi * max (-1 / 4) (min (1 / 4) y))| =
        2 * |Real.cos (2 * Real.pi * max (-1 / 4) (min (1 / 4) x)) -
          Real.cos (2 * Real.pi * max (-1 / 4) (min (1 / 4) y))| := by
            rw [← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2 * |2 * Real.pi * max (-1 / 4) (min (1 / 4) x) -
        2 * Real.pi * max (-1 / 4) (min (1 / 4) y)| :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_sub_cos_le _ _) (by norm_num)
    _ = 4 * Real.pi * |max (-1 / 4) (min (1 / 4) x) -
        max (-1 / 4) (min (1 / 4) y)| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
      ring
    _ ≤ 4 * Real.pi * |x - y| := mul_le_mul_of_nonneg_left hc (by positivity)

/-- Direct integration of the squared interior derivative gives four pi squared.  [the stated conclusion holds](goal). -/
-- @node: baseline_derivative_energy
lemma baseline_derivative_energy :
    (∫ w in Set.Icc (-1 / 4 : ℝ) (1 / 4),
      (4 * Real.pi * Real.sin (2 * Real.pi * w)) ^ 2) = 4 * Real.pi ^ 2 := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 / 4 : ℝ) ≤ 1 / 4)]
  simp_rw [mul_pow]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x ^ 2)
    (by positivity : 2 * Real.pi ≠ 0)]
  rw [integral_sin_sq]
  have hl : 2 * Real.pi * (-1 / 4 : ℝ) = -(Real.pi / 2) := by ring
  have hu : 2 * Real.pi * (1 / 4 : ℝ) = Real.pi / 2 := by ring
  simp only [hl, hu, Real.cos_neg, Real.cos_pi_div_two, mul_zero, sub_zero,
    smul_eq_mul]
  field_simp
  ring

/-- Cauchy–Schwarz on a finite measure bounds the squared integral by mass times energy.  [For the stated data and conditions](hyp:α,μ,g,hg,hg2), [the stated conclusion holds](goal). -/
-- @node: baseline_interval_cauchy_schwarz
lemma baseline_interval_cauchy_schwarz {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (g : α → ℝ) (hg : Integrable g μ) (hg2 : Integrable (fun x => g x ^ 2) μ) :
    (∫ x, g x ∂μ) ^ 2 ≤ μ.real Set.univ * ∫ x, g x ^ 2 ∂μ := by
  let m := μ.real Set.univ
  let I := ∫ x, g x ∂μ
  have hm0 : 0 ≤ m := measureReal_nonneg
  by_cases hm : m = 0
  · have hμ : μ = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      exact ((ENNReal.toReal_eq_zero_iff _).mp hm).resolve_right (measure_ne_top μ Set.univ)
    simp [hμ]
  · have hmp : 0 < m := lt_of_le_of_ne hm0 (Ne.symm hm)
    have hex : (fun x => (m * g x - I) ^ 2) =
        (fun x => m ^ 2 * g x ^ 2 - (2 * m * I) * g x + I ^ 2) := by
      funext x; ring
    have hn : 0 ≤ ∫ x, (m * g x - I) ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
    rw [hex] at hn
    have hs : Integrable (fun x => m ^ 2 * g x ^ 2 - (2 * m * I) * g x) μ :=
      (hg2.const_mul _).sub (hg.const_mul _)
    rw [integral_add hs (integrable_const (I ^ 2)),
      integral_sub (hg2.const_mul (m ^ 2)) (hg.const_mul (2 * m * I)),
      integral_const_mul, integral_const_mul, integral_const] at hn
    change 0 ≤ m ^ 2 * (∫ x, g x ^ 2 ∂μ) - (2 * m * I) * I + m * I ^ 2 at hn
    have hx : 0 ≤ m * (m * (∫ x, g x ^ 2 ∂μ) - I ^ 2) := by nlinarith [hn]
    have := nonneg_of_mul_nonneg_right hx hmp
    dsimp [m, I] at this
    linarith

/-- Integrating the interval Cauchy–Schwarz bound and applying Fubini controls translation energy by derivative energy.  [For the stated data and conditions](hyp:f,g,hg,hgi,hg2,hrep,a,b,hab), [the stated conclusion holds](goal). -/
-- @node: translation_energy_le_of_integral_representation
lemma translation_energy_le_of_integral_representation (f g : ℝ → ℝ) (hg : Measurable g) (hgi : Integrable g)
    (hg2 : Integrable (fun x => g x ^ 2))
    (hrep : ∀ a b, a ≤ b → (∫ x in a..b, g x) = f b - f a)
    (a b : ℝ) (hab : a ≤ b) :
    (∫ w, (f (w + b) - f (w + a)) ^ 2) ≤
      (b - a) ^ 2 * (∫ w, g w ^ 2) := by
  let ν := volume.restrict (Set.Ioc a b)
  have hν : IsFiniteMeasure ν := inferInstance
  have hprod : Integrable (fun p : ℝ × ℝ => g (p.1 + p.2) ^ 2) (volume.prod ν) := by
    apply (integrable_prod_iff' ((hg.comp (measurable_fst.add measurable_snd)).pow_const 2).aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall (fun v => hg2.comp_add_right v), ?_⟩
    have he : (fun v => ∫ w, ‖g (w + v) ^ 2‖) = (fun _ : ℝ => ∫ w, g w ^ 2) := by
      funext v
      simp only [Real.norm_eq_abs, abs_sq]
      exact integral_add_right_eq_self (fun w => g w ^ 2) v
    change Integrable (fun v => ∫ w, ‖g (w + v) ^ 2‖) ν
    rw [he]
    exact integrable_const _
  have hpoint (w : ℝ) : (f (w + b) - f (w + a)) ^ 2 ≤
      (b - a) * ∫ v, g (w + v) ^ 2 ∂ν := by
    have hi : Integrable (fun v => g (w + v)) ν :=
      (hgi.comp_add_left w).restrict
    have hi2 : Integrable (fun v => g (w + v) ^ 2) ν :=
      (hg2.comp_add_left w).restrict
    have he : (∫ v, g (w + v) ∂ν) = f (w + b) - f (w + a) := by
      rw [← intervalIntegral.integral_of_le hab,
        intervalIntegral.integral_comp_add_left g w]
      exact hrep _ _ (add_le_add_right hab w)
    have hc := baseline_interval_cauchy_schwarz ν (fun v => g (w + v)) hi hi2
    rw [he] at hc
    simpa [ν, measureReal_restrict_apply, Real.volume_real_Ioc_of_le hab] using hc
  calc
    (∫ w, (f (w + b) - f (w + a)) ^ 2) ≤
        ∫ w, (b - a) * ∫ v, g (w + v) ^ 2 ∂ν :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        (hprod.integral_prod_left.const_mul _) (Filter.Eventually.of_forall hpoint)
    _ = (b - a) ^ 2 * (∫ w, g w ^ 2) := by
      rw [integral_const_mul, integral_integral_swap hprod]
      simp_rw [integral_add_right_eq_self (fun w => g w ^ 2)]
      simp [ν, measureReal_restrict_apply, Real.volume_real_Ioc_of_le hab, pow_two, mul_assoc]

/-- The supported interior derivative of the square-root cosine baseline; endpoint values are immaterial to integration. -/
-- @node: baselineSqrtDerivative
def baselineSqrtDerivative (w : ℝ) : ℝ :=
  (Set.Icc (-1 / 4 : ℝ) (1 / 4)).indicator (fun w => -4 * Real.pi * Real.sin (2 * Real.pi * w)) w

/-- The supported derivative and its square are integrable by compact support.  [the stated conclusion holds](goal). -/
-- @node: baselineSqrtDerivative_integrable
lemma baselineSqrtDerivative_integrable : Integrable baselineSqrtDerivative ∧ Integrable (fun w => baselineSqrtDerivative w ^ 2) := by
  have hc : Continuous (fun w : ℝ => -4 * Real.pi * Real.sin (2 * Real.pi * w)) := by fun_prop
  constructor
  · exact (integrable_indicator_iff measurableSet_Icc).mpr hc.continuousOn.integrableOn_Icc
  · have he : (fun w => baselineSqrtDerivative w ^ 2) =
        (Set.Icc (-1 / 4 : ℝ) (1 / 4)).indicator
          (fun w => (-4 * Real.pi * Real.sin (2 * Real.pi * w)) ^ 2) := by
      funext w
      by_cases hw : w ∈ Set.Icc (-1 / 4 : ℝ) (1 / 4)
      · simp only [baselineSqrtDerivative, Set.indicator_of_mem hw]
      · simp only [baselineSqrtDerivative, Set.indicator_of_notMem hw, zero_pow, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true]
    rw [he]
    exact (integrable_indicator_iff measurableSet_Icc).mpr
      (hc.pow 2).continuousOn.integrableOn_Icc

/-- The supported derivative has total squared energy four pi squared.  [the stated conclusion holds](goal). -/
-- @node: baselineSqrtDerivative_energy
lemma baselineSqrtDerivative_energy : (∫ w, baselineSqrtDerivative w ^ 2) = 4 * Real.pi ^ 2 := by
  have he : (fun w => baselineSqrtDerivative w ^ 2) =
      (Set.Icc (-1 / 4 : ℝ) (1 / 4)).indicator
        (fun w => (4 * Real.pi * Real.sin (2 * Real.pi * w)) ^ 2) := by
    funext w
    by_cases hw : w ∈ Set.Icc (-1 / 4 : ℝ) (1 / 4)
    · simp only [baselineSqrtDerivative, Set.indicator_of_mem hw]; ring
    · simp only [baselineSqrtDerivative, Set.indicator_of_notMem hw, zero_pow, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true]
  rw [he, integral_indicator measurableSet_Icc]
  exact baseline_derivative_energy

/-- Integration of the supported derivative recovers square-root baseline increments, including across the support boundaries.  [For the stated data and conditions](hyp:a,b,hab), [the stated conclusion holds](goal). -/
-- @node: baselineSqrtDerivative_integral
lemma baselineSqrtDerivative_integral (a b : ℝ) (hab : a ≤ b) :
    (∫ w in a..b, baselineSqrtDerivative w) =
      Real.sqrt (cosSqDensity b) - Real.sqrt (cosSqDensity a) := by
  have he : (∫ w in a..b, baselineSqrtDerivative w) =
      ∫ w in Set.Icc (max (-1 / 4) a) (min (1 / 4) b),
        -4 * Real.pi * Real.sin (2 * Real.pi * w) := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    unfold baselineSqrtDerivative
    rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
      Set.Icc_inter_Icc]
  rw [he, sqrt_cosSqDensity_eq_clamped_cos, sqrt_cosSqDensity_eq_clamped_cos]
  rcases lt_or_ge b (-1 / 4) with hb | hb
  · have hempty : Set.Icc (max (-1 / 4 : ℝ) a) (min (1 / 4) b) = ∅ :=
      Set.Icc_eq_empty_of_lt (lt_of_le_of_lt (min_le_right _ _) (hb.trans_le (le_max_left _ _)))
    rw [hempty]
    simp only [Measure.restrict_empty, integral_zero_measure]
    rw [min_eq_right (by linarith : b ≤ (1 / 4 : ℝ)),
      max_eq_left hb.le, min_eq_right (by linarith : a ≤ (1 / 4 : ℝ)),
      max_eq_left (by linarith : a ≤ (-1 / 4 : ℝ))]
    ring
  rcases lt_or_ge (1 / 4 : ℝ) a with ha | ha
  · have hempty : Set.Icc (max (-1 / 4 : ℝ) a) (min (1 / 4) b) = ∅ :=
      Set.Icc_eq_empty_of_lt (lt_of_le_of_lt (min_le_left _ _) (ha.trans_le (le_max_right _ _)))
    rw [hempty]
    simp only [Measure.restrict_empty, integral_zero_measure]
    rw [min_eq_left (by linarith : (1 / 4 : ℝ) ≤ b),
      max_eq_right (by norm_num : (-1 / 4 : ℝ) ≤ 1 / 4), min_eq_left ha.le,
      max_eq_right (by norm_num : (-1 / 4 : ℝ) ≤ 1 / 4)]
    ring
  have hLU : max (-1 / 4 : ℝ) a ≤ min (1 / 4) b := by
    exact max_le (le_min (by norm_num) hb) (le_min ha hab)
  rw [min_eq_right ha, max_eq_right (le_min (by norm_num) hb),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hLU]
  rw [max_comm (-1 / 4 : ℝ) a]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun w => 2 * Real.cos (2 * Real.pi * w))
  · intro w hw
    convert ((Real.hasDerivAt_cos (2 * Real.pi * w)).comp w
      ((hasDerivAt_id w).const_mul (2 * Real.pi))).const_mul 2 using 1 <;> first | rfl | ring
  · exact (show Continuous (fun w : ℝ => -4 * Real.pi * Real.sin (2 * Real.pi * w)) by
      fun_prop).intervalIntegrable _ _

/-- The square-root baseline translation energy is bounded by four pi squared times the squared shift difference.  [For the stated data and conditions](hyp:s,t), [the stated conclusion holds](goal). -/
-- @node: baseline_translation_energy
lemma baseline_translation_energy (s t : ℝ) :
    (∫ w, (Real.sqrt (cosSqDensity (w - s)) - Real.sqrt (cosSqDensity (w - t))) ^ 2) ≤
      4 * Real.pi ^ 2 * (s - t) ^ 2 := by
  have hmeas : Measurable baselineSqrtDerivative := by
    unfold baselineSqrtDerivative
    have hs : MeasurableSet (Set.Icc (-1 / 4 : ℝ) (1 / 4)) := measurableSet_Icc
    fun_prop
  have hle (s t : ℝ) (hst : t ≤ s) :
      (∫ w, (Real.sqrt (cosSqDensity (w - s)) - Real.sqrt (cosSqDensity (w - t))) ^ 2) ≤
        4 * Real.pi ^ 2 * (s - t) ^ 2 := by
    have hx := translation_energy_le_of_integral_representation (fun w => Real.sqrt (cosSqDensity w)) baselineSqrtDerivative
      hmeas baselineSqrtDerivative_integrable.1 baselineSqrtDerivative_integrable.2 baselineSqrtDerivative_integral (-s) (-t) (by linarith)
    rw [baselineSqrtDerivative_energy] at hx
    simp only [← sub_eq_add_neg] at hx
    have he : (fun w => (Real.sqrt (cosSqDensity (w - s)) -
        Real.sqrt (cosSqDensity (w - t))) ^ 2) =
        (fun w => (Real.sqrt (cosSqDensity (w - t)) -
        Real.sqrt (cosSqDensity (w - s))) ^ 2) := by
      funext w; ring
    rw [he]
    convert hx using 1 <;> ring
  rcases le_total t s with h | h
  · exact hle s t h
  · have hx := hle t s h
    have he : (fun w => (Real.sqrt (cosSqDensity (w - s)) -
        Real.sqrt (cosSqDensity (w - t))) ^ 2) =
        (fun w => (Real.sqrt (cosSqDensity (w - t)) -
        Real.sqrt (cosSqDensity (w - s))) ^ 2) := by
      funext w; ring
    rw [he]
    convert hx using 1 <;> ring

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier

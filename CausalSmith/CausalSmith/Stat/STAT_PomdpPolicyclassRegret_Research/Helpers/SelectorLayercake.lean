module
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Integrating the selector's bias-shifted regret tail

The positive excess over the bias converts equation (11) into an expectation
bound without conditioning or independence assumptions. The low-threshold
part contributes at most one standard deviation; the remaining integral is
exactly the polynomial median tail to be evaluated in equation (12).
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory
open scoped ENNReal

/-- Positive excess is integrable whenever the underlying regret is. For
[the sample space](hyp:Ω), [the measure](hyp:μ), [the r](hyp:R), [the behavior policy](hyp:b),
and [the r assumption](hyp:hR), this establishes
[the selector excess integrability result](goal). -/
-- @node: selector_excess_integrable
lemma selector_excess_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → ℝ) (b : ℝ)
    (hR : Integrable R μ) :
    Integrable (fun w ↦ max 0 (R w / 2 - b)) μ := by
  exact (integrable_const (0 : ℝ)).sup ((hR.div_const 2).sub (integrable_const b))

/-- The excess has exactly the bias-shifted regret tail on positive thresholds. For
[the sample space](hyp:Ω), [the measure](hyp:μ), [the r](hyp:R), [the behavior policy](hyp:b),
and [the r assumption](hyp:hR), this establishes [the selector excess layercake result](goal). -/
-- @node: selector_excess_layercake
lemma selector_excess_layercake {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → ℝ) (b : ℝ)
    (hR : Integrable R μ) :
    ENNReal.ofReal (∫ w, max 0 (R w / 2 - b) ∂μ) =
      ∫⁻ x : ℝ in Set.Ioi 0, μ {w | 2 * (b + x) < R w} := by
  have hF := selector_excess_integrable μ R b hR
  rw [ofReal_integral_eq_lintegral_ofReal hF
    (Filter.Eventually.of_forall fun w ↦ le_max_left _ _)]
  rw [lintegral_eq_lintegral_meas_lt (f := fun w ↦ max 0 (R w / 2 - b)) μ
    (Filter.Eventually.of_forall fun w ↦ le_max_left _ _) hF.aemeasurable]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  congr 1
  ext w
  have hx0 : 0 < x := hx
  simp only [Set.mem_setOf_eq, lt_max_iff]
  constructor
  · rintro (h | h)
    · linarith
    · linarith
  · intro h
    right
    linarith

/-- Deterministic argmax comparison followed by integration contributes twice both the bias and
the positive excess. For [the sample space](hyp:Ω), [the measure](hyp:μ), [the r](hyp:R),
[the behavior policy](hyp:b), and [the r assumption](hyp:hR), this establishes
[the selector integral bound bias excess result](goal). -/
-- @node: selector_integral_le_bias_excess
lemma selector_integral_le_bias_excess {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → ℝ) (b : ℝ)
    (hR : Integrable R μ) :
    (∫ w, R w ∂μ) ≤ 2 * b + 2 * ∫ w, max 0 (R w / 2 - b) ∂μ := by
  have hF := selector_excess_integrable μ R b hR
  calc
    _ ≤ ∫ w, (2 * b + 2 * max 0 (R w / 2 - b)) ∂μ := by
      apply integral_mono hR ((integrable_const _).add (hF.const_mul 2))
      intro w
      change R w ≤ 2 * b + 2 * max 0 (R w / 2 - b)
      have := le_max_right (0 : ℝ) (R w / 2 - b)
      linarith
    _ = _ := by rw [integral_add (integrable_const _) (hF.const_mul 2),
      integral_const_mul, integral_const_mul]; simp

/-- Split layer-cake at a nonnegative threshold. The probability cap bounds the initial
interval; any valid large-threshold tail bounds the remainder. For [the sample space](hyp:Ω),
[the measure](hyp:μ), [the r](hyp:R), [the behavior policy](hyp:b), [the σ](hyp:σ),
[the h](hyp:H), [the r assumption](hyp:hR), [the σ assumption](hyp:hσ), and
[the tail assumption](hyp:htail), this establishes
[the selector excess layercake bound result](goal). -/
-- @node: selector_excess_layercake_bound
lemma selector_excess_layercake_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → ℝ) (b σ : ℝ)
    (H : ℝ → ℝ≥0∞) (hR : Integrable R μ) (hσ : 0 ≤ σ)
    (htail : ∀ x, 0 < x → σ ≤ x → μ {w | 2 * (b + x) < R w} ≤ H x) :
    ENNReal.ofReal (∫ w, max 0 (R w / 2 - b) ∂μ) ≤
      ENNReal.ofReal σ + ∫⁻ x : ℝ in Set.Ioi σ, H x := by
  rw [selector_excess_layercake μ R b hR]
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 σ ∪ Set.Ioi σ := by
    ext x
    simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro hx
      by_cases h : x ≤ σ
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr (lt_of_not_ge h)
    · rintro (⟨hx, _⟩ | hx)
      · exact hx
      · exact hσ.trans_lt hx
  rw [hsplit]
  apply (lintegral_union_le _ _ _).trans
  apply add_le_add
  · calc
      _ ≤ ∫⁻ _x : ℝ in Set.Ioc 0 σ, (1 : ℝ≥0∞) :=
        lintegral_mono fun x ↦ prob_le_one
      _ = ENNReal.ofReal σ := by simp [Real.volume_Ioc]
  · apply setLIntegral_mono' measurableSet_Ioi
    intro x hx
    exact htail x (hσ.trans_lt hx) hx.le

/-- An inverse-square envelope above its own scale has total tail area equal to that scale. This
provides a uniform, finite expectation bound. For [the action](hyp:a) and
[the action assumption](hyp:ha), this establishes
[the selector inverse square tail integral result](goal). -/
-- @node: selector_inverse_square_tail_integral
lemma selector_inverse_square_tail_integral (a : ℝ) (ha : 0 < a) :
    (∫⁻ x : ℝ in Set.Ioi a, ENNReal.ofReal ((a / x) ^ 2)) =
      ENNReal.ofReal a := by
  have heq : ∀ x : ℝ, 0 ≤ x → (a / x) ^ 2 = a ^ 2 * x ^ (-2 : ℝ) := by
    intro x hx
    rw [div_pow, Real.rpow_neg hx]
    norm_num
    ring
  have hi : IntegrableOn (fun x : ℝ ↦ a ^ 2 * x ^ (-2 : ℝ)) (Set.Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha).const_mul _
  have hl : (∫⁻ x : ℝ in Set.Ioi a, ENNReal.ofReal ((a / x) ^ 2)) =
      ∫⁻ x : ℝ in Set.Ioi a, ENNReal.ofReal (a ^ 2 * x ^ (-2 : ℝ)) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact congrArg ENNReal.ofReal (heq x (ha.trans hx).le)
  rw [hl, ← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) ha]
    norm_num
    rw [Real.rpow_neg_one]
    congr 1
    field_simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (sq_nonneg a) (Real.rpow_nonneg (ha.trans hx).le _)

/-- Integrating an inverse-square upper envelope gives a linear expected regret bound in its
scale, with no boundedness premise on the random variable. For [the sample space](hyp:Ω),
[the measure](hyp:μ), [the r](hyp:R), [the behavior policy](hyp:b), [the action](hyp:a),
[the r assumption](hyp:hR), [the action assumption](hyp:ha), and
[the tail assumption](hyp:htail), this establishes
[the selector integral bound of square tail result](goal). -/
-- @node: selector_integral_le_of_square_tail
lemma selector_integral_le_of_square_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → ℝ) (b a : ℝ)
    (hR : Integrable R μ) (ha : 0 < a)
    (htail : ∀ x, a ≤ x → μ {w | 2 * (b + x) < R w} ≤
      ENNReal.ofReal ((a / x) ^ 2)) :
    (∫ w, R w ∂μ) ≤ 2 * b + 4 * a := by
  have hF := selector_excess_integrable μ R b hR
  have hbnd := selector_excess_layercake_bound μ R b a
    (fun x ↦ ENNReal.ofReal ((a / x) ^ 2)) hR ha.le
    (fun x _ hx ↦ htail x hx)
  rw [selector_inverse_square_tail_integral a ha,
    ← ENNReal.ofReal_add ha.le ha.le] at hbnd
  have hreal : (∫ w, max 0 (R w / 2 - b) ∂μ) ≤ a + a := by
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ a + a)).mp hbnd
  have hreg := selector_integral_le_bias_excess μ R b hR
  linarith

/-- Above twice e standard deviations, the M-candidate median tail is bounded by an
inverse-square envelope uniformly over the list size. For [the candidate-policy count](hyp:M),
[the second event](hyp:B), [the σ](hyp:σ), [the observed state](hyp:x),
[the candidate-policy count assumption](hyp:hM), [the second event assumption](hyp:hB),
[the log assumption](hyp:hlog), [the σ assumption](hyp:hσ),
[the observed state assumption](hyp:hx), and [the scale assumption](hyp:hscale), this
establishes [the selector median tail square envelope result](goal). -/
-- @node: selector_median_tail_square_envelope
lemma selector_median_tail_square_envelope (M B : Nat) (σ x : ℝ)
    (hM : 0 < M) (hB : 2 ≤ B) (hlog : Real.log (M : ℝ) ≤ B)
    (hσ : 0 ≤ σ) (hx : 0 < x) (hscale : 2 * Real.exp 1 * σ ≤ x) :
    (M : ℝ≥0∞) * ENNReal.ofReal ((2 * σ / x) ^ B) ≤
      ENNReal.ofReal ((2 * Real.exp 1 * σ / x) ^ 2) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hMe : (M : ℝ) ≤ Real.exp 1 ^ B := by
    rw [← Real.exp_nat_mul, mul_one]
    exact (Real.exp_log hMr) ▸ Real.exp_le_exp.mpr hlog
  have hr0 : 0 ≤ 2 * Real.exp 1 * σ / x := by positivity
  have hr1 : 2 * Real.exp 1 * σ / x ≤ 1 := (div_le_one hx).mpr hscale
  have hreal : (M : ℝ) * (2 * σ / x) ^ B ≤
      (2 * Real.exp 1 * σ / x) ^ 2 := by
    calc
      _ ≤ Real.exp 1 ^ B * (2 * σ / x) ^ B :=
        mul_le_mul_of_nonneg_right hMe (by positivity)
      _ = (2 * Real.exp 1 * σ / x) ^ B := by
        rw [← mul_pow]
        congr 1
        ring
      _ ≤ _ := pow_le_pow_of_le_one hr0 hr1 hB
  have hcast : (M : ℝ≥0∞) = ENNReal.ofReal (M : ℝ) := by simp
  rw [hcast, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

end CausalSmith.Stat.PomdpPolicyclassRegret

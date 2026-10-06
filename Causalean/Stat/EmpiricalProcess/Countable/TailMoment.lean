module
public import Causalean.Stat.EmpiricalProcess.Countable.Holder
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fourth-moment tail integration

Layer cake and Tonelli convert a weak tail bound into the mixed fourth-moment
estimate used by Doob. Tail integrals use positive real levels and include
the event boundary; Layercake already justifies the closed-tail convention.
This file has no martingale or empirical-process dependencies.
-/

public section

open MeasureTheory Set
namespace Causalean.Stat.EmpiricalProcess.Countable

/-- Under [a finite measure μ](hyp:μ), if [a real function A](hyp:A) is
[nonnegative](hyp:hA) and [measurable](hyp:hm), [its (n + 1)-st
power](hyp:n) [is integrable](hyp:hi), and [c is a nonnegative
constant](hyp:c,hc), then [the function t ↦ c t^n μ(A ≥ t) is integrable
over the positive levels t, and its integral equals c/(n + 1) times the
integral of A^(n + 1)](goal), the polynomial layer-cake formula. -/
theorem polynomial_tail_identity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A : Ω → ℝ)
    (hA : ∀ x, 0 ≤ A x) (hm : Measurable A) (n : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hi : Integrable (fun x => A x ^ (n + 1)) μ) :
    IntegrableOn (fun t : ℝ => c * t ^ n * μ.real {x | t ≤ A x}) (Ioi 0) ∧
      (c / (n + 1 : ℝ)) * (∫ x, A x ^ (n + 1) ∂μ) =
        ∫ t in Ioi (0 : ℝ), c * t ^ n * μ.real {x | t ≤ A x} := by
  have hp (a : ℝ) : (∫ t in 0..a, c * t ^ n) = c / (n + 1 : ℝ) * a ^ (n + 1) := by
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp only [zero_pow (Nat.succ_ne_zero n), sub_zero]
    ring
  have hn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ c * t ^ n := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg hc (pow_nonneg (le_of_lt ht) _)
  have hl := lintegral_comp_eq_lintegral_meas_le_mul μ
    (Filter.Eventually.of_forall hA) hm.aemeasurable
    (g := fun t => c * t ^ n)
    (fun t _ => (continuous_const.mul (continuous_id.pow n)).intervalIntegrable 0 t) hn
  simp only [hp] at hl
  have hleft := hi.const_mul (c / (n + 1 : ℝ))
  have hln : ∀ x, 0 ≤ c / (n + 1 : ℝ) * A x ^ (n + 1) := fun x =>
    mul_nonneg (div_nonneg hc (by positivity)) (pow_nonneg (hA x) _)
  have htm : Measurable (fun t : ℝ => μ {x | t ≤ A x}) :=
    Antitone.measurable (fun _ _ h => measure_mono (fun _ hx => le_trans h hx))
  have hrm : Measurable (fun t : ℝ => c * t ^ n * μ.real {x | t ≤ A x}) :=
    ((continuous_const.mul (continuous_id.pow n)).measurable).mul htm.ennreal_toReal
  have hrn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      0 ≤ c * t ^ n * μ.real {x | t ≤ A x} := by
    filter_upwards [hn] with t ht using mul_nonneg ht (measureReal_nonneg)
  have he : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
      (c * t ^ n * μ.real {x | t ≤ A x})) =
      ∫⁻ t in Ioi (0 : ℝ), μ {x | t ≤ A x} * ENNReal.ofReal (c * t ^ n) := by
    apply lintegral_congr_ae
    filter_upwards [hn] with t ht
    rw [ENNReal.ofReal_mul ht, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top μ _), mul_comm]
  have hri : IntegrableOn (fun t : ℝ => c * t ^ n * μ.real {x | t ≤ A x}) (Ioi 0) :=
    (lintegral_ofReal_ne_top_iff_integrable hrm.aestronglyMeasurable hrn).1
      (by rw [he, ← hl]; exact hleft.lintegral_lt_top.ne)
  refine ⟨hri, ?_⟩
  rw [← integral_const_mul]
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hln)
    hleft.aestronglyMeasurable, integral_eq_lintegral_of_nonneg_ae hrn hri.aestronglyMeasurable,
    he, ← hl]

/-- Under [a probability measure μ](hyp:μ), if [a real function
A](hyp:A) is [nonnegative](hyp:hA), [measurable](hyp:hm), and [has an
integrable fourth power](hyp:h4), then [the function t ↦ 4 t^3 μ(A ≥ t) is
integrable over the positive levels t, and its integral equals the
expectation of A^4](goal). -/
theorem fourth_tail_identity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → ℝ)
    (hA : ∀ x, 0 ≤ A x) (hm : Measurable A)
    (h4 : Integrable (fun x => A x ^ 4) μ) :
    IntegrableOn (fun t : ℝ => 4 * t ^ 3 * μ.real {x | t ≤ A x}) (Ioi 0) ∧
      (∫ x, A x ^ 4 ∂μ) =
        ∫ t in Ioi (0 : ℝ), 4 * t ^ 3 * μ.real {x | t ≤ A x} := by
  -- Specialize Layercake's lintegral_comp_eq_lintegral_meas_le_mul
  -- to g(t)=4*t^3, whose integral from 0 to a is a^4, and transfer
  -- finite nonnegative lintegrals to real integrals.
  have ht := polynomial_tail_identity μ A hA hm 3 4 (by norm_num) h4
  norm_num at ht
  exact ht

/-- Under [a probability measure μ](hyp:μ), if [two real functions A and
B](hyp:A,B) are [nonnegative](hyp:hA,hB), [A is measurable](hyp:hAm) and [B
almost everywhere strongly measurable](hyp:hBm), and [both have integrable
fourth powers](hyp:hA4,hB4), then [the function t ↦ 4 t^2 times the
integral of B over the event A ≥ t is integrable over the positive levels t,
and its integral equals 4/3 times the expectation of A^3·B](goal). -/
theorem mixed_tail_identity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A B : Ω → ℝ)
    (hA : ∀ x, 0 ≤ A x) (hB : ∀ x, 0 ≤ B x)
    (hAm : Measurable A) (hBm : AEStronglyMeasurable B μ)
    (hA4 : Integrable (fun x => A x ^ 4) μ)
    (hB4 : Integrable (fun x => B x ^ 4) μ) :
    IntegrableOn (fun t : ℝ => 4 * t ^ 2 * ∫ x in {x | t ≤ A x}, B x ∂μ)
      (Ioi 0) ∧
    (∫ t in Ioi (0 : ℝ), 4 * t ^ 2 * ∫ x in {x | t ≤ A x}, B x ∂μ) =
      (4 / 3 : ℝ) * ∫ x, A x ^ 3 * B x ∂μ := by
  -- Apply polynomial Layercake to the finite measure with density B.
  -- The withDensity integral formula supplies the mixed moment; Holder
  -- makes it finite, permitting conversion to legal real tail integrals.
  have hBi : Integrable B μ := by
    have hn4 : Integrable (fun x => ‖B x‖ ^ 4) μ := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hB _)] using hB4
    have hn1 := integrable_norm_pow_of_le hBm (p := 1) (by norm_num : 1 ≤ 4) hn4
    simpa only [pow_one, Real.norm_eq_abs, abs_of_nonneg (hB _)] using hn1
  let ν := μ.withDensity (fun x => ENNReal.ofReal (B x))
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hBi.hasFiniteIntegral
  have hdm : AEMeasurable (fun x => ENNReal.ofReal (B x)) μ := hBm.aemeasurable.ennreal_ofReal
  have hdtop : ∀ᵐ x ∂μ, ENNReal.ofReal (B x) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hmix := (fourth_moment_holder μ A B hA hB hA4 hB4
    hAm.aestronglyMeasurable hBm).1
  have hc : Integrable (fun x => A x ^ 3) ν := by
    apply (integrable_withDensity_iff_integrable_smul₀' hdm hdtop).2
    simpa only [ENNReal.toReal_ofReal (hB _), smul_eq_mul, mul_comm] using hmix
  have htail (t : ℝ) : ν.real {x | t ≤ A x} = ∫ x in {x | t ≤ A x}, B x ∂μ := by
    rw [measureReal_def, withDensity_apply _ (measurableSet_le measurable_const hAm)]
    exact (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hB)
      hBm.restrict).symm
  have hv : (∫ x, A x ^ 3 ∂ν) = ∫ x, A x ^ 3 * B x ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul₀ hdm hdtop]
    simp only [ENNReal.toReal_ofReal (hB _), smul_eq_mul, mul_comm]
  have ht := polynomial_tail_identity ν A hA hAm 2 4 (by norm_num) hc
  simp only [htail, hv] at ht
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at ht
  exact ⟨ht.1, ht.2.symm⟩

/-- Under [a probability measure μ](hyp:μ), let [two real functions A and
B](hyp:A,B) be [nonnegative](hyp:hA,hB), with [A measurable](hyp:hAm) and
[B almost everywhere strongly measurable](hyp:hBm), and [both with
integrable fourth powers](hyp:hA4,hB4). If [for every positive level t, t
times the probability that A ≥ t is at most the integral of B over that
event](hyp:hweak), then [the expectation of A^4 is at most 4/3 times the
expectation of A^3·B](goal). -/
theorem weak_fourth_mixed {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A B : Ω → ℝ)
    (hA : ∀ x, 0 ≤ A x) (hB : ∀ x, 0 ≤ B x)
    (hAm : Measurable A) (hBm : AEStronglyMeasurable B μ)
    (hA4 : Integrable (fun x => A x ^ 4) μ)
    (hB4 : Integrable (fun x => B x ^ 4) μ)
    (hweak : ∀ t : ℝ, 0 < t →
      t * μ.real {x | t ≤ A x} ≤ ∫ x in {x | t ≤ A x}, B x ∂μ) :
    (∫ x, A x ^ 4 ∂μ) ≤ (4 / 3 : ℝ) * ∫ x, A x ^ 3 * B x ∂μ := by
  -- Compare the legal tail integrals after multiplying hweak by 4*t^2.
  -- This weak hypothesis is derived from Mathlib maximal_ineq in Doob.lean;
  -- it is not an assumed fourth-moment or centered-process inequality.
  obtain ⟨hfi, hfe⟩ := fourth_tail_identity μ A hA hAm hA4
  obtain ⟨hmi, hme⟩ := mixed_tail_identity μ A B hA hB hAm hBm hA4 hB4
  rw [hfe, ← hme]
  apply setIntegral_mono_on hfi hmi measurableSet_Ioi
  intro t ht
  have h := mul_le_mul_of_nonneg_left (hweak t ht) (by positivity : 0 ≤ 4 * t ^ 2)
  convert h using 1
  ring

end Causalean.Stat.EmpiricalProcess.Countable

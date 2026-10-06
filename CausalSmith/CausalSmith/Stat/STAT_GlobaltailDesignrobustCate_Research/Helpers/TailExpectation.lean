module
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Integrating the finite-bandwidth deviation bound

A Gaussian tail above bias plus one stochastic unit gives a first moment
bounded by a constant times the sum of the bias and stochastic scales.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory
open scoped ENNReal

/-- Layer cake integrates the deviation inequality, retaining the probability
bound one below the first stochastic unit. -/
-- @node: gaussianTail_lintegral_le
lemma gaussianTail_lintegral_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : AEMeasurable f μ) (hnonneg : ∀ x, 0 ≤ f x)
    (b s K c : ℝ) (hb : 0 ≤ b) (hs : 0 < s) (hK : 0 < K) (hc : 0 < c)
    (htail : ∀ u : ℝ, 1 ≤ u →
      μ.real {x | b + u * s < f x} ≤ K * Real.exp (-c * u ^ 2)) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤
      ENNReal.ofReal (((1 + K) * Real.exp c / c) * (b + s)) := by
  let F : Ω → ℝ := fun x => f x / (b + s)
  let H : ℝ := (1 + K) * Real.exp c
  have hbs : 0 < b + s := by linarith
  have hH : 0 < H := by dsimp [H]; positivity
  have hF : AEMeasurable F μ := hf.div_const _
  have henv (u : ℝ) (hu : 0 < u) :
      μ.real {x | u < F x} ≤ H * Real.exp (-c * u) := by
    by_cases hu1 : 1 ≤ u
    · have hset : {x | u < F x} ⊆ {x | b + u * s < f x} := by
        intro x hx
        have hx' := (lt_div_iff₀ hbs).mp hx
        have hbu : b ≤ b * u := le_mul_of_one_le_right hb hu1
        change b + u * s < f x
        nlinarith
      calc
        μ.real {x | u < F x} ≤ μ.real {x | b + u * s < f x} :=
          measureReal_mono hset
        _ ≤ K * Real.exp (-c * u ^ 2) := htail u hu1
        _ ≤ H * Real.exp (-c * u) := by
          apply mul_le_mul
          · dsimp [H]
            have he : 1 ≤ Real.exp c := Real.one_le_exp_iff.mpr hc.le
            nlinarith
          · apply Real.exp_le_exp.mpr
            nlinarith [mul_nonneg hc.le (show 0 ≤ u ^ 2 - u by nlinarith)]
          · exact Real.exp_nonneg _
          · exact hH.le
    · calc
        μ.real {x | u < F x} ≤ 1 := measureReal_le_one
        _ ≤ H * Real.exp (-c * u) := by
          have he : 1 ≤ Real.exp (c + -c * u) :=
            Real.one_le_exp_iff.mpr (by nlinarith)
          dsimp [H]
          rw [mul_assoc, ← Real.exp_add]
          nlinarith [Real.exp_pos (c + -c * u)]
  have htailE (u : ℝ) (hu : 0 < u) :
      μ {x | u < F x} ≤ ENNReal.ofReal (H * Real.exp (-c * u)) := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (by positivity)]
    exact henv u hu
  have hInt : IntegrableOn (fun u : ℝ => H * Real.exp (-c * u)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0).const_mul H
  have hnorm : (∫⁻ x, ENNReal.ofReal (F x) ∂μ) ≤ ENNReal.ofReal (H / c) := by
    rw [lintegral_eq_lintegral_meas_lt μ
      (Filter.Eventually.of_forall (fun x => div_nonneg (hnonneg x) hbs.le)) hF]
    calc
      _ ≤ ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (H * Real.exp (-c * u)) := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro u hu
        exact htailE u hu
      _ = ENNReal.ofReal (H / c) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hInt
          (Filter.Eventually.of_forall (fun _ => by positivity)), integral_const_mul,
          integral_exp_mul_Ioi (a := -c) (by linarith)]
        simp [div_eq_mul_inv]
  calc
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) =
        ENNReal.ofReal (b + s) * ∫⁻ x, ENNReal.ofReal (F x) ∂μ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro x
      rw [← ENNReal.ofReal_mul hbs.le]
      congr 1
      dsimp [F]
      field_simp
    _ ≤ ENNReal.ofReal (b + s) * ENNReal.ofReal (H / c) :=
      mul_le_mul le_rfl hnorm zero_le zero_le
    _ = _ := by rw [← ENNReal.ofReal_mul hbs.le]; congr 1; dsimp [H]; ring

/-- The same layer-cake bound applies to finite nonnegative extended-real
losses, such as the clipped estimator's supremum loss. -/
-- @node: gaussianTail_ennreal_lintegral_le
lemma gaussianTail_ennreal_lintegral_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ENNReal)
    (hf : AEMeasurable f μ) (hfinite : ∀ x, f x ≠ ⊤)
    (b s K c : ℝ) (hb : 0 ≤ b) (hs : 0 < s) (hK : 0 < K) (hc : 0 < c)
    (htail : ∀ u : ℝ, 1 ≤ u →
      μ.real {x | ENNReal.ofReal (b + u * s) < f x} ≤ K * Real.exp (-c * u ^ 2)) :
    (∫⁻ x, f x ∂μ) ≤
      ENNReal.ofReal (((1 + K) * Real.exp c / c) * (b + s)) := by
  have htail' (u : ℝ) (hu : 1 ≤ u) :
      μ.real {x | b + u * s < (f x).toReal} ≤ K * Real.exp (-c * u ^ 2) := by
    have hsets : {x | b + u * s < (f x).toReal} =
        {x | ENNReal.ofReal (b + u * s) < f x} := by
      ext x
      exact (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) (hfinite x)).symm
    rw [hsets]
    exact htail u hu
  have hbound := gaussianTail_lintegral_le μ (fun x => (f x).toReal)
    hf.ennreal_toReal (fun _ => ENNReal.toReal_nonneg) b s K c hb hs hK hc htail'
  simpa only [ENNReal.ofReal_toReal (hfinite _)] using hbound

end CausalSmith.Stat.GlobalTailDesignRobustCate

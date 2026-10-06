module
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Probability.CentralLimitTheorem

/-! # Integrability of a difference of distribution functions

Finite first moments control the positive and negative CDF tails of two
probability laws. Their CDF difference is therefore Lebesgue integrable.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- For [two real probability laws with finite first moments](hyp:hμ,hν),
[the difference of their cumulative distribution functions is Lebesgue
integrable](goal). -/
theorem integrable_cdf_difference_of_first_moments
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun y : ℝ => y) μ)
    (hν : Integrable (fun y : ℝ => y) ν) :
    Integrable (fun x : ℝ =>
      (μ (Set.Iic x)).toReal - (ν (Set.Iic x)).toReal) volume := by
  let T (ρ : Measure ℝ) (t : ℝ) : ENNReal := ρ {y : ℝ | t ≤ |y|}
  have hTmeas (ρ : Measure ℝ) : Measurable (T ρ) := by
    apply Antitone.measurable
    intro a b hab
    exact measure_mono (by intro y hy; exact le_trans hab hy)
  have hTfin (ρ : Measure ℝ) (hρ : Integrable (fun y : ℝ => y) ρ) :
      ∫⁻ t in Set.Ioi (0 : ℝ), T ρ t < ⊤ := by
    have h := lintegral_eq_lintegral_meas_le ρ
      (f := fun y : ℝ => |y|) (Filter.Eventually.of_forall (fun y => abs_nonneg y))
      (measurable_id.abs.aemeasurable)
    rw [← h]
    exact hρ.abs.lintegral_lt_top
  have hTint (ρ : Measure ℝ) (hρ : Integrable (fun y : ℝ => y) ρ) :
      IntegrableOn (fun t => (T ρ t).toReal) (Set.Ioi 0) := by
    exact integrable_toReal_of_lintegral_ne_top
      (hTmeas ρ).aemeasurable (hTfin ρ hρ).ne
  have hleft (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
      (hρ : Integrable (fun y : ℝ => y) ρ) :
      IntegrableOn (fun x => (ρ (Set.Iic x)).toReal) (Set.Iic 0) := by
    have hdom : IntegrableOn (fun x => (T ρ (-x)).toReal) (Set.Iic 0) := by
      have hh : IntegrableOn (fun x => (T ρ (-x)).toReal) (Set.Iio 0) := by
        have h0 : IntegrableOn (fun t => (T ρ t).toReal) (Set.Ioi (-(0 : ℝ))) := by
          simpa only [neg_zero] using hTint ρ hρ
        exact h0.comp_neg_Iio
      exact (integrableOn_Iic_iff_integrableOn_Iio
        (f := fun x : ℝ => (T ρ (-x)).toReal) (μ := volume) (b := 0)).mpr hh
    apply hdom.mono'
    · have hm : Measurable (fun x : ℝ => ρ (Set.Iic x)) :=
        (show Monotone (fun x : ℝ => ρ (Set.Iic x)) from
          fun _ _ h => measure_mono (Set.Iic_subset_Iic.mpr h)).measurable
      exact hm.ennreal_toReal.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
      have hsub : Set.Iic x ⊆ {y : ℝ | -x ≤ |y|} := by
        intro y hy
        exact le_trans (neg_le_neg hy) (neg_le_abs y)
      have hb := measureReal_mono (μ := ρ) hsub
      rw [measureReal_def, measureReal_def] at hb
      simpa only [Real.norm_eq_abs, abs_of_nonneg (ENNReal.toReal_nonneg)] using hb
  have hright (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
      (hρ : Integrable (fun y : ℝ => y) ρ) :
      IntegrableOn (fun x => (ρ (Set.Ioi x)).toReal) (Set.Ioi 0) := by
    apply (hTint ρ hρ).mono'
    · have hm : Measurable (fun x : ℝ => ρ (Set.Ioi x)) :=
        (show Antitone (fun x : ℝ => ρ (Set.Ioi x)) from
          fun _ _ h => measure_mono (Set.Ioi_subset_Ioi h)).measurable
      exact hm.ennreal_toReal.aestronglyMeasurable
    · apply Filter.Eventually.of_forall
      intro x
      have hsub : Set.Ioi x ⊆ {y : ℝ | x ≤ |y|} := by
        intro y hy
        exact le_trans (le_of_lt hy) (le_abs_self y)
      have hb := measureReal_mono (μ := ρ) hsub
      rw [measureReal_def, measureReal_def] at hb
      simpa only [Real.norm_eq_abs, abs_of_nonneg (ENNReal.toReal_nonneg)] using hb
  have hneg := (hleft μ hμ).sub (hleft ν hν)
  have hpos := (hright ν hν).sub (hright μ hμ)
  apply integrableOn_univ.mp
  rw [← Set.Iic_union_Ioi (a := (0 : ℝ))]
  apply IntegrableOn.union
  · exact hneg
  · apply hpos.congr_fun _ measurableSet_Ioi
    intro x hx
    have hμc := probReal_compl_eq_one_sub (μ := μ) (s := Set.Iic x) measurableSet_Iic
    have hνc := probReal_compl_eq_one_sub (μ := ν) (s := Set.Iic x) measurableSet_Iic
    change (ν (Set.Ioi x)).toReal - (μ (Set.Ioi x)).toReal =
      (μ (Set.Iic x)).toReal - (ν (Set.Iic x)).toReal
    simp only [Set.compl_Iic, Measure.real] at hμc hνc
    linarith

end Causalean.Stat.CLT.BerryEsseen

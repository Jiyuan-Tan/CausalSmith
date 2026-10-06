module
public import Causalean.Stat.RecurrentEvent.CountingProcess.Basic

/-!
One-dimensional hazard-density change of measure for a censored event.
This is the scalar measure step needed before predictable sample histories
and product-law resampling enter the compensator argument.
-/

public section

open MeasureTheory

namespace Causalean.Stat.RecurrentEvent.CountingProcess

/-- If [the censor-time law has the given censor hazard](hyp:hazard,hHazard), the payoff g is
[measurable](hyp:hG) and [nonnegative](hyp:hGnonneg), and [the horizon u is
nonnegative](hyp:hu), then for a fixed failure time f, [the expected payoff over censor times
that fall by u and strictly before f equals the Lebesgue integral, over times s from 0 to u with
s before f, of the payoff times the hazard times the probability of censoring at or after
s](goal). -/
theorem censor_event_hazard_lintegral
    (censorLaw : Measure ℝ) (hazard g : ℝ → ℝ)
    (hHazard : HasCensorHazard censorLaw hazard)
    (hG : Measurable g) (hGnonneg : ∀ s, 0 ≤ g s)
    (f u : ℝ) (hu : 0 ≤ u) :
    (∫⁻ c : ℝ,
      ENNReal.ofReal (if c ≤ u ∧ c < f then g c else 0) ∂censorLaw) =
    ∫⁻ s in Set.Icc 0 u,
      ENNReal.ofReal (if s < f then
        g s * hazard s * (censorLaw (Set.Ici s)).toReal else 0) ∂volume := by
  haveI : IsProbabilityMeasure censorLaw := ⟨hHazard.1.1⟩
  have hsupport : Set.Ici (0 : ℝ) ∈ ae censorLaw :=
    (mem_ae_iff_prob_eq_one measurableSet_Ici).2 hHazard.1.2
  have hsurv : Measurable (fun s : ℝ => censorLaw (Set.Ici s)) := by
    apply Antitone.measurable
    intro a b hab
    exact measure_mono (Set.Ici_subset_Ici.mpr hab)
  have hdens : Measurable (fun s : ℝ =>
      ENNReal.ofReal (hazard s * (censorLaw (Set.Ici s)).toReal)) :=
    (hHazard.2.1.mul hsurv.ennreal_toReal).ennreal_ofReal
  have hcut : Measurable (fun s : ℝ =>
      ENNReal.ofReal (if s < f then g s else 0)) := by
    exact (Measurable.ite measurableSet_Iio hG measurable_const).ennreal_ofReal
  calc
    (∫⁻ c : ℝ, ENNReal.ofReal (if c ≤ u ∧ c < f then g c else 0) ∂censorLaw) =
        ∫⁻ c in Set.Icc 0 u, ENNReal.ofReal (if c < f then g c else 0) ∂censorLaw := by
      rw [← lintegral_indicator measurableSet_Icc]
      apply lintegral_congr_ae
      filter_upwards [hsupport] with c hc
      simp only [Set.indicator_apply, Set.mem_Icc, Set.mem_Ici] at hc ⊢
      by_cases hcu : c ≤ u <;> simp [hc, hcu]
    _ = ∫⁻ s in Set.Icc 0 u,
        ENNReal.ofReal (hazard s * (censorLaw (Set.Ici s)).toReal) *
          ENNReal.ofReal (if s < f then g s else 0) ∂volume := by
      simpa only [← hHazard.2.2.2.2, Pi.mul_apply] using
        (setLIntegral_withDensity_eq_lintegral_mul₀
          (μ := volume) (s := Set.Icc 0 u) hdens.aemeasurable
          hcut.aemeasurable measurableSet_Icc)
    _ = ∫⁻ s in Set.Icc 0 u,
        ENNReal.ofReal (if s < f then
          g s * hazard s * (censorLaw (Set.Ici s)).toReal else 0) ∂volume := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro s hs
      by_cases hsf : s < f
      · simp only [if_pos hsf]
        rw [← ENNReal.ofReal_mul
          (mul_nonneg (hHazard.2.2.1 s) ENNReal.toReal_nonneg)]
        congr 1
        ring
      · simp [hsf]

end Causalean.Stat.RecurrentEvent.CountingProcess

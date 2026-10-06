module
public import Causalean.Stat.OrderStatistic.CDFTransport

/-!
# Interval masses under a bounded density

An almost-everywhere density envelope on a closed interval bounds the mass of
each subinterval by its length. This is the measure-theoretic input to CDF and
order-spacing comparisons.
-/

public section

namespace Causalean.Stat.OrderStatistic

open MeasureTheory

noncomputable section

/-- Given [a real probability law](hyp:μ), [interval endpoints](hyp:a,b), [positive lower and upper density constants](hyp:cg,Cg,hcg,hCg), [a density](hyp:p), [its density representation](hyp:hμ), [an almost-everywhere density envelope on the interval](hyp:hbound), and [a subinterval specified by its endpoint bounds](hyp:hax,hxy,hyb), [that subinterval's mass lies between the two density constants times its length](goal). -/
theorem withDensity_interval_mass_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b cg Cg : ℝ) (p : ℝ → ℝ)
    (hcg : 0 < cg) (hCg : cg ≤ Cg)
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (p x)))
    (hbound : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)), cg ≤ p x ∧ p x ≤ Cg)
    {x y : ℝ} (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
    cg * (y - x) ≤ μ.real (Set.Ioc x y) ∧
      μ.real (Set.Ioc x y) ≤ Cg * (y - x) := by
  have hsub : Set.Ioc x y ⊆ Set.Icc a b := by
    intro z hz
    exact ⟨le_trans hax hz.1.le, le_trans hz.2 hyb⟩
  have hlocal := ae_restrict_of_ae_restrict_of_subset hsub hbound
  have hlen : 0 ≤ y - x := sub_nonneg.mpr hxy
  have hmass :
      ENNReal.ofReal cg * volume (Set.Ioc x y) ≤ μ (Set.Ioc x y) ∧
        μ (Set.Ioc x y) ≤ ENNReal.ofReal Cg * volume (Set.Ioc x y) := by
    rw [hμ, withDensity_apply _ measurableSet_Ioc]
    constructor
    · rw [← setLIntegral_const]
      apply setLIntegral_mono_ae' measurableSet_Ioc
      exact (ae_restrict_iff' measurableSet_Ioc).1
        (hlocal.mono fun z hz => ENNReal.ofReal_le_ofReal hz.1)
    · rw [← setLIntegral_const]
      apply setLIntegral_mono_ae' measurableSet_Ioc
      exact (ae_restrict_iff' measurableSet_Ioc).1
        (hlocal.mono fun z hz => ENNReal.ofReal_le_ofReal hz.2)
  have hfin : μ (Set.Ioc x y) ≠ ⊤ := measure_ne_top μ _
  have hvol : volume (Set.Ioc x y) = ENNReal.ofReal (y - x) := by
    simp [Real.volume_Ioc]
  constructor
  · have h := ENNReal.toReal_mono hfin hmass.1
    simpa [measureReal_def, hvol, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (le_of_lt hcg), ENNReal.toReal_ofReal hlen] using h
  · have hupper : ENNReal.ofReal Cg * volume (Set.Ioc x y) ≠ ⊤ := by
      rw [hvol, ← ENNReal.ofReal_mul (le_trans (le_of_lt hcg) hCg)]
      exact ENNReal.ofReal_ne_top
    have h := ENNReal.toReal_mono hupper hmass.2
    simpa [measureReal_def, hvol, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (le_trans (le_of_lt hcg) hCg),
      ENNReal.toReal_ofReal hlen] using h

end
end Causalean.Stat.OrderStatistic

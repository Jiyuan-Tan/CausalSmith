module
public import Causalean.Stat.Privacy.LaplaceMechanism

/-!
# Centered Laplace mean

Reflection invariance and the exact zero mean of the existing density-defined
Laplace measure. Absolute integrability is reused from the primary library.
This file is independent of the second-moment proof chain.
-/

public section

namespace Causalean.Stat.Privacy

open MeasureTheory Causalean.Stat.Privacy

/-- At [a real scale](hyp:b) with [a positive-scale certificate](hyp:hb), [a centered
Laplace draw has an integrable signed value](goal). -/
theorem laplaceMeasure_integrable_id (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : ℝ => x) (laplaceMeasure b) := by
  exact (laplaceMeasure_integrable_abs b hb).mono' (by fun_prop)
    (ae_of_all _ fun x => by simp)

/-- At [a real scale](hyp:b), [reflecting the centered Laplace measure about zero
preserves that measure](goal).

Prove this directly from `laplaceMeasure`, `abs_neg`, and the invariance of
Lebesgue measure under negation. No distribution moment is assumed.
-/
theorem laplaceMeasure_map_neg (b : ℝ) :
    (laplaceMeasure b).map (fun x : ℝ => -x) = laplaceMeasure b := by
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs, laplaceMeasure,
    withDensity_apply _ (hs.preimage (by fun_prop)), withDensity_apply _ hs]
  calc
    (∫⁻ x in (fun x : ℝ => -x) ⁻¹' s, ENNReal.ofReal (laplacePDF b x)) =
        ∫⁻ x in (fun x : ℝ => -x) ⁻¹' s, ENNReal.ofReal (laplacePDF b (-x)) := by
      simp only [laplacePDF, abs_neg]
    _ = ∫⁻ x in s, ENNReal.ofReal (laplacePDF b x)
        ∂(volume.map (fun x : ℝ => -x)) :=
      (setLIntegral_map hs (measurable_laplacePDF b).ennreal_ofReal
        (by fun_prop)).symm
    _ = _ := by rw [Measure.map_neg_eq_self]

/-- At [a real scale](hyp:b) with [a positive-scale certificate](hyp:hb), [a centered
Laplace draw has mean zero](goal).

Use reflection invariance to equate the mean with its negative. Integrability
is supplied separately by `laplaceMeasure_integrable_id`.
-/
theorem laplaceMeasure_integral_id (b : ℝ) (hb : 0 < b) :
    ∫ x : ℝ, x ∂laplaceMeasure b = 0 := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x)
      ((laplaceMeasure b).map (fun x : ℝ => -x)) := by
    rw [laplaceMeasure_map_neg b]
    exact (laplaceMeasure_integrable_id b hb).aestronglyMeasurable
  have hreflection := integral_map (μ := laplaceMeasure b)
    (φ := fun x : ℝ => -x) (by fun_prop) hmeas
  rw [laplaceMeasure_map_neg b, integral_neg] at hreflection
  linarith

end Causalean.Stat.Privacy

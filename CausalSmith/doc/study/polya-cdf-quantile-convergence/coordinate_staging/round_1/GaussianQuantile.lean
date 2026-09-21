module

public import Causalean.Mathlib.Probability.GaussianMoments
public import Causalean.Mathlib.Probability.StdNormalCDF
public import Causalean.Stat.Quantile.Convergence

/-!
# Gaussian CDFs and quantiles

This module transfers the standard-normal CDF and probit API to every centered Gaussian with
positive variance, identifying its lower quantiles by the usual scale transformation.
-/

public section

open MeasureTheory ProbabilityTheory Real

namespace Causalean.Stat

/-- A centered Gaussian with [positive variance](hyp:hv), evaluated at [a threshold](hyp:x), has
[the standard-normal CDF at the threshold scaled by its standard deviation](goal). -/
theorem cdf_gaussianReal_zero {v : NNReal} (hv : 0 < v) (x : ℝ) :
    cdf (gaussianReal 0 v) x =
      Causalean.Mathlib.stdNormalCDF (x / Real.sqrt (v : ℝ)) := by
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  have hs : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.2 hvR
  rw [cdf_eq_real, Causalean.Mathlib.gaussianReal_eq_map_std]
  rw [MeasureTheory.map_measureReal_apply
    (f := fun z : ℝ => Real.sqrt (v : ℝ) * z + 0)
    (continuous_const.mul continuous_id |>.add continuous_const).measurable measurableSet_Iic]
  rw [show (fun z : ℝ => Real.sqrt (v : ℝ) * z + 0) ⁻¹' Set.Iic x =
      Set.Iic (x / Real.sqrt (v : ℝ)) by
    ext z
    simp only [Set.mem_preimage, Set.mem_Iic, add_zero]
    simpa only [mul_comm] using
      (le_div_iff₀ hs : z ≤ x / Real.sqrt (v : ℝ) ↔
        z * Real.sqrt (v : ℝ) ≤ x).symm]
  rw [← cdf_eq_real]
  rfl

/-- A centered Gaussian with [positive variance](hyp:hv) has [a continuous CDF](goal). -/
theorem continuous_cdf_gaussianReal_zero {v : NNReal} (hv : 0 < v) :
    Continuous (cdf (gaussianReal 0 v)) := by
  rw [show cdf (gaussianReal 0 v) =
      Causalean.Mathlib.stdNormalCDF ∘ (fun x : ℝ => x / Real.sqrt (v : ℝ)) by
    funext x
    exact cdf_gaussianReal_zero hv x]
  exact Causalean.Mathlib.stdNormalCDF_continuous.comp (continuous_id.div_const _)

/-- A centered Gaussian with [positive variance](hyp:hv) has [a strictly increasing CDF](goal). -/
theorem strictMono_cdf_gaussianReal_zero {v : NNReal} (hv : 0 < v) :
    StrictMono (cdf (gaussianReal 0 v)) := by
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  have hs : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.2 hvR
  rw [show cdf (gaussianReal 0 v) =
      Causalean.Mathlib.stdNormalCDF ∘ (fun x : ℝ => x / Real.sqrt (v : ℝ)) by
    funext x
    exact cdf_gaussianReal_zero hv x]
  exact Causalean.Mathlib.stdNormalCDF_strictMono.comp (strictMono_id.div_const hs)

/-- A centered Gaussian with [positive variance](hyp:hv) at [an interior probability level](hyp:hβ0,hβ1)
has [quantile equal to its standard deviation times the standard-normal quantile](goal). -/
theorem quantile_gaussianReal_zero {v : NNReal} (hv : 0 < v) {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) :
    quantile (gaussianReal 0 v) β =
      Real.sqrt (v : ℝ) * Causalean.Mathlib.probit β := by
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  have hs : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.2 hvR
  have hcont := continuous_cdf_gaussianReal_zero hv
  have hquant :
      cdf (gaussianReal 0 v) (quantile (gaussianReal 0 v) β) = β :=
    cdf_quantile_eq_of_continuousAt _ hβ0 hβ1 hcont.continuousAt
  have hcand :
      cdf (gaussianReal 0 v)
          (Real.sqrt (v : ℝ) * Causalean.Mathlib.probit β) = β := by
    rw [cdf_gaussianReal_zero hv]
    rw [mul_div_cancel_left₀ _ hs.ne']
    exact Causalean.Mathlib.stdNormalCDF_probit hβ0 hβ1
  exact (strictMono_cdf_gaussianReal_zero hv).injective (hquant.trans hcand.symm)

end Causalean.Stat

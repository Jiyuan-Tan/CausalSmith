module
public import Causalean.Mathlib.Analysis.RealInterpolation.Basic
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Weighted dilation on positive scales

Positive dilation of a measurable nonnegative scale function contributes the exact
power of the dilation factor in quadratic real interpolation. Infinite integrals
are allowed. This module has no dependence on the scalar normalization evaluation,
so the operator branch can use dilation without importing that evaluation.
-/

public section
open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace Causalean.Mathlib.Analysis.RealInterpolation

/-- [A nonnegative extended measurable scale function](hyp:F,hF), [a positive
dilation](hyp:c,hc), and [an exponent](hyp:θ) satisfy [the dilation identity: the integral over positive t of t^(−1−2θ)·F(c·t) equals
c^(2θ) times the integral over positive t of t^(−1−2θ)·F(t)](goal).
Only measurability on the positive half-line is required; infinite integrals are allowed. -/
theorem lintegral_weighted_dilation (F : ℝ → ℝ≥0∞)
    (hF : Measurable (Set.indicator (Ioi (0 : ℝ)) F))
    (c : ℝ) (hc : 0 < c) (θ : ℝ) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-1 - 2 * θ)) * F (t * c)) =
      ENNReal.ofReal (c ^ (2 * θ)) *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-1 - 2 * θ)) * F t := by
  let G : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (-1 - 2 * θ)) *
    (Ioi (0 : ℝ)).indicator F t
  have hG : Measurable G :=
    ((measurable_id.pow_const (-1 - 2 * θ)).ennreal_ofReal).mul hF
  have hscale : (∫⁻ t, G (t * c)) =
      ENNReal.ofReal c⁻¹ * ∫⁻ t, G t := by
    rw [← lintegral_map (μ := volume) (g := fun t : ℝ => t * c) hG (by fun_prop),
      Real.map_volume_mul_right hc.ne', lintegral_smul_measure, abs_of_pos (inv_pos.mpr hc)]
    rfl
  have hweight : ∀ t ∈ Ioi (0 : ℝ),
      ENNReal.ofReal (t ^ (-1 - 2 * θ)) * F (t * c) =
        ENNReal.ofReal (c ^ (1 + 2 * θ)) * G (t * c) := by
    intro t ht
    have htc : t * c ∈ Ioi (0 : ℝ) := mul_pos ht hc
    simp only [G, indicator_of_mem htc, ← mul_assoc,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _), Real.mul_rpow ht.le hc.le]
    have hcancel : c ^ (1 + 2 * θ) * (t ^ (-1 - 2 * θ) * c ^ (-1 - 2 * θ)) =
        t ^ (-1 - 2 * θ) := by
      rw [mul_left_comm, ← Real.rpow_add hc]
      simp
    rw [← mul_assoc] at hcancel
    rw [hcancel]
  have hsupport : (∫⁻ t in Ioi (0 : ℝ), G (t * c)) = ∫⁻ t, G (t * c) := by
    rw [← lintegral_indicator measurableSet_Ioi]
    congr 1
    ext t
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · simp [ht]
    · have htc : t * c ∉ Ioi (0 : ℝ) := by
        simpa only [mem_Ioi, mul_pos_iff_of_pos_right hc] using ht
      simp [ht, G, htc]
  have hbase : (∫⁻ t, G t) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-1 - 2 * θ)) * F t := by
    have heq : G = (Ioi (0 : ℝ)).indicator
        (fun t => ENNReal.ofReal (t ^ (-1 - 2 * θ)) * F t) := by
      ext t
      by_cases ht : t ∈ Ioi (0 : ℝ) <;> simp [G, ht]
    rw [heq, lintegral_indicator measurableSet_Ioi]
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (c ^ (1 + 2 * θ)) * G (t * c) :=
      setLIntegral_congr_fun measurableSet_Ioi hweight
    _ = ENNReal.ofReal (c ^ (1 + 2 * θ)) * ∫⁻ t, G (t * c) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hsupport]
    _ = _ := by
      rw [hscale, ← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _)]
      have hpow : c ^ (1 + 2 * θ) * c⁻¹ = c ^ (2 * θ) := by
        rw [show 1 + 2 * θ = 2 * θ + 1 by ring, Real.rpow_add hc, Real.rpow_one]
        field_simp
      rw [hpow, hbase]


end Causalean.Mathlib.Analysis.RealInterpolation

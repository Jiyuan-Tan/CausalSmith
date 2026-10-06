module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzBudgetCutoffs

/-! # Integrability for deterministic Prawitz compact certificates

The low-frequency discrepancy cancels the singularity of the filter at zero.
The high-frequency moment factor is integrable on every positive subinterval
of the kernel band. These unchanged proofs are extracted from the compact
budget files so cell certificates have no admitted import dependency.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- For [a nonnegative ratio](hyp:ρ,hρ) and [an interval contained in a
positive kernel band](hyp:U,a,hU,ha,haU), the [low-frequency discrepancy
integrand is interval integrable, including at zero](goal). -/
theorem prawitz_low_compact_intervalIntegrable
    (ρ U a : ℝ) (hρ : 0 ≤ ρ) (hU : 0 < U) (ha : 0 ≤ a) (haU : a ≤ U) :
    IntervalIntegrable
      (fun t : ℝ => ‖prawitzKernel (t / U)‖ * prawitzDiscrepancyEnvelope ρ t)
      volume 0 a := by
  let G : ℝ → ℝ := fun t =>
    (U / (2 * Real.pi) * (ρ * t ^ 2 / 6 + ρ ^ 2 * t ^ 3 / 8) +
      (ρ * t ^ 3 / 6 + ρ ^ 2 * t ^ 4 / 8) / 2) *
        Real.exp (-(t ^ 2 / 4) + ρ * t ^ 3 / 10)
  have hG : Continuous G := by dsimp [G]; fun_prop
  have hK : Measurable prawitzKernel := by
    unfold prawitzKernel Real.sign
    apply Measurable.ite
    · exact (measurableSet_eq_fun measurable_id measurable_const).union
        (measurableSet_lt measurable_const continuous_abs.measurable)
    · exact measurable_const
    · apply Measurable.add
      · exact Complex.measurable_ofReal.comp (by fun_prop)
      · apply Measurable.mul _ measurable_const
        apply Complex.measurable_ofReal.comp
        apply Measurable.div_const
        apply Measurable.add
        · fun_prop
        · apply Measurable.div_const
          apply Measurable.ite (measurableSet_lt measurable_id measurable_const)
            measurable_const
          exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
            measurable_const measurable_const
  have hD : Continuous (prawitzDiscrepancyEnvelope ρ) := by
    unfold prawitzDiscrepancyEnvelope prawitzMomentEnvelope
    fun_prop
  have hm : Measurable
      (fun t : ℝ => ‖prawitzKernel (t / U)‖ * prawitzDiscrepancyEnvelope ρ t) :=
    ((hK.comp (measurable_id.div_const U)).norm).mul hD.measurable
  apply (hG.intervalIntegrable 0 a).mono_fun' hm.aestronglyMeasurable
  rw [Set.uIoc_of_le ha]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : 0 < t := ht.1
  have htU : t ≤ U := ht.2.trans haU
  have hs : 0 < t / U := div_pos ht0 hU
  have hs1 : t / U ≤ 1 := (div_le_one hU).2 htU
  have hk := prawitzKernel_norm_le (t / U)
    (by simpa only [abs_of_pos hs] using hs)
    (by simpa only [abs_of_pos hs] using hs1)
  rw [abs_of_pos hs] at hk
  have hd0 : 0 ≤ prawitzDiscrepancyEnvelope ρ t := by
    unfold prawitzDiscrepancyEnvelope prawitzMomentEnvelope
    positivity
  have hd : prawitzDiscrepancyEnvelope ρ t ≤
      (ρ * t ^ 3 / 6 + ρ ^ 2 * t ^ 4 / 8) *
        Real.exp (-(t ^ 2 / 4) + ρ * t ^ 3 / 10) := by
    simpa only [prawitzDiscrepancyEnvelope, abs_of_pos ht0] using
      (min_le_left
        ((ρ * |t| ^ 3 / 6 + ρ ^ 2 * t ^ 4 / 8) *
          Real.exp (-(t ^ 2 / 4) + ρ * |t| ^ 3 / 10))
        (prawitzMomentEnvelope ρ t + Real.exp (-(t ^ 2 / 2))))
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) hd0)]
  calc
    _ ≤ (1 / (2 * Real.pi * (t / U)) + 1 / 2) *
        ((ρ * t ^ 3 / 6 + ρ ^ 2 * t ^ 4 / 8) *
          Real.exp (-(t ^ 2 / 4) + ρ * t ^ 3 / 10)) :=
      mul_le_mul hk hd hd0 (by positivity)
    _ = G t := by
      dsimp [G]
      field_simp


/-- On [a positive frequency interval [a, b] inside the kernel band of positive
width U](hyp:U,a,b,hU,ha,hab,hbU), [the product of the Prawitz filter
magnitude at t/U and the cubic moment envelope is interval integrable on
[a, b]](goal) for [any ratio ρ](hyp:ρ). The statement covers the assigned
value of the filter at the upper endpoint. -/
theorem prawitz_high_compact_intervalIntegrable
    (ρ U a b : ℝ) (hU : 0 < U) (ha : 0 < a) (hab : a ≤ b) (hbU : b ≤ U) :
    IntervalIntegrable
      (fun t : ℝ => ‖prawitzKernel (t / U)‖ * prawitzMomentEnvelope ρ t)
      volume a b := by
  have hK : Measurable prawitzKernel := by
    unfold prawitzKernel Real.sign
    apply Measurable.ite
    · exact (measurableSet_eq_fun measurable_id measurable_const).union
        (measurableSet_lt measurable_const continuous_abs.measurable)
    · exact measurable_const
    · apply Measurable.add
      · exact Complex.measurable_ofReal.comp (by fun_prop)
      · apply Measurable.mul _ measurable_const
        apply Complex.measurable_ofReal.comp
        apply Measurable.div_const
        apply Measurable.add
        · fun_prop
        · apply Measurable.div_const
          apply Measurable.ite (measurableSet_lt measurable_id measurable_const)
            measurable_const
          exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
            measurable_const measurable_const
  have hM : Continuous (prawitzMomentEnvelope ρ) := by
    unfold prawitzMomentEnvelope
    fun_prop
  have hm : Measurable
      (fun t : ℝ => ‖prawitzKernel (t / U)‖ * prawitzMomentEnvelope ρ t) :=
    ((hK.comp (measurable_id.div_const U)).norm).mul hM.measurable
  apply (intervalIntegrable_const (c := 1 / (2 * Real.pi * (a / U)) + 1 / 2)).mono_fun'
    hm.aestronglyMeasurable
  rw [Set.uIoc_of_le hab]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : 0 < t := ha.trans ht.1
  have hs : 0 < t / U := div_pos ht0 hU
  have hs1 : t / U ≤ 1 := (div_le_one hU).2 (ht.2.trans hbU)
  have hk := prawitzKernel_norm_le (t / U)
    (by simpa only [abs_of_pos hs] using hs)
    (by simpa only [abs_of_pos hs] using hs1)
  rw [abs_of_pos hs] at hk
  have hm0 : 0 ≤ prawitzMomentEnvelope ρ t := by
    unfold prawitzMomentEnvelope
    positivity
  have hm1 : prawitzMomentEnvelope ρ t ≤ 1 := min_le_left _ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) hm0)]
  calc
    _ ≤ ‖prawitzKernel (t / U)‖ * 1 :=
      mul_le_mul_of_nonneg_left hm1 (norm_nonneg _)
    _ ≤ 1 / (2 * Real.pi * (t / U)) + 1 / 2 := by simpa using hk
    _ ≤ 1 / (2 * Real.pi * (a / U)) + 1 / 2 := by
      gcongr
      exact ht.1.le

end Causalean.Stat.CLT.BerryEsseen

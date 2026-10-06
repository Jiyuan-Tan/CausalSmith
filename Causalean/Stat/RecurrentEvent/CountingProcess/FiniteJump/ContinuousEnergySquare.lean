module
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.Basic

/-!
# Square identity for an absolutely continuous compensator

This isolates the real-analysis identity needed to expand the square of a
pathwise compensator integral. The rate is the model's at-risk intensity.
-/

public section

open MeasureTheory Set

namespace Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The square of the integrated predictable intensity is twice the integral
of its running integral times the current intensity-weighted payoff. [The
model, payoff, and path](hyp:M,H,ω), [predictability](hyp:hH), and
[boundedness](hyp:hbound) give [the pathwise square identity](goal). -/
theorem Model.energyIntegral_square (M : Model Ω μ) (H : ℝ → Ω → ℝ)
    (hH : M.Predictable H)
    (hbound : ∃ C : ℝ, ∀ t ω, |H t ω| ≤ C) (ω : Ω) :
    (M.energyIntegral H M.horizon ω) ^ 2 =
      2 * ∫ t in Ioc 0 M.horizon,
        M.energyIntegral H t ω *
          (H t ω * (M.atRisk t ω * M.intensity t ω)) ∂volume := by
  let f : ℝ → ℝ := fun t => H t ω * (M.atRisk t ω * M.intensity t ω)
  let F : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, f s
  have hHjoint : Measurable (fun p : ℝ × Ω => H p.1 p.2) := by
    apply Measurable.le ?_ hH
    apply (MeasurableSpace.generateFrom_le_iff _).mpr
    rintro S ⟨a, b, B, hB, rfl⟩
    exact measurableSet_Ioc.prod ((M.filtration_le a) B hB)
  have hHm : Measurable (fun t => H t ω) :=
    hHjoint.comp (measurable_id.prodMk measurable_const)
  have hrate : Integrable (fun t => M.atRisk t ω * M.intensity t ω)
      (volume.restrict (Ioc 0 M.horizon)) := M.rate_integrable ω
  obtain ⟨C, hC⟩ := hbound
  have hf : Integrable f (volume.restrict (Ioc 0 M.horizon)) := by
    apply Integrable.mono' (hrate.abs.const_mul |C|)
    · exact (hHm.mul ((M.atRisk_joint_measurable.comp
        (measurable_id.prodMk measurable_const)).mul
        (M.intensity_joint_measurable.comp
        (measurable_id.prodMk measurable_const)))).aestronglyMeasurable
    · filter_upwards with t
      simp only [Real.norm_eq_abs, f, abs_mul]
      have hle : |H t ω| ≤ |C| := (hC t ω).trans (le_abs_self C)
      exact mul_le_mul_of_nonneg_right hle (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hfi : IntervalIntegrable f volume 0 M.horizon :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le M.horizon_pos.le).2 hf
  have hF : AbsolutelyContinuousOnInterval F 0 M.horizon :=
    hfi.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hprod := hF.integral_deriv_mul_eq_sub hF
  have hderiv := hfi.ae_hasDerivAt_integral
  have heq : (∫ t in (0 : ℝ)..M.horizon, deriv F t * F t + F t * deriv F t) =
      ∫ t in (0 : ℝ)..M.horizon, 2 * F t * f t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderiv] with t ht htm
    have htIcc : t ∈ Icc (0 : ℝ) M.horizon := by
      simpa [uIcc_of_le M.horizon_pos.le] using (uIoc_subset_uIcc htm)
    have hd : deriv F t = f t :=
      (ht (by simpa [uIcc_of_le M.horizon_pos.le] using htIcc) 0 (by simp)).deriv
    rw [hd]
    ring
  rw [heq] at hprod
  have hzero : F 0 = 0 := by simp [F]
  have hfinal : F M.horizon = M.energyIntegral H M.horizon ω := by
    simp [F, f, Model.energyIntegral, intervalIntegral.integral_of_le M.horizon_pos.le]
  rw [hzero, hfinal] at hprod
  simp only [zero_mul, sub_zero] at hprod
  calc
    (M.energyIntegral H M.horizon ω) ^ 2 =
        ∫ t in (0 : ℝ)..M.horizon, 2 * F t * f t := by
          nlinarith [hprod]
    _ = 2 * ∫ t in Ioc 0 M.horizon,
        M.energyIntegral H t ω *
          (H t ω * (M.atRisk t ω * M.intensity t ω)) ∂volume := by
          rw [intervalIntegral.integral_of_le M.horizon_pos.le, ← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          have ht0 : 0 ≤ t := le_of_lt ht.1
          simp only [F, f, Model.energyIntegral,
            intervalIntegral.integral_of_le ht0]
          ring

end Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump

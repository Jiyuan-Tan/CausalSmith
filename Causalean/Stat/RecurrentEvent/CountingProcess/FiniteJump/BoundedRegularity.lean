module
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.EnergyOccupation

/-!
# Bounded finite-jump integral regularity

Joint measurability, the count second moment, and the uniform finite-horizon
rate bound supply Bochner integrability independently of compensation. This
lower layer is also used by the dominated-convergence bridge.
-/

public section

open MeasureTheory Set

namespace Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A predictable process is jointly measurable for ordinary time and sample
σ-algebras because each filtration is contained in the sample σ-algebra. -/
theorem Model.predictable_joint_measurable (M : Model Ω μ)
    (H : ℝ → Ω → ℝ) (hH : M.Predictable H) :
    Measurable (fun p : ℝ × Ω => H p.1 p.2) := by
  apply Measurable.le ?_ hH
  apply (MeasurableSpace.generateFrom_le_iff _).mpr
  rintro S ⟨a, b, B, hB, rfl⟩
  exact measurableSet_Ioc.prod ((M.filtration_le a) B hB)

/-- A finite-horizon compensated integral of a predictable integrand is a
measurable function of the sample path. -/
theorem Model.measurable_stochasticIntegral (M : Model Ω μ)
    (H : ℝ → Ω → ℝ) (hH : M.Predictable H) :
    Measurable (M.stochasticIntegral H M.horizon) := by
  unfold Model.stochasticIntegral
  exact (M.measurable_jumpIntegral H (M.predictable_joint_measurable H hH)).sub
    (M.measurable_energyIntegral H (M.predictable_joint_measurable H hH))

/-- The finite event count has an integrable first moment under the assumed
second moment of the count. -/
theorem Model.integrable_eventCount (M : Model Ω μ) [IsProbabilityMeasure μ] :
    Integrable (fun ω => ((M.eventTimes ω).card : ℝ)) μ := by
  have hmeas : Measurable (fun ω => ((M.eventTimes ω).card : ℝ)) := by
    have hcount : Measurable (M.count M.horizon) :=
      (M.count_adapted M.horizon).mono (M.filtration_le M.horizon) le_rfl
    have hcard : (fun ω => (M.eventTimes ω).card) = M.count M.horizon := by
      funext ω
      simp only [Model.count]
      congr 1
      exact (Finset.filter_eq_self.mpr
        (fun t ht => (M.events_in_horizon ω t ht).2)).symm
    exact (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (hcard ▸ hcount)
  exact ((memLp_two_iff_integrable_sq
    hmeas.aestronglyMeasurable).2
    M.count_square_integrable).integrable one_le_two

/-- A uniformly bounded event payoff has absolute finite sum at most its
bound times the number of events in the horizon. -/
theorem Model.abs_jumpIntegral_le_card (M : Model Ω μ)
    (H : ℝ → Ω → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ t ω, |H t ω| ≤ C) (ω : Ω) :
    |M.jumpIntegral H M.horizon ω| ≤ C * ((M.eventTimes ω).card : ℝ) := by
  classical
  have hfilter : (M.eventTimes ω).filter (fun t => t ≤ M.horizon) =
      M.eventTimes ω := Finset.filter_eq_self.mpr
    (fun t ht => (M.events_in_horizon ω t ht).2)
  rw [Model.jumpIntegral, hfilter]
  calc
    |∑ t ∈ M.eventTimes ω, H t ω| ≤ ∑ t ∈ M.eventTimes ω, |H t ω| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ M.eventTimes ω, C :=
      Finset.sum_le_sum (fun t _ => hbound t ω)
    _ = C * ((M.eventTimes ω).card : ℝ) := by simp [mul_comm]

/-- The absolute intensity integral of a uniformly bounded payoff is at
most its bound times the nonnegative compensator at the horizon. -/
theorem Model.abs_energyIntegral_le_compensator (M : Model Ω μ)
    (H : ℝ → Ω → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ t ω, |H t ω| ≤ C) (ω : Ω) :
    |M.energyIntegral H M.horizon ω| ≤ C * M.compensator M.horizon ω := by
  have hr_nonneg (t : ℝ) : 0 ≤ M.atRisk t ω * M.intensity t ω :=
    mul_nonneg (M.atRisk_nonneg t ω) (M.intensity_nonneg t ω)
  have hdom (t : ℝ) :
      |H t ω * (M.atRisk t ω * M.intensity t ω)| ≤
        C * (M.atRisk t ω * M.intensity t ω) := by
    rw [abs_mul, abs_of_nonneg (hr_nonneg t)]
    exact mul_le_mul_of_nonneg_right (hbound t ω) (hr_nonneg t)
  have hrate : Integrable (fun t => C * (M.atRisk t ω * M.intensity t ω))
      (volume.restrict (Ioc 0 M.horizon)) :=
    (M.rate_integrable ω).const_mul C
  have hmain := norm_integral_le_of_norm_le
    (f := fun t => H t ω * (M.atRisk t ω * M.intensity t ω))
    (g := fun t => C * (M.atRisk t ω * M.intensity t ω))
    hrate (Filter.Eventually.of_forall (fun t => by
      simpa only [Real.norm_eq_abs] using hdom t))
  simpa [Model.energyIntegral, Model.compensator, Real.norm_eq_abs,
    integral_const_mul] using hmain

/-- A bounded predictable integrand has an integrable finite event sum.
[The model and payoff](hyp:M,H), [predictability](hyp:hH), and [the uniform
bound](hyp:hbound) give [Bochner integrability of the event sum](goal). -/
theorem Model.integrable_jump (M : Model Ω μ) [IsProbabilityMeasure μ]
    (H : ℝ → Ω → ℝ)
    (hH : M.Predictable H)
    (hbound : ∃ C : ℝ, ∀ t ω, |H t ω| ≤ C) :
    Integrable (M.jumpIntegral H M.horizon) μ := by
  obtain ⟨C, hC⟩ := hbound
  apply (M.integrable_eventCount.const_mul |C|).mono'
    (M.measurable_jumpIntegral H (M.predictable_joint_measurable H hH)).aestronglyMeasurable
  filter_upwards [] with ω
  simpa only [Real.norm_eq_abs] using
    M.abs_jumpIntegral_le_card H |C| (abs_nonneg C)
      (fun t ω => (hC t ω).trans (le_abs_self C)) ω

/-- A bounded predictable integrand has an integrable time integral against
the at-risk intensity. -/
theorem Model.integrable_energy (M : Model Ω μ) [IsProbabilityMeasure μ]
    (H : ℝ → Ω → ℝ)
    (hH : M.Predictable H)
    (hbound : ∃ C : ℝ, ∀ t ω, |H t ω| ≤ C) :
    Integrable (M.energyIntegral H M.horizon) μ := by
  obtain ⟨C, hC⟩ := hbound
  obtain ⟨R, hR, hr⟩ := M.rate_horizon_uniform_bound
  apply (integrable_const (|C| * (R * M.horizon) : ℝ)).mono'
    (M.measurable_energyIntegral H (M.predictable_joint_measurable H hH)).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs]
  calc
    |M.energyIntegral H M.horizon ω| ≤ |C| * M.compensator M.horizon ω :=
      M.abs_energyIntegral_le_compensator H |C| (abs_nonneg C)
        (fun t ω => (hC t ω).trans (le_abs_self C)) ω
    _ ≤ |C| * (R * M.horizon) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
      have hi := integral_mono_ae (M.rate_integrable ω)
        (integrable_const R : Integrable (fun _t : ℝ => R)
          (volume.restrict (Ioc 0 M.horizon)))
        (ae_restrict_of_forall_mem measurableSet_Ioc
          (fun t ht => (hr t ω (le_of_lt ht.1) ht.2).2))
      simpa [Model.compensator, integral_const, Real.volume_Ioc,
        M.horizon_pos.le, mul_comm] using hi


end Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump

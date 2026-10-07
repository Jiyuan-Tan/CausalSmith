module
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.BoundedRegularity

/-!
# Pathwise bounds for finite-jump prefixes

The bounds use only a finite event set, a bounded payoff, and the uniform
finite-horizon rate bound. They do not depend on compensation or isometry.
They supply envelopes for both same-subject and cross-subject payoffs.
-/

public section

open MeasureTheory Set

namespace Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A bounded payoff's intensity integral through a time in the horizon is
bounded by the payoff bound times the rate bound times the horizon. -/
theorem Model.abs_energyIntegral_le_horizon (M : Model Ω μ)
    (H : ℝ → Ω → ℝ) (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hH : ∀ t ω, |H t ω| ≤ C)
    (hr : ∀ t ω, 0 ≤ t → t ≤ M.horizon →
      M.atRisk t ω * M.intensity t ω ≤ R)
    (t : ℝ) (ht : t ∈ Icc 0 M.horizon) (ω : Ω) :
    |M.energyIntegral H t ω| ≤ C * (R * M.horizon) := by
  have h := norm_integral_le_of_norm_le
    (f := fun s => H s ω * (M.atRisk s ω * M.intensity s ω))
    (integrable_const (C * R) : Integrable (fun _s : ℝ => C * R)
      (volume.restrict (Ioc 0 t)))
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs => by
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (mul_nonneg (M.atRisk_nonneg s ω) (M.intensity_nonneg s ω))]
      exact mul_le_mul (hH s ω) (hr s ω hs.1.le (hs.2.trans ht.2))
        (mul_nonneg (M.atRisk_nonneg s ω) (M.intensity_nonneg s ω)) hC))
  have h' : |M.energyIntegral H t ω| ≤ (C * R) * t := by
    simpa [Model.energyIntegral, Real.norm_eq_abs, integral_const,
      Real.volume_Ioc, ht.1, mul_comm] using h
  calc
    |M.energyIntegral H t ω| ≤ (C * R) * t := h'
    _ ≤ (C * R) * M.horizon :=
      mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hC hR)
    _ = C * (R * M.horizon) := by ring

/-- A strict-past compensated integral in the horizon is bounded by the
payoff bound times the full event count plus its deterministic rate envelope. -/
theorem Model.abs_prefixIntegral_le (M : Model Ω μ)
    (H : ℝ → Ω → ℝ) (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hH : ∀ t ω, |H t ω| ≤ C)
    (hr : ∀ t ω, 0 ≤ t → t ≤ M.horizon →
      M.atRisk t ω * M.intensity t ω ≤ R)
    (t : ℝ) (ht : t ∈ Icc 0 M.horizon) (ω : Ω) :
    |M.prefixIntegral H t ω| ≤
      C * ((M.eventTimes ω).card : ℝ) + C * (R * M.horizon) := by
  classical
  have hj : |∑ s ∈ (M.eventTimes ω).filter (fun s => s < t), H s ω| ≤
      C * ((M.eventTimes ω).card : ℝ) := by
    calc
      _ ≤ ∑ s ∈ (M.eventTimes ω).filter (fun s => s < t), |H s ω| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ M.eventTimes ω, |H s ω| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (by intro s hs hns; exact abs_nonneg _)
      _ ≤ ∑ _s ∈ M.eventTimes ω, C := Finset.sum_le_sum (fun s _ => hH s ω)
      _ = C * ((M.eventTimes ω).card : ℝ) := by simp [mul_comm]
  have hab : |M.prefixIntegral H t ω| ≤
      |∑ s ∈ (M.eventTimes ω).filter (fun s => s < t), H s ω| +
        |M.energyIntegral H t ω| := by
    simpa [Model.prefixIntegral] using
      (abs_sub_le (∑ s ∈ (M.eventTimes ω).filter (fun s => s < t), H s ω)
        0 (M.energyIntegral H t ω))
  exact hab.trans (add_le_add hj
    (M.abs_energyIntegral_le_horizon H C R hC hR hH hr t ht ω))

/-- A terminal compensated integral is bounded by the payoff bound times
the full event count plus its deterministic rate envelope. [The model and
payoff](hyp:M,H), [the payoff and rate bounds](hyp:C,R,hC,hR,hH,hr), and [the
path](hyp:ω) give [the terminal bound](goal). -/
theorem Model.abs_stochasticIntegral_le (M : Model Ω μ)
    (H : ℝ → Ω → ℝ) (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hH : ∀ t ω, |H t ω| ≤ C)
    (hr : ∀ t ω, 0 ≤ t → t ≤ M.horizon →
      M.atRisk t ω * M.intensity t ω ≤ R) (ω : Ω) :
    |M.stochasticIntegral H M.horizon ω| ≤
      C * ((M.eventTimes ω).card : ℝ) + C * (R * M.horizon) := by
  have hab : |M.stochasticIntegral H M.horizon ω| ≤
      |M.jumpIntegral H M.horizon ω| + |M.energyIntegral H M.horizon ω| := by
    simpa [Model.stochasticIntegral] using
      (abs_sub_le (M.jumpIntegral H M.horizon ω) 0 (M.energyIntegral H M.horizon ω))
  exact hab.trans
    (add_le_add (M.abs_jumpIntegral_le_card H C hH ω)
      (M.abs_energyIntegral_le_horizon H C R hC hR hH hr
        M.horizon ⟨M.horizon_pos.le, le_rfl⟩ ω))

/-- A jointly measurable payoff whose horizon values have a sample-dependent
envelope has an integrable jump sum if envelope times count is integrable. -/
theorem Model.integrable_jump_of_envelope (M : Model Ω μ)
    (G : ℝ → Ω → ℝ) (hG : Measurable (fun p : ℝ × Ω => G p.1 p.2))
    (B : Ω → ℝ)
    (hB : Integrable (fun ω => B ω * ((M.eventTimes ω).card : ℝ)) μ)
    (hbound : ∀ t ω, 0 < t → t ≤ M.horizon → |G t ω| ≤ B ω) :
    Integrable (M.jumpIntegral G M.horizon) μ := by
  classical
  apply hB.mono' (M.measurable_jumpIntegral G hG).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, Model.jumpIntegral,
    Finset.filter_eq_self.mpr (fun t ht => (M.events_in_horizon ω t ht).2)]
  calc
    |∑ t ∈ M.eventTimes ω, G t ω| ≤ ∑ t ∈ M.eventTimes ω, |G t ω| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ M.eventTimes ω, B ω := Finset.sum_le_sum
      (fun t ht => hbound t ω (M.events_in_horizon ω t ht).1
        (M.events_in_horizon ω t ht).2)
    _ = B ω * ((M.eventTimes ω).card : ℝ) := by simp [mul_comm]

/-- A jointly measurable payoff with an integrable sample-dependent envelope
on the horizon has an integrable intensity integral under a bounded rate. -/
theorem Model.integrable_energy_of_envelope (M : Model Ω μ)
    (G : ℝ → Ω → ℝ) (hG : Measurable (fun p : ℝ × Ω => G p.1 p.2))
    (B : Ω → ℝ) (hB : Integrable B μ) (hBnonneg : ∀ ω, 0 ≤ B ω)
    (R : ℝ)
    (hr : ∀ t ω, 0 ≤ t → t ≤ M.horizon →
      M.atRisk t ω * M.intensity t ω ≤ R)
    (hbound : ∀ t ω, 0 < t → t ≤ M.horizon → |G t ω| ≤ B ω) :
    Integrable (M.energyIntegral G M.horizon) μ := by
  apply (hB.mul_const (R * M.horizon)).mono'
    (M.measurable_energyIntegral G hG).aestronglyMeasurable
  filter_upwards [] with ω
  have h := norm_integral_le_of_norm_le
    (f := fun s => G s ω * (M.atRisk s ω * M.intensity s ω))
    (integrable_const (B ω * R) : Integrable (fun _s : ℝ => B ω * R)
      (volume.restrict (Ioc 0 M.horizon)))
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs => by
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (mul_nonneg (M.atRisk_nonneg s ω) (M.intensity_nonneg s ω))]
      exact mul_le_mul (hbound s ω hs.1 hs.2) (hr s ω hs.1.le hs.2)
        (mul_nonneg (M.atRisk_nonneg s ω) (M.intensity_nonneg s ω)) (hBnonneg ω)))
  simpa [Model.energyIntegral, integral_const, Real.volume_Ioc,
    M.horizon_pos.le, mul_assoc, mul_comm, mul_left_comm] using h

end Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump

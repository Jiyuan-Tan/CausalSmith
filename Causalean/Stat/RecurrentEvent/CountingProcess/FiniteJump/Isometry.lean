module
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.Compensator
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.ContinuousEnergySquare
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.FiniteJumpAlgebra
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.Regularity

/-!
# Centering and L² isometry for finite-jump counting processes

The pathwise square expansion exposes a quadratic jump payoff and a mixed
strict-past payoff. Predictable compensation cancels the latter and converts
the former into the integrated quadratic intensity.
-/

public section

open MeasureTheory

namespace Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The square of a finite-jump compensated integral is its jump-sum of
quadratic payoffs plus the mixed jump payoff minus the mixed compensator
payoff. -/
theorem Model.square_pathwise (M : Model Ω μ) (H : ℝ → Ω → ℝ)
    (hH : M.Predictable H)
    (hbound : ∃ C : ℝ, ∀ t ω, |H t ω| ≤ C) (ω : Ω) :
    (M.stochasticIntegral H M.horizon ω) ^ 2 =
      M.jumpIntegral (M.quadraticPayoff H) M.horizon ω +
      M.jumpIntegral (M.prefixPayoff H) M.horizon ω -
      M.energyIntegral (M.prefixPayoff H) M.horizon ω := by
  have hj := M.jumpIntegral_square H ω
  have hc := M.jump_energy_cross H hH hbound ω
  have he := M.energyIntegral_square H hH hbound ω
  unfold Model.stochasticIntegral Model.quadraticPayoff
    Model.prefixPayoff Model.prefixIntegral
  dsimp only [Model.jumpIntegral, Model.energyIntegral] at hj hc he ⊢
  classical
  let r : ℝ → ℝ := fun t => M.atRisk t ω * M.intensity t ω
  let f : ℝ → ℝ := fun t => H t ω * r t
  let J : ℝ → ℝ := fun t =>
    ∑ s ∈ (M.eventTimes ω).filter (fun s => s < t), H s ω
  let F : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, f s
  have hHm : Measurable (fun t => H t ω) :=
    (M.predictable_joint_measurable H hH).comp
      (measurable_id.prodMk measurable_const)
  have hrm : Measurable r :=
    (M.atRisk_joint_measurable.comp (measurable_id.prodMk measurable_const)).mul
      (M.intensity_joint_measurable.comp (measurable_id.prodMk measurable_const))
  obtain ⟨C, hC⟩ := hbound
  have hf : Integrable f (volume.restrict (Set.Ioc 0 M.horizon)) := by
    apply Integrable.mono' ((M.rate_integrable ω).abs.const_mul |C|)
    · exact (hHm.mul hrm).aestronglyMeasurable
    · filter_upwards with t
      simp only [Real.norm_eq_abs, f, abs_mul]
      simpa [r, abs_mul, mul_assoc] using
        mul_le_mul_of_nonneg_right ((hC t ω).trans (le_abs_self C))
          (abs_nonneg (r t))
  have hJm : Measurable J := by
    dsimp [J]
    simp_rw [Finset.sum_filter]
    apply Finset.measurable_sum
    intro s hs
    exact Measurable.ite measurableSet_Ioi measurable_const measurable_const
  have hJbound (t : ℝ) : |J t| ≤ ∑ s ∈ M.eventTimes ω, |H s ω| := by
    calc
      |J t| ≤ ∑ s ∈ (M.eventTimes ω).filter (fun s => s < t), |H s ω| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ M.eventTimes ω, |H s ω| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (by intro s hs hns; exact abs_nonneg _)
  have hfi : IntervalIntegrable f volume 0 M.horizon :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le M.horizon_pos.le).2 hf
  have hFcont : ContinuousOn F (Set.Icc 0 M.horizon) := by
    simpa [F, Set.uIcc_of_le M.horizon_pos.le] using
      (hfi.absolutelyContinuousOnInterval_intervalIntegral (by simp)).continuousOn
  obtain ⟨D, hD⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn hFcont
  have hFm : AEStronglyMeasurable F (volume.restrict (Set.Ioc 0 M.horizon)) :=
    (hFcont.mono (Set.Ioc_subset_Icc_self)).aestronglyMeasurable measurableSet_Ioc
  have hA : Integrable (fun t => (2 * H t ω * J t) * r t)
      (volume.restrict (Set.Ioc 0 M.horizon)) := by
    apply (M.rate_integrable ω).bdd_mul (c :=
      2 * |C| * ∑ s ∈ M.eventTimes ω, |H s ω|)
      ((measurable_const.mul hHm).mul hJm).aestronglyMeasurable
    filter_upwards with t
    simp only [Real.norm_eq_abs]
    have ht := hJbound t
    have hHle : |H t ω| ≤ |C| := (hC t ω).trans (le_abs_self C)
    calc
      |2 * H t ω * J t| = 2 * |H t ω| * |J t| := by simp [abs_mul]
      _ ≤ 2 * |C| * ∑ s ∈ M.eventTimes ω, |H s ω| := by gcongr
  have hB : Integrable (fun t => (2 * F t * H t ω) * r t)
      (volume.restrict (Set.Ioc 0 M.horizon)) := by
    apply (M.rate_integrable ω).bdd_mul (c := 2 * D * |C|)
      ((MeasureTheory.AEStronglyMeasurable.const_mul hFm 2).mul
        hHm.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [Real.norm_eq_abs]
    have hFle : |F t| ≤ D := hD t ⟨le_of_lt ht.1, ht.2⟩
    have hHle : |H t ω| ≤ |C| := (hC t ω).trans (le_abs_self C)
    have hD0 : 0 ≤ D := (abs_nonneg _).trans hFle
    calc
      |2 * F t * H t ω| = 2 * |F t| * |H t ω| := by simp [abs_mul]
      _ ≤ 2 * D * |C| := by gcongr
  have hI :
      (∫ t in Set.Ioc 0 M.horizon,
        (2 * H t ω * (J t - M.energyIntegral H t ω)) * r t ∂volume) =
      (∫ t in Set.Ioc 0 M.horizon, (2 * H t ω * J t) * r t ∂volume) -
      (∫ t in Set.Ioc 0 M.horizon, (2 * F t * H t ω) * r t ∂volume) := by
    calc
      _ = ∫ t in Set.Ioc 0 M.horizon,
          ((2 * H t ω * J t) * r t - (2 * F t * H t ω) * r t) ∂volume := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have hFt : F t = M.energyIntegral H t ω := by
          simp [F, f, r, Model.energyIntegral,
            intervalIntegral.integral_of_le (le_of_lt ht.1)]
        rw [← hFt]
        ring
      _ = _ := integral_sub hA hB
  simp only [J, r, Model.energyIntegral] at hI
  rw [hI]
  have hBval :
      (∫ t in Set.Ioc 0 M.horizon,
        (2 * F t * H t ω) * (M.atRisk t ω * M.intensity t ω) ∂volume) =
      (∫ t in Set.Ioc 0 M.horizon,
        H t ω * (M.atRisk t ω * M.intensity t ω) ∂volume) ^ 2 := by
    rw [he, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [F, f, r, intervalIntegral.integral_of_le (le_of_lt ht.1)]
    ring
  simp only [mul_sub, Finset.sum_sub_distrib]
  nlinarith [hj, hc, hBval]

/-- The expected finite-horizon stochastic integral of a bounded predictable
integrand against the compensated count is zero. -/
theorem Model.stochasticIntegral_centered (M : Model Ω μ)
    (H : ℝ → Ω → ℝ) (hH : M.Predictable H)
    (hbound : ∃ C : ℝ, ∀ t ω, |H t ω| ≤ C) :
    (∫ ω, M.stochasticIntegral H M.horizon ω ∂μ) = 0 := by
  unfold Model.stochasticIntegral
  rw [integral_sub (M.integrable_jump H hH hbound)
    (M.integrable_energy H hH hbound),
    M.bounded_predictable_compensator H hH hbound
      (M.integrable_jump H hH hbound) (M.integrable_energy H hH hbound)]
  ring

/-- The expected square of a bounded predictable compensated counting
integral equals the expected integral of its squared integrand against the
at-risk intensity. [The model and payoff](hyp:M,H), [predictability](hyp:hH),
and [boundedness](hyp:hbound) give [the subject compensated-integral
isometry](goal). -/
theorem Model.stochasticIntegral_isometry (M : Model Ω μ)
    (H : ℝ → Ω → ℝ) (hH : M.Predictable H)
    (hbound : ∃ C : ℝ, ∀ t ω, |H t ω| ≤ C) :
    (∫ ω, (M.stochasticIntegral H M.horizon ω) ^ 2 ∂μ) =
      ∫ ω, M.energyIntegral (M.quadraticPayoff H) M.horizon ω ∂μ := by
  have hjq := M.integrable_quadratic_jump H hH hbound
  have heq := M.integrable_quadratic_energy H hH hbound
  have hjp := M.integrable_prefix_jump H hH hbound
  have hep := M.integrable_prefix_energy H hH hbound
  have hquad : ∃ C : ℝ, ∀ t ω, |M.quadraticPayoff H t ω| ≤ C := by
    obtain ⟨C, hC⟩ := hbound
    refine ⟨C ^ 2, ?_⟩
    intro t ω
    simpa [Model.quadraticPayoff, abs_pow] using
      (pow_le_pow_left₀ (abs_nonneg (H t ω)) (hC t ω) 2)
  have hcq := M.bounded_predictable_compensator (M.quadraticPayoff H)
    (M.predictable_quadratic H hH) hquad hjq heq
  have hcp := M.predictable_compensator (M.prefixPayoff H)
    (M.predictable_prefix_payoff H hH hbound)
    (M.integrable_prefix_jump_abs H hH hbound)
    (M.integrable_prefix_energy_abs H hH hbound)
  calc
    (∫ ω, (M.stochasticIntegral H M.horizon ω) ^ 2 ∂μ) =
        ∫ ω, M.jumpIntegral (M.quadraticPayoff H) M.horizon ω +
          M.jumpIntegral (M.prefixPayoff H) M.horizon ω -
          M.energyIntegral (M.prefixPayoff H) M.horizon ω ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall (M.square_pathwise H hH hbound))
    _ = (∫ ω, M.jumpIntegral (M.quadraticPayoff H) M.horizon ω ∂μ) +
          (∫ ω, M.jumpIntegral (M.prefixPayoff H) M.horizon ω ∂μ) -
          (∫ ω, M.energyIntegral (M.prefixPayoff H) M.horizon ω ∂μ) := by
      change (∫ ω, (M.jumpIntegral (M.quadraticPayoff H) M.horizon +
        M.jumpIntegral (M.prefixPayoff H) M.horizon -
        M.energyIntegral (M.prefixPayoff H) M.horizon) ω ∂μ) = _
      rw [integral_sub' (hjq.add hjp) hep, integral_add' hjq hjp]
    _ = ∫ ω, M.energyIntegral (M.quadraticPayoff H) M.horizon ω ∂μ := by
      rw [hcq, hcp]
      ring

end Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump

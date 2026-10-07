module
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.BoundedRegularity

/-!
# Dominated convergence for bounded finite-jump payoffs

These two analytic bridges isolate passage to the limit in expected event sums
and intensity integrals. They use finite counts and bounded rates, without any
compensation or isometry premise.
-/

public section

open MeasureTheory Filter

namespace Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Uniformly bounded predictable payoffs converging pointwise have convergent
expected finite event sums under a probability law with a count second moment.
[The model](hyp:M), [the approximating and limiting payoffs](hyp:G,H), [predictability of the
approximating payoffs](hyp:hG), [the common bound](hyp:C,hbound),
and [pointwise convergence](hyp:hlim) give [convergence of expected event
sums](goal). -/
theorem Model.tendsto_expected_jumpIntegral (M : Model Ω μ)
    [IsProbabilityMeasure μ] (G : ℕ → ℝ → Ω → ℝ) (H : ℝ → Ω → ℝ)
    (hG : ∀ k, M.Predictable (G k))
    (C : ℝ) (hbound : ∀ k t ω, |G k t ω| ≤ C)
    (hlim : ∀ t ω, Tendsto (fun k => G k t ω) atTop (nhds (H t ω))) :
    Tendsto (fun k => ∫ ω, M.jumpIntegral (G k) M.horizon ω ∂μ)
      atTop (nhds (∫ ω, M.jumpIntegral H M.horizon ω ∂μ)) := by
  /- First commute the limit with the fixed finite event sum on each path
     (`tendsto_finset_sum`). The integrable envelope is C times event count,
     from `integrable_eventCount` and `abs_jumpIntegral_le_card`. Use Mathlib's
     `tendsto_integral_of_dominated_convergence`; no intensity identity is used. -/
  classical
  apply tendsto_integral_of_dominated_convergence
    (fun ω => C * ((M.eventTimes ω).card : ℝ))
  · intro k
    exact (M.measurable_jumpIntegral (G k)
      (M.predictable_joint_measurable (G k) (hG k))).aestronglyMeasurable
  · exact M.integrable_eventCount.const_mul C
  · intro k
    exact Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs] using
        M.abs_jumpIntegral_le_card (G k) C (hbound k) ω)
  · apply Eventually.of_forall
    intro ω
    unfold Model.jumpIntegral
    exact tendsto_finsetSum _ (fun t _ => hlim t ω)

/-- Uniformly bounded predictable payoffs converging pointwise have convergent
expected intensity integrals on the finite horizon. -/
theorem Model.tendsto_expected_energyIntegral (M : Model Ω μ)
    [IsProbabilityMeasure μ] (G : ℕ → ℝ → Ω → ℝ) (H : ℝ → Ω → ℝ)
    (hG : ∀ k, M.Predictable (G k))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ k t ω, |G k t ω| ≤ C)
    (hlim : ∀ t ω, Tendsto (fun k => G k t ω) atTop (nhds (H t ω))) :
    Tendsto (fun k => ∫ ω, M.energyIntegral (G k) M.horizon ω ∂μ)
      atTop (nhds (∫ ω, M.energyIntegral H M.horizon ω ∂μ)) := by
  /- Apply dominated convergence in time on each path, using C times its
     nonnegative integrable rate. Then apply it in the sample variable with
     the constant envelope C * rateBound * horizon. Both measurability facts
     follow from `predictable_joint_measurable` and `measurable_energyIntegral`.
     This lemma imports no compensator theorem, avoiding a dependency cycle. -/
  obtain ⟨R, hR, hr⟩ := M.rate_horizon_uniform_bound
  apply tendsto_integral_of_dominated_convergence
    (fun _ω => C * (R * M.horizon))
  · intro k
    exact (M.measurable_energyIntegral (G k)
      (M.predictable_joint_measurable (G k) (hG k))).aestronglyMeasurable
  · exact integrable_const _
  · intro k
    apply Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs]
    calc
      |M.energyIntegral (G k) M.horizon ω| ≤ C * M.compensator M.horizon ω :=
        M.abs_energyIntegral_le_compensator (G k) C (hbound k) ω
      _ ≤ C * (R * M.horizon) := by
        apply mul_le_mul_of_nonneg_left _ hC
        have hi := integral_mono_ae (M.rate_integrable ω)
          (integrable_const R : Integrable (fun _t : ℝ => R)
            (volume.restrict (Set.Ioc 0 M.horizon)))
          (ae_restrict_of_forall_mem measurableSet_Ioc
            (fun t ht => (hr t ω (le_of_lt ht.1) ht.2).2))
        simpa [Model.compensator, integral_const, Real.volume_Ioc,
          M.horizon_pos.le, mul_comm] using hi
  · apply Eventually.of_forall
    intro ω
    unfold Model.energyIntegral
    apply tendsto_integral_of_dominated_convergence
      (fun t => C * (M.atRisk t ω * M.intensity t ω))
    · intro k
      exact (((M.predictable_joint_measurable (G k) (hG k)).comp
        (measurable_id.prodMk measurable_const)).mul
        ((M.atRisk_joint_measurable.comp (measurable_id.prodMk measurable_const)).mul
          (M.intensity_joint_measurable.comp
            (measurable_id.prodMk measurable_const)))).aestronglyMeasurable
    · exact (M.rate_integrable ω).const_mul C
    · intro k
      apply Eventually.of_forall
      intro t
      have hnonneg : 0 ≤ M.atRisk t ω * M.intensity t ω :=
        mul_nonneg (M.atRisk_nonneg t ω) (M.intensity_nonneg t ω)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnonneg]
      exact mul_le_mul_of_nonneg_right (hbound k t ω) hnonneg
    · exact Eventually.of_forall (fun t => (hlim t ω).mul tendsto_const_nhds)

end Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump

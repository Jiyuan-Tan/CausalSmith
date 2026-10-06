module
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.JumpEnumeration

/-!
# The intensity occupation measure of a finite-jump model

The intensity occupation measure weights time-sample product measure by the
nonnegative at-risk intensity on the finite horizon. Its mass is the expected
compensator integral of an indicator.
-/

@[expose] public section

open MeasureTheory Set

namespace Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The intensity occupation measure gives each time-sample point the
nonnegative at-risk intensity within the horizon. -/
noncomputable def Model.energyOccupation (M : Model Ω μ) : Measure (ℝ × Ω) :=
  ((volume.restrict (Ioc 0 M.horizon)).prod μ).withDensity
    (fun p => ENNReal.ofReal (M.atRisk p.1 p.2 * M.intensity p.1 p.2))

/-- On the observed horizon the at-risk intensity is nonnegative and has a
common finite upper bound, uniformly over sample paths. -/
theorem Model.rate_horizon_uniform_bound (M : Model Ω μ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, 0 ≤ t → t ≤ M.horizon →
      0 ≤ M.atRisk t ω * M.intensity t ω ∧
        M.atRisk t ω * M.intensity t ω ≤ C := by
  obtain ⟨C, hC⟩ := M.rate_bounded
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ω ht hT
  exact ⟨mul_nonneg (M.atRisk_nonneg t ω) (M.intensity_nonneg t ω),
    (hC t ω ht hT).trans (le_max_left _ _)⟩

/-- A uniformly bounded at-risk intensity on the finite horizon makes the
intensity occupation measure finite under a probability law. -/
theorem Model.energyOccupation_finite (M : Model Ω μ) [IsProbabilityMeasure μ] :
    M.energyOccupation univ < ⊤ := by
  obtain ⟨C, hC, hrate⟩ := M.rate_horizon_uniform_bound
  have : IsFiniteMeasure ((volume.restrict (Ioc 0 M.horizon)).prod μ) := inferInstance
  have hbound : ∀ᵐ p ∂(volume.restrict (Ioc 0 M.horizon)).prod μ,
      ENNReal.ofReal (M.atRisk p.1 p.2 * M.intensity p.1 p.2) ≤
        ENNReal.ofReal C := by
    have h : ∀ᵐ p ∂(volume.prod μ).restrict (Ioc 0 M.horizon ×ˢ univ),
        ENNReal.ofReal (M.atRisk p.1 p.2 * M.intensity p.1 p.2) ≤
          ENNReal.ofReal C :=
      ae_restrict_of_forall_mem (measurableSet_Ioc.prod MeasurableSet.univ)
      (fun p hp => ENNReal.ofReal_le_ofReal (hrate p.1 p.2
        (le_of_lt hp.1.1) hp.1.2).2)
    rw [← Measure.prod_restrict, Measure.restrict_univ] at h
    exact h
  rw [Model.energyOccupation, withDensity_apply _ MeasurableSet.univ]
  simpa using lt_of_le_of_lt (lintegral_mono_ae hbound)
    (lintegral_const_lt_top ENNReal.ofReal_ne_top)

/-- The intensity occupation mass of a measurable time-sample set equals
the expected integral of its indicator against at-risk intensity. [The model
and measurable set](hyp:M,S,hS), together with [integrability of its energy
indicator](hyp:henergy), give [the occupation-mass identity](goal). -/
theorem Model.energyOccupation_indicator (M : Model Ω μ)
    [IsProbabilityMeasure μ] (S : Set (ℝ × Ω)) (hS : MeasurableSet S)
    (henergy : Integrable
      (M.energyIntegral (fun t ω => S.indicator (fun _ => (1 : ℝ)) (t, ω))
        M.horizon) μ) :
    (M.energyOccupation S).toReal =
      ∫ ω, M.energyIntegral
        (fun t ω => S.indicator (fun _ => (1 : ℝ)) (t, ω))
        M.horizon ω ∂μ := by
  let r : ℝ × Ω → ℝ := fun p => M.atRisk p.1 p.2 * M.intensity p.1 p.2
  let f : ℝ × Ω → ℝ := fun p => S.indicator (fun _ => (1 : ℝ)) p * r p
  have hrmeas : Measurable r := M.atRisk_joint_measurable.mul M.intensity_joint_measurable
  have hfmeas : Measurable f := (measurable_const.indicator hS).mul hrmeas
  have hfnonneg : ∀ p, 0 ≤ f p := by
    intro p
    by_cases hp : p ∈ S <;> simp [f, r, Set.indicator, hp,
      mul_nonneg (M.atRisk_nonneg p.1 p.2) (M.intensity_nonneg p.1 p.2)]
  have hsection (ω : Ω) : Integrable (fun t => f (t, ω))
      (volume.restrict (Ioc 0 M.horizon)) := by
    have hs : MeasurableSet {t : ℝ | (t, ω) ∈ S} :=
      hS.preimage measurable_prodMk_right
    have h := (M.rate_integrable ω).indicator hs
    change Integrable (Set.indicator {t : ℝ | (t, ω) ∈ S}
      (fun t => M.atRisk t ω * M.intensity t ω))
        (volume.restrict (Ioc 0 M.horizon)) at h
    convert h using 1
    funext t
    by_cases ht : (t, ω) ∈ S <;> simp [f, r, Set.indicator, ht]
  have htime (ω : Ω) :
      ∫⁻ t, ENNReal.ofReal (f (t, ω)) ∂(volume.restrict (Ioc 0 M.horizon)) =
        ENNReal.ofReal (M.energyIntegral
          (fun t ω => S.indicator (fun _ => (1 : ℝ)) (t, ω)) M.horizon ω) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hsection ω)
      (Filter.Eventually.of_forall (fun t => hfnonneg (t, ω)))]
    rfl
  have hmass : M.energyOccupation S =
      ∫⁻ ω, ENNReal.ofReal (M.energyIntegral
        (fun t ω => S.indicator (fun _ => (1 : ℝ)) (t, ω)) M.horizon ω) ∂μ := by
    rw [Model.energyOccupation, withDensity_apply _ hS]
    rw [← lintegral_indicator hS]
    have hpoint : S.indicator (fun p => ENNReal.ofReal (r p)) =
        fun p => ENNReal.ofReal (f p) := by
      funext p
      by_cases hp : p ∈ S <;> simp [f, Set.indicator, hp]
    rw [hpoint, lintegral_prod_symm' _ hfmeas.ennreal_ofReal]
    simp_rw [htime]
  have hnonneg : ∀ ω, 0 ≤ M.energyIntegral
      (fun t ω => S.indicator (fun _ => (1 : ℝ)) (t, ω)) M.horizon ω := by
    intro ω
    change 0 ≤ ∫ t in Ioc 0 M.horizon, f (t, ω) ∂volume
    exact integral_nonneg (fun t => hfnonneg (t, ω))
  have hreal := ofReal_integral_eq_lintegral_ofReal henergy
    (Filter.Eventually.of_forall hnonneg)
  rw [← hmass] at hreal
  rw [← hreal]
  exact ENNReal.toReal_ofReal (integral_nonneg hnonneg)

end Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump

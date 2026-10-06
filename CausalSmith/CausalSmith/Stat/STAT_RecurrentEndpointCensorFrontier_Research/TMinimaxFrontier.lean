module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.MinimaxCore

/-!
# Three-regime minimax frontier

The mathematical rate statement consumes the ungated paper-owned minimax
helpers. Cited scope and threshold results are comparison material only.
-/

@[expose] public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The treatment probability conditional on the (trivial) baseline covariate
in this randomized experiment. -/
noncomputable def horizonTreatmentMechanism (P : SubjectLaw) (a : Arm) :
    LatentSubject → ℝ :=
  P.latent[Set.indicator {w | w.treatment = a} (fun _ => (1 : ℝ)) | ⊥]

/-- Conditional retention through the analysis horizon given the arm-specific
recurrent and death history. Under independent censoring it is almost surely
the marginal retention. -/
noncomputable def horizonConditionalCensorProduct (P : SubjectLaw) (a : Arm) :
    LatentSubject → ℝ :=
  P.latent[Set.indicator {w | (1 : ENNReal) ≤ w.censor a} (fun _ => (1 : ℝ)) |
    MeasurableSpace.comap (fun w : LatentSubject => (w.recur a, w.death a)) inferInstance]

-- @node: thm:minimax-frontier
theorem minimax_frontier (c : ClassConstants)
    (hNonempty : ∃ P : SubjectLaw, ModelClass c P) :
    ∃ c₀ C : ℝ, 0 < c₀ ∧ c₀ < C ∧
      (∀ n : ℕ, 3 ≤ n →
        c₀ * riskScale c n ≤ minimaxRisk c n ∧
        minimaxRisk c n ≤ C * riskScale c n ∧
        ∀ P : SubjectLaw, ModelClass c P →
          Causalean.Stat.sqRisk (sampleLaw P n) (observableEstimator c)
            (causalTarget P) ≤ C * riskScale c n) ∧
      (∀ P : SubjectLaw, ModelClass c P →
        (∀ a : Arm, retention P a 1 = 0 ∧
          P.p a * retention P a 1 = 0) ∧
        sInf {v : ℝ | ∃ a : Arm, ∃ t ∈ Set.Icc (0 : ℝ) 1,
          v = P.p a * retention P a t} = 0 ∧
        (∀ a : Arm, ∀ᵐ z ∂P.latent,
          horizonTreatmentMechanism P a z = P.p a ∧
          horizonConditionalCensorProduct P a z = retention P a 1 ∧
          horizonConditionalCensorProduct P a z *
            horizonTreatmentMechanism P a z = 0) ∧
        (∀ η : ℝ, 0 < η → ∀ a : Arm,
          ¬ (∀ᵐ z ∂P.latent,
            η < horizonConditionalCensorProduct P a z *
              horizonTreatmentMechanism P a z)) ∧
        (∀ ε : ℝ, 0 < ε → ∀ a : Arm,
          ¬ (∀ᵐ z ∂P.latent, ε < P.p a * retention P a 1))) := by
  obtain ⟨c₀, C, hc₀, hlt, hrisk⟩ := minimax_core c hNonempty
  refine ⟨c₀, C, hc₀, hlt, hrisk, ?_⟩
  intro P hP
  have hret := zero_horizon_retention c P hP
  have hinf := zero_horizon_retention_inf c P hP
  have hscope : ∀ a : Arm, ∀ᵐ z ∂P.latent,
      horizonTreatmentMechanism P a z = P.p a ∧
      horizonConditionalCensorProduct P a z = retention P a 1 ∧
      horizonConditionalCensorProduct P a z * horizonTreatmentMechanism P a z = 0 := by
      intro a
      letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
      have hzero : P.latent {z | (1 : ENNReal) ≤ z.censor a} = 0 := by
        apply (measureReal_eq_zero_iff).mp
        simpa [retention] using hret a
      have hnull : (fun z : LatentSubject =>
          Set.indicator {w | (1 : ENNReal) ≤ w.censor a} (fun _ => (1 : ℝ)) z) =ᵐ[P.latent]
          (fun _ => 0) := by
        filter_upwards [(ae_iff.mpr (by simpa using hzero) :
          ∀ᵐ z ∂P.latent, z ∉ {w | (1 : ENNReal) ≤ w.censor a})] with z hz
        simp [Set.indicator, hz]
      have hcensor : ∀ᵐ z ∂P.latent,
          horizonConditionalCensorProduct P a z = 0 := by
        filter_upwards [(condExp_congr_ae (m := MeasurableSpace.comap
          (fun w : LatentSubject => (w.recur a, w.death a)) inferInstance) hnull)]
          with z hz
        simpa [horizonConditionalCensorProduct] using hz
      have htreat : ∀ᵐ z ∂P.latent,
          horizonTreatmentMechanism P a z = P.p a := by
        have hint : (∫ z, Set.indicator {w : LatentSubject | w.treatment = a}
            (fun _ => (1 : ℝ)) z ∂P.latent) = P.p a := by
          have hind : Set.indicator {w : LatentSubject | w.treatment = a}
              (fun _ => (1 : ℝ)) =
              Set.indicator {w : LatentSubject | w.treatment = a}
                (1 : LatentSubject → ℝ) := by
            ext z
            rfl
          rw [hind]
          rw [integral_indicator_one (μ := P.latent)
            (s := {w : LatentSubject | w.treatment = a})
            (by
              exact (measurable_fst.comp
                measurable_latentSubject_toCoordinates)
                (measurableSet_singleton a))]
          exact hP.assignmentLaw a
        simpa [horizonTreatmentMechanism, condExp_bot, hint]
      filter_upwards [htreat, hcensor] with z ht hc
      simp [ht, hc, hret a]
  refine ⟨?_, hinf, ?_, ?_, ?_⟩
  · intro a
    exact ⟨hret a, by simp [hret a]⟩
  · exact hscope
  · intro η hη a hfalse
    letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
    have hprod : ∀ᵐ z ∂P.latent,
        horizonConditionalCensorProduct P a z *
          horizonTreatmentMechanism P a z = 0 := by
      filter_upwards [hscope a] with z hz
      exact hz.2.2
    have hbad : ∀ᵐ z ∂P.latent, η < (0 : ℝ) := by
      filter_upwards [hfalse, hprod] with z hlt hz
      simpa [hz] using hlt
    exact (not_lt_of_ge hη.le) (Filter.Eventually.exists hbad |>.choose_spec)
  · intro ε hε a hfalse
    letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
    have : ¬ (ε < P.p a * retention P a 1) := by simp [hret a, not_lt, hε.le]
    exact this (Filter.Eventually.exists hfalse |>.choose_spec)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

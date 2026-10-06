module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalHolder
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PerturbModelClass

/-! # Packaging a critical direction as an explicit model witness -/

public section

open MeasureTheory Set ProbabilityTheory

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Once its band and Hölder estimates are supplied, the critical direction
defines the exact full-model witness used in the lower-bound theorem. -/
lemma exists_criticalPerturb_modelClass_of_bounds
    (c : ClassConstants) (P₀ : SubjectLaw) (hP₀ : ModelClass c P₀)
    (cut : CutoffData c) {u : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hband : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      c.lambdaMin ≤ midpointLambda c + criticalDirection c cut u n t ∧
        midpointLambda c + criticalDirection c cut u n t ≤ c.lambdaMax)
    (hholder : HolderSeminormLe (holderOrder c) (c.beta - holderOrder c)
      c.Llambda (fun t ↦ midpointLambda c + criticalDirection c cut u n t)) :
    let Pbase := midpointBaseline c P₀
    let lam1 := fun t : ℝ => midpointLambda c + criticalDirection c cut u n t
    ∃ hfinite : ∀ a : Arm, IsFiniteMeasure
        (treatmentPerturbIntensity Pbase lam1 a),
      let P₁ := SubjectLaw.perturbTreatment Pbase lam1 hfinite
      ModelClass c P₁ ∧
        P₁.p = Pbase.p ∧
        P₁.hazard = Pbase.hazard ∧
        P₁.lam false = Pbase.lam false ∧
        P₁.latent.map LatentSubject.censor =
          Pbase.latent.map LatentSubject.censor ∧
        (∀ a t, retention P₁ a t = retention Pbase a t) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
          P₁.lam true t = Pbase.lam true t +
            criticalDirection c cut u n t) := by
  dsimp only
  let Pbase := midpointBaseline c P₀
  let lam1 := fun t : ℝ => midpointLambda c + criticalDirection c cut u n t
  have hbaseModel : ModelClass c Pbase := midpointBaseline_modelClass c P₀ hP₀
  have hbaseLam (a : Arm) : Pbase.lam a = fun _ => midpointLambda c := by
    funext t
    exact midpointBaseline_lam c P₀ a t
  have hfinite : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity Pbase lam1 a) := by
    intro a
    cases a
    · unfold treatmentPerturbIntensity
      apply recurrenceIntensity_isFinite_of_continuous
      rw [hbaseLam false]
      exact continuous_const
    · unfold treatmentPerturbIntensity
      exact criticalDirection_intensity_isFinite c cut (midpointLambda c) u hn
  refine ⟨hfinite, ?_⟩
  let P₁ := SubjectLaw.perturbTreatment Pbase lam1 hfinite
  have hregular : ∀ a : Arm,
      AEMeasurable (if a then lam1 else Pbase.lam false)
          (volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
        (∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
          0 ≤ (if a then lam1 else Pbase.lam false) t) := by
    intro a
    cases a
    · constructor
      · rw [hbaseLam false]
        exact measurable_const.aemeasurable
      · filter_upwards [] with t
        rw [hbaseLam false]
        exact (midpoint_strict_bounds c).1.le.trans' c.lambdaMin_pos.le
    · constructor
      · change AEMeasurable
          (fun t : ℝ => midpointLambda c + criticalDirection c cut u n t)
            (volume.restrict (Set.Ioc (0 : ℝ) 1))
        exact measurable_const.aemeasurable.add
          (criticalDirection_aemeasurable_restrict c cut u hn)
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact c.lambdaMin_pos.le.trans (hband t ⟨ht.1.le, ht.2⟩).1
  have hbounds : ∀ a : Arm, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      c.lambdaMin ≤ (if a then lam1 else Pbase.lam false) t ∧
        (if a then lam1 else Pbase.lam false) t ≤ c.lambdaMax := by
    intro a t ht
    cases a
    · rw [hbaseLam false]
      exact ⟨(midpoint_strict_bounds c).1.le,
        (midpoint_strict_bounds c).2.1.le⟩
    · exact hband t ht
  have hholders : ∀ a : Arm,
      HolderSeminormLe (holderOrder c) (c.beta - holderOrder c) c.Llambda
        (if a then lam1 else Pbase.lam false) := by
    intro a
    cases a
    · rw [hbaseLam false]
      exact holderSeminormLe_const (holderOrder c) (c.beta - holderOrder c)
        c.Llambda (midpointLambda c) c.Llambda_pos.le
    · exact hholder
  have hmodel : ModelClass c P₁ :=
    SubjectLaw.perturbTreatment_modelClass c Pbase hbaseModel lam1 hfinite
      hregular hbounds hholders
  refine ⟨hmodel, rfl, rfl, rfl,
    (SubjectLaw.perturbTreatment_preserves_marginals Pbase lam1 hfinite).2.2,
    SubjectLaw.perturbTreatment_retention_eq Pbase lam1 hfinite, ?_⟩
  intro t ht
  change lam1 t = (midpointBaseline c P₀).lam true t +
    criticalDirection c cut u n t
  simpa [lam1]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

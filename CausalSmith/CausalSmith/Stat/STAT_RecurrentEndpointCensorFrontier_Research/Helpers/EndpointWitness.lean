module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.EndpointDirectionBounds
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PerturbModelClass

/-! # Explicit endpoint alternatives in the model class -/

public section

open MeasureTheory Set ProbabilityTheory

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The rate-tuned endpoint direction gives a concrete treatment perturbation
inside the full model class.  The existential proof object is retained so the
result can be used directly in the lower-bound witness. -/
lemma exists_endpointPerturb_modelClass
    (c : ClassConstants) (P₀ : SubjectLaw) (hP₀ : ModelClass c P₀)
    (cut : CutoffData c) {u : ℝ}
    (hu0 : 0 < u) (hu : u ≤ endpointModelRadius c cut)
    {n : ℕ} (hn : 1 ≤ n) :
    let Pbase := midpointBaseline c P₀
    let lam1 := fun t : ℝ => midpointLambda c +
      endpointDirection c cut u
        ((n : ℝ) ^ (-(1 / (2 * c.beta + c.kappa + 1)))) t
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
            endpointDirection c cut u
              ((n : ℝ) ^ (-(1 / (2 * c.beta + c.kappa + 1)))) t) := by
  dsimp only
  let Pbase := midpointBaseline c P₀
  let h := (n : ℝ) ^ (-(1 / (2 * c.beta + c.kappa + 1)))
  let lam1 := fun t : ℝ => midpointLambda c + endpointDirection c cut u h t
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hh0 : 0 < h := by
    exact Real.rpow_pos_of_pos hnpos _
  have hh1 : h ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · exact_mod_cast hn
    · have hden : 0 < 2 * c.beta + c.kappa + 1 := by
        linarith [c.beta_pos, c.kappa_pos]
      exact neg_nonpos.mpr (div_nonneg zero_le_one hden.le)
  have hbaseModel : ModelClass c Pbase := midpointBaseline_modelClass c P₀ hP₀
  have hbaseLam (a : Arm) : Pbase.lam a = fun _ => midpointLambda c := by
    funext t
    exact midpointBaseline_lam c P₀ a t
  have hconditions := endpointDirection_rate_model_conditions c cut hu0 hu hn
  have hfinite : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity Pbase lam1 a) := by
    intro a
    cases a
    · unfold treatmentPerturbIntensity
      apply recurrenceIntensity_isFinite_of_continuous
      rw [hbaseLam false]
      exact continuous_const
    · unfold treatmentPerturbIntensity
      apply recurrenceIntensity_isFinite_of_continuous
      exact continuous_const.add
        (endpointDirection_continuous c cut u h hh0.ne')
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
        exact
          ((midpoint_strict_bounds c).1.le.trans' c.lambdaMin_pos.le)
    · constructor
      · change AEMeasurable
          (fun t : ℝ => midpointLambda c + endpointDirection c cut u h t)
            (volume.restrict (Set.Ioc (0 : ℝ) 1))
        exact (continuous_const.add
          (endpointDirection_continuous c cut u h hh0.ne')).aemeasurable
      · filter_upwards [] with t
        simpa [Pbase, lam1, h] using
            c.lambdaMin_pos.le.trans (hconditions.1 t).1
  have hbounds : ∀ a : Arm, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      c.lambdaMin ≤ (if a then lam1 else Pbase.lam false) t ∧
        (if a then lam1 else Pbase.lam false) t ≤ c.lambdaMax := by
    intro a t ht
    cases a
    · rw [hbaseLam false]
      exact And.intro (midpoint_strict_bounds c).1.le
        (midpoint_strict_bounds c).2.1.le
    · simpa [Pbase, lam1, h] using hconditions.1 t
  have hholder : ∀ a : Arm,
      HolderSeminormLe (holderOrder c) (c.beta - holderOrder c) c.Llambda
        (if a then lam1 else Pbase.lam false) := by
    intro a
    cases a
    · rw [hbaseLam false]
      exact holderSeminormLe_const (holderOrder c) (c.beta - holderOrder c)
        c.Llambda (midpointLambda c) c.Llambda_pos.le
    · simpa [Pbase, lam1, h] using hconditions.2
  have hmodel : ModelClass c P₁ :=
    SubjectLaw.perturbTreatment_modelClass c Pbase hbaseModel lam1 hfinite
      hregular hbounds hholder
  refine ⟨hmodel, rfl, rfl, rfl,
    (SubjectLaw.perturbTreatment_preserves_marginals Pbase lam1 hfinite).2.2,
    SubjectLaw.perturbTreatment_retention_eq Pbase lam1 hfinite, ?_⟩
  intro t ht
  change lam1 t = (midpointBaseline c P₀).lam true t +
    endpointDirection c cut u
      ((n : ℝ) ^ (-(1 / (2 * c.beta + c.kappa + 1)))) t
  simpa [lam1, h]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

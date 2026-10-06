module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PromotedBoundaryNull
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PromotedIdentificationAdapter

/-!
# Stopped-mean bridge to the promoted recurrent-event model
-/

@[expose] public section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- The ModelClass boundary-null property removes the strict/non-strict
convention difference in the clinical recurrence count. -/
lemma ModelClass.strictClinicalCount_ae_eq_clinicalCount
    {c : ClassConstants} {P : SubjectLaw}
    (hP : ModelClass c P) (a : Arm) :
    strictClinicalCount (a := a) =ᵐ[P.latent]
      fun z ↦ clinicalCount z a 1 := by
  filter_upwards [hP.ae_no_recurrence_at_stopping_boundaries a] with z hz
  exact strictClinicalCount_eq_clinicalCount_of_no_boundary z a
    (fun i ↦ (hz i).1) (fun i ↦ (hz i).2.2)

/-- The promoted strict stopped-count score on a recurrence/death pair. -/
@[no_expose]
noncomputable def strictStoppedPairCount (q : RecurConfig × ℝ) : ℕ :=
  ∑ i : Fin q.1.1,
    if (q.1.2 i).1 < q.2 ∧ (q.1.2 i).1 < 1 then 1 else 0

lemma strictStoppedPairCount_eq_clinicalCount_of_no_boundary
    (z : LatentSubject) (a : Arm)
    (hdeath : ∀ i : Fin (z.recur a).1, ((z.recur a).2 i).1 ≠ z.death a)
    (hhorizon : ∀ i : Fin (z.recur a).1, ((z.recur a).2 i).1 ≠ 1) :
    strictStoppedPairCount (z.recur a, z.death a) = clinicalCount z a 1 := by
  unfold strictStoppedPairCount clinicalCount RecurConfig.countLE
  simp only [RecurConfig.paddedCountLE, finiteSamplePaddedStream]
  apply Finset.sum_congr rfl
  intro i _
  have heq :
      (((z.recur a).2 i).1 < z.death a ∧ ((z.recur a).2 i).1 < 1) ↔
        ((z.recur a).2 i).1 ≤ min 1 (z.death a) := by
    constructor
    · rintro ⟨hd, h1⟩
      exact le_min h1.le hd.le
    · intro hle
      have h1le := hle.trans (min_le_left _ _)
      have hdle := hle.trans (min_le_right _ _)
      exact ⟨lt_of_le_of_ne hdle (hdeath i),
        lt_of_le_of_ne h1le (hhorizon i)⟩
  rw [if_congr heq rfl rfl]
  congr 1
  simp [FiniteSample.count, FiniteSample.points, i.isLt]

@[fun_prop]
lemma measurable_strictStoppedPairCount : Measurable strictStoppedPairCount := by
  let F := strictStoppedPairCount
  have he (n : ℕ) : MeasurableEmbedding
      (fixedSizeEmbed (X := ℝ × ℝ) n) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x y h
      exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
    · exact measurable_fixedSizeEmbed n
    · intro s hs
      change @MeasurableSet _
        (⨅ m, (inferInstance : MeasurableSpace (Fin m → ℝ × ℝ)).map (Sigma.mk m))
        (fixedSizeEmbed n '' s)
      rw [MeasurableSpace.measurableSet_iInf]
      intro m
      change MeasurableSet (fixedSizeEmbed m ⁻¹' (fixedSizeEmbed n '' s))
      by_cases h : m = n
      · subst m
        rw [Set.preimage_image_eq s (fun x y h ↦
          eq_of_heq (Sigma.mk.inj_iff.mp h).2)]
        exact hs
      · convert MeasurableSet.empty using 1
        ext x
        simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false, iff_false]
        rintro ⟨y, _, heq⟩
        exact h (congrArg Sigma.fst heq).symm
  intro t ht
  have hpre : F ⁻¹' t = ⋃ n : ℕ,
      (Prod.map (fixedSizeEmbed (X := ℝ × ℝ) n) id) ''
        {q : (Fin n → ℝ × ℝ) × ℝ | F (⟨n, q.1⟩, q.2) ∈ t} := by
    ext ⟨⟨n, x⟩, r⟩
    constructor
    · intro h
      exact Set.mem_iUnion.mpr ⟨n, ⟨(x, r), h, rfl⟩⟩
    · rintro h
      obtain ⟨m, ⟨y, r⟩, hy, hz⟩ := Set.mem_iUnion.mp h
      cases hz
      exact hy
  rw [hpre]
  apply MeasurableSet.iUnion
  intro n
  apply ((he n).prodMap MeasurableEmbedding.id).measurableSet_image.mpr
  apply ht.preimage
  change Measurable (fun q : (Fin n → ℝ × ℝ) × ℝ ↦
    ∑ i : Fin n, if (q.1 i).1 < q.2 ∧ (q.1 i).1 < 1 then 1 else 0)
  apply Finset.measurable_sum Finset.univ
  intro i _
  have htime : Measurable (fun q : (Fin n → ℝ × ℝ) × ℝ ↦ (q.1 i).1) := by
    fun_prop
  exact Measurable.ite
    ((measurableSet_lt htime measurable_snd).inter
      (measurableSet_lt htime measurable_const))
    measurable_const measurable_const

/-- Combining the marginal adapter with boundary-nullity identifies a
promoted death-stopped mean with the paper's clinical-count expectation. -/
lemma ModelClass.lintegral_clinicalCount_eq_promoted
    {c : ClassConstants} {P : SubjectLaw}
    (hP : ModelClass c P) (a : Arm)
    (M : Causalean.Stat.RecurrentEvent.Model Unit (ℝ × ℝ))
    (hH : M.horizon = 1)
    (htime : M.time = Prod.fst)
    (hrecur :
      P.latent.map (fun z : LatentSubject ↦ z.recur a) =
        (letI : IsProbabilityMeasure M.pointLaw := M.pointProb
         finitePoissonSampleLaw M.pointLaw M.poissonRate))
    (hdeath : P.latent.map (fun z : LatentSubject ↦ z.death a) = M.deathLaw) :
    (∫⁻ z, (clinicalCount z a 1 : ℝ≥0∞) ∂P.latent) =
      M.deathStoppedCountMean := by
  letI : IsProbabilityMeasure M.pointLaw := M.pointProb
  let score : RecurConfig × ℝ → ℝ≥0∞ := fun q ↦
    (strictStoppedPairCount q : ℝ≥0∞)
  have hscore : Measurable score :=
    (measurable_of_countable (fun n : ℕ ↦ (n : ℝ≥0∞))).comp
      measurable_strictStoppedPairCount
  have hjoint :
      P.latent.map (fun z : LatentSubject ↦ (z.recur a, z.death a)) =
        (finitePoissonSampleLaw M.pointLaw M.poissonRate).prod M.deathLaw := by
    rw [armRecurrenceDeath_joint_eq_prod P a hP.recurrenceDeathIndependence,
      hrecur, hdeath]
  calc
    (∫⁻ z, (clinicalCount z a 1 : ℝ≥0∞) ∂P.latent) =
        ∫⁻ z, score (z.recur a, z.death a) ∂P.latent := by
      apply lintegral_congr_ae
      filter_upwards [hP.ae_no_recurrence_at_stopping_boundaries a] with z hz
      dsimp only [score]
      norm_cast
      exact (strictStoppedPairCount_eq_clinicalCount_of_no_boundary z a
        (fun i ↦ (hz i).1) (fun i ↦ (hz i).2.2)).symm
    _ = ∫⁻ q, score q ∂(P.latent.map
          (fun z : LatentSubject ↦ (z.recur a, z.death a))) := by
      rw [lintegral_map hscore
        ((measurable_latentSubject_recur a).prodMk
          (measurable_latentSubject_death a))]
    _ = ∫⁻ q, score q ∂((finitePoissonSampleLaw
          M.pointLaw M.poissonRate).prod M.deathLaw) := by rw [hjoint]
    _ = M.deathStoppedCountMean := by
      rw [Causalean.Stat.RecurrentEvent.Model.deathStoppedCountMean]
      simp only [score, strictStoppedPairCount, hH, htime]
      apply lintegral_congr
      intro q
      norm_cast

/-- The promoted Campbell identity now applies directly to the paper clinical
count, with no strict-boundary remainder. -/
lemma ModelClass.lintegral_clinicalCount_eq_promoted_formula
    {c : ClassConstants} {P : SubjectLaw}
    (hP : ModelClass c P) (a : Arm)
    (M : Causalean.Stat.RecurrentEvent.Model Unit (ℝ × ℝ))
    (hH : M.horizon = 1)
    (htime : M.time = Prod.fst)
    (hrecur :
      P.latent.map (fun z : LatentSubject ↦ z.recur a) =
        (letI : IsProbabilityMeasure M.pointLaw := M.pointProb
         finitePoissonSampleLaw M.pointLaw M.poissonRate))
    (hdeath : P.latent.map (fun z : LatentSubject ↦ z.death a) = M.deathLaw) :
    (∫⁻ z, (clinicalCount z a 1 : ℝ≥0∞) ∂P.latent) =
      ∫⁻ t in Set.Ico (0 : ℝ) 1,
        M.deathLaw (Set.Ici t) * (M.intensity t : ℝ≥0∞) ∂volume := by
  rw [hP.lintegral_clinicalCount_eq_promoted a M hH htime hrecur hdeath,
    M.death_stopped_poisson_mean, hH]


end CausalSmith.Stat.RecurrentEndpointCensorFrontier

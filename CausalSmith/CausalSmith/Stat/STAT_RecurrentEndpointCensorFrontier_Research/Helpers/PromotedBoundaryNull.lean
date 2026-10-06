module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.IdentificationObservables
public import Causalean.Stat.RecurrentEvent

/-!
# Boundary-null facts for the promoted recurrent-event adapter

Canonical recurrence configurations have diffuse event times.  This file
proves the fixed-boundary fact directly from the finite-Poisson Campbell
formula; it is the basic ingredient for removing strict/non-strict stopping
conventions.
-/

@[expose] public section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- Number of recurrence points whose time coordinate equals `r`. -/
@[no_expose]
noncomputable def recurrenceBoundaryCount (r : ℝ) (s : RecurConfig) : ℕ :=
  ∑ i : Fin s.1, if (s.2 i).1 = r then 1 else 0

@[fun_prop]
lemma measurable_recurrenceBoundaryCount (r : ℝ) :
    Measurable (recurrenceBoundaryCount r) := by
  intro t ht
  change @MeasurableSet _
    (⨅ n, (inferInstance : MeasurableSpace (Fin n → ℝ × ℝ)).map (Sigma.mk n))
    ((recurrenceBoundaryCount r) ⁻¹' t)
  rw [MeasurableSpace.measurableSet_iInf]
  intro n
  change MeasurableSet
    ((fun x : Fin n → ℝ × ℝ ↦ ∑ i, if (x i).1 = r then 1 else 0) ⁻¹' t)
  apply ht.preimage
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite
    (measurableSet_eq_fun
      (measurable_fst.comp (measurable_pi_apply i)) measurable_const)
    measurable_const measurable_const

/-- A recurrence intensity generated from Lebesgue density has no atom at a
fixed time. -/
lemma recurrenceIntensity_singleton (P : SubjectLaw) (a : Arm) (r : ℝ) :
    recurrenceIntensity P a {r} = 0 := by
  apply withDensity_absolutelyContinuous
  rw [Measure.restrict_apply (measurableSet_singleton r)]
  exact measure_mono_null inter_subset_left (measure_singleton r)

/-- Under the canonical finite-Poisson recurrence law, a fixed time is almost
surely absent from the finite configuration. -/
lemma canonicalRecurrenceLaw_boundaryCount_ae_zero
    (P : SubjectLaw) (a : Arm)
    [hν : IsFiniteMeasure (recurrenceIntensity P a)] (r : ℝ) :
    recurrenceBoundaryCount r =ᵐ[
      @canonicalRecurrenceLaw P a hν] 0 := by
  let ν := recurrenceIntensity P a
  let Q := normalizedFiniteMeasure ν (Measure.dirac 0)
  let R : Measure ℝ := Measure.dirac 0
  let rate := finiteMeasureMass ν
  let score : (ℝ × ℝ) → ℝ≥0∞ := fun x ↦ if x.1 = r then 1 else 0
  letI : IsProbabilityMeasure (Measure.dirac (0 : ℝ)) := inferInstance
  letI : IsProbabilityMeasure Q := by dsimp [Q]; infer_instance
  have hscore : Measurable score := by
    exact Measurable.ite
      (measurableSet_eq_fun measurable_fst measurable_const)
      measurable_const measurable_const
  have hcampbell := Causalean.Stat.RecurrentEvent.finitePoissonSample_lintegral_sum
    (Q.prod R) rate score hscore
  have hrhs : (∫⁻ x, score x ∂(((rate : ℝ≥0∞) • Q.prod R))) = 0 := by
    rw [lintegral_smul_measure]
    by_cases hzero : ν = 0
    · simp [rate, finiteMeasureMass, hzero]
    · have hQatom : Q {r} = 0 := by
        dsimp [Q]
        rw [normalizedFiniteMeasure, dif_neg hzero,
          Measure.smul_apply ((ν Set.univ)⁻¹) ν {r}]
        have hatom : ν {r} = 0 := by
          simpa only [ν] using recurrenceIntensity_singleton P a r
        rw [hatom]
        simp
      have hprod : (Q.prod R) ({r} ×ˢ (Set.univ : Set ℝ)) = 0 := by
        rw [Measure.prod_prod, hQatom, zero_mul]
      have hscoreInd : score = ({r} ×ˢ (Set.univ : Set ℝ)).indicator 1 := by
        funext x
        by_cases hx : x.1 = r <;> simp [score, hx]
      rw [hscoreInd, lintegral_indicator
        ((measurableSet_singleton r).prod MeasurableSet.univ)]
      simp [hprod]
  have hlint :
      (∫⁻ s, (recurrenceBoundaryCount r s : ℝ≥0∞)
        ∂@canonicalRecurrenceLaw P a hν) = 0 := by
    rw [show @canonicalRecurrenceLaw P a hν =
        finitePoissonSampleLaw (Q.prod R) rate by
      unfold canonicalRecurrenceLaw canonicalRecurrenceLawOf
        finiteMeasureMarkedPoissonLaw finiteMarkedPoissonSampleLaw
      simp only [one_mul, Q, R, rate, ν]]
    convert hcampbell.trans hrhs using 1
    apply lintegral_congr
    intro s
    simp only [recurrenceBoundaryCount, score]
    norm_cast
  have hmeas : Measurable
      (fun s : RecurConfig ↦ (recurrenceBoundaryCount r s : ℝ≥0∞)) :=
    (measurable_of_countable (fun n : ℕ ↦ (n : ℝ≥0∞))).comp
      (measurable_recurrenceBoundaryCount r)
  have hcoe := (lintegral_eq_zero_iff' hmeas.aemeasurable).mp hlint
  filter_upwards [hcoe] with s hs
  change (recurrenceBoundaryCount r s : ℝ≥0∞) = 0 at hs
  exact_mod_cast hs

/-- The boundary count is jointly measurable in a finite configuration and a
candidate boundary time. -/
@[fun_prop]
lemma measurable_recurrenceBoundaryCount_pair :
    Measurable (fun q : RecurConfig × ℝ ↦ recurrenceBoundaryCount q.2 q.1) := by
  let F := fun q : RecurConfig × ℝ ↦ recurrenceBoundaryCount q.2 q.1
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
    ∑ i : Fin n, if (q.1 i).1 = q.2 then 1 else 0)
  apply Finset.measurable_sum Finset.univ
  intro i _
  exact Measurable.ite
    (measurableSet_eq_fun
      (measurable_fst.comp ((measurable_pi_apply i).comp measurable_fst))
      measurable_snd)
    measurable_const measurable_const

/-- A canonical diffuse recurrence configuration cannot hit an independent
random boundary time. -/
lemma canonicalRecurrenceLaw_ae_no_independent_boundary
    (P : SubjectLaw) (a : Arm)
    [hν : IsFiniteMeasure (recurrenceIntensity P a)]
    (b : LatentSubject → ℝ) (hb : Measurable b)
    (hind : IndepFun (fun z : LatentSubject ↦ z.recur a) b P.latent)
    (hmarg : P.latent.map (fun z : LatentSubject ↦ z.recur a) =
      @canonicalRecurrenceLaw P a hν) :
    ∀ᵐ z ∂P.latent, ∀ i : Fin (z.recur a).1,
      ((z.recur a).2 i).1 ≠ b z := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let μr := P.latent.map (fun z : LatentSubject ↦ z.recur a)
  let μb := P.latent.map b
  have hset : MeasurableSet
      {q : RecurConfig × ℝ | recurrenceBoundaryCount q.2 q.1 = 0} :=
    measurableSet_eq_fun measurable_recurrenceBoundaryCount_pair measurable_const
  have hfixed : ∀ r : ℝ, ∀ᵐ s ∂μr, recurrenceBoundaryCount r s = 0 := by
    intro r
    change ∀ᵐ s ∂P.latent.map (fun z : LatentSubject ↦ z.recur a),
      recurrenceBoundaryCount r s = 0
    rw [hmarg]
    exact canonicalRecurrenceLaw_boundaryCount_ae_zero P a r
  have hiter : ∀ᵐ s ∂μr, ∀ᵐ r ∂μb,
      recurrenceBoundaryCount r s = 0 := by
    rw [Measure.ae_ae_comm hset]
    exact Filter.Eventually.of_forall hfixed
  have hprod : ∀ᵐ q ∂μr.prod μb, recurrenceBoundaryCount q.2 q.1 = 0 :=
    (Measure.ae_prod_iff_ae_ae hset).2 hiter
  have hjoint := hind.map_prod_eq_prod_map_map
    (measurable_latentSubject_recur a).aemeasurable hb.aemeasurable
  rw [← hjoint] at hprod
  have hpull := (ae_map_iff
    ((measurable_latentSubject_recur a).prodMk hb).aemeasurable hset).1 hprod
  filter_upwards [hpull] with z hz
  intro i hi
  have hterm : (1 : ℕ) ≤ recurrenceBoundaryCount (b z) (z.recur a) := by
    unfold recurrenceBoundaryCount
    calc
      1 = (if ((z.recur a).2 i).1 = b z then 1 else 0) := by simp [hi]
      _ ≤ ∑ j : Fin (z.recur a).1,
          if ((z.recur a).2 j).1 = b z then 1 else 0 :=
        Finset.single_le_sum (f := fun j : Fin (z.recur a).1 ↦
          if ((z.recur a).2 j).1 = b z then 1 else 0)
          (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  omega

/-- Under the model-class recurrence/death independence atom, recurrence
times almost surely avoid the latent death time. -/
lemma ModelClass.ae_no_recurrence_at_death {c : ClassConstants} {P : SubjectLaw}
    (hP : ModelClass c P) (a : Arm) :
    ∀ᵐ z ∂P.latent, ∀ i : Fin (z.recur a).1,
      ((z.recur a).2 i).1 ≠ z.death a := by
  rcases hP.poissonRecurrence a with ⟨_, _, hν, hmarg⟩
  exact canonicalRecurrenceLaw_ae_no_independent_boundary P a
    (fun z ↦ z.death a) (measurable_latentSubject_death a)
    (hP.recurrenceDeathIndependence a) hmarg

/-- Under independent censoring, recurrence times almost surely avoid the
finite censoring horizon. -/
lemma ModelClass.ae_no_recurrence_at_censorHorizon
    {c : ClassConstants} {P : SubjectLaw}
    (hP : ModelClass c P) (a : Arm) :
    ∀ᵐ z ∂P.latent, ∀ i : Fin (z.recur a).1,
      ((z.recur a).2 i).1 ≠ censorHorizon z a := by
  rcases hP.poissonRecurrence a with ⟨_, _, hν, hmarg⟩
  have hind : IndepFun (fun z : LatentSubject ↦ z.recur a)
      (fun z : LatentSubject ↦ censorHorizon z a) P.latent := by
    have hraw := (hP.independentCensoring a).symm.comp
      measurable_fst
      (show Measurable (fun x : ENNReal ↦ if x = ⊤ then (1 : ℝ) else min x.toReal 1) by
        exact Measurable.ite (measurableSet_singleton ⊤)
          measurable_const (ENNReal.measurable_toReal.min measurable_const))
    change IndepFun
      (Prod.fst ∘ fun z : LatentSubject ↦ (z.recur a, z.death a))
      ((fun x : ENNReal ↦ if x = ⊤ then (1 : ℝ) else min x.toReal 1) ∘
        fun z : LatentSubject ↦ z.censor a) P.latent
    exact hraw
  exact canonicalRecurrenceLaw_ae_no_independent_boundary P a
    (fun z ↦ censorHorizon z a)
    (measurable_censorHorizon.comp (measurable_id.prodMk measurable_const))
    hind hmarg

/-- Canonical recurrence times almost surely avoid the deterministic study
horizon. -/
lemma ModelClass.ae_no_recurrence_at_horizon {c : ClassConstants} {P : SubjectLaw}
    (hP : ModelClass c P) (a : Arm) :
    ∀ᵐ z ∂P.latent, ∀ i : Fin (z.recur a).1,
      ((z.recur a).2 i).1 ≠ 1 := by
  rcases hP.poissonRecurrence a with ⟨_, _, hν, hmarg⟩
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  exact canonicalRecurrenceLaw_ae_no_independent_boundary P a
    (fun _ ↦ (1 : ℝ)) measurable_const
    (indepFun_const_right (fun z : LatentSubject ↦ z.recur a) (1 : ℝ)) hmarg

/-- All three stopping boundaries used by the paper and promoted models are
almost surely free of recurrence points. -/
lemma ModelClass.ae_no_recurrence_at_stopping_boundaries
    {c : ClassConstants} {P : SubjectLaw}
    (hP : ModelClass c P) (a : Arm) :
    ∀ᵐ z ∂P.latent, ∀ i : Fin (z.recur a).1,
      ((z.recur a).2 i).1 ≠ z.death a ∧
      ((z.recur a).2 i).1 ≠ censorHorizon z a ∧
      ((z.recur a).2 i).1 ≠ 1 := by
  filter_upwards [hP.ae_no_recurrence_at_death a,
    hP.ae_no_recurrence_at_censorHorizon a,
    hP.ae_no_recurrence_at_horizon a] with z hd hc hh
  intro i
  exact ⟨hd i, hc i, hh i⟩


end CausalSmith.Stat.RecurrentEndpointCensorFrontier

module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.IntensityKL
public import Causalean.Mathlib.InformationTheory.KLBind
public import Causalean.Mathlib.Probability.Kernel.GraphMapProd

/-!
# Exact stopped-recurrence KL bridges

This module identifies a fixed-exit stopped canonical recurrence law with the
finite marked Poisson law of the restricted intensity.  It also gives the
exact common-exit composition-product chain rule on observed histories.
-/

@[expose] public section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

lemma timeCutPartition_cellSet_true (x : ℝ) :
    (timeCutPartition x).cellSet true = Set.Iic x := by
  ext t
  simp [FiniteMeasurablePartition.cellSet, timeCutPartition]

lemma cellMass_smul_cellObservationLaw
    {X ι : Type*} [MeasurableSpace X] [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (p : FiniteMeasurablePartition X ι)
    (P : Measure X) [IsProbabilityMeasure P] (j : ι) :
    p.cellMass P j • p.cellObservationLaw P j = P.restrict (p.cellSet j) := by
  classical
  unfold FiniteMeasurablePartition.cellMass
    FiniteMeasurablePartition.cellObservationLaw
  split_ifs with h
  · rw [h]
    simp [Measure.restrict_eq_zero.mpr h]
  · ext s hs
    rw [Measure.smul_apply, Measure.smul_apply]
    change ((P (p.cellSet j)).toNNReal : ℝ≥0∞) *
      ((P (p.cellSet j))⁻¹ * (P.restrict (p.cellSet j)) s) = _
    rw [ENNReal.coe_toNNReal (measure_ne_top P _)]
    rw [← mul_assoc]
    rw [ENNReal.mul_inv_cancel h (measure_ne_top P _)]
    simp

lemma normalizedFiniteMeasure_reconstruct
    {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν]
    (P₀ : Measure X) [IsProbabilityMeasure P₀] :
    finiteMeasureMass ν • normalizedFiniteMeasure ν P₀ = ν := by
  classical
  by_cases hν : ν = 0
  · subst ν
    simp [finiteMeasureMass, normalizedFiniteMeasure]
  · ext s hs
    rw [normalizedFiniteMeasure, dif_neg hν, Measure.smul_apply,
      Measure.smul_apply]
    change ((finiteMeasureMass ν : ℝ≥0) : ℝ≥0∞) *
      ((ν Set.univ)⁻¹ * ν s) = ν s
    rw [finiteMeasureMass,
      ENNReal.coe_toNNReal (ne_of_lt (measure_lt_top ν Set.univ)),
      ← mul_assoc, ENNReal.mul_inv_cancel]
    · simp
    · exact fun h => hν (Measure.measure_univ_eq_zero.mp h)
    · exact ne_of_lt (measure_lt_top ν Set.univ)

private lemma poissonMeasure_zero_local : poissonMeasure 0 = Measure.dirac 0 := by
  ext s hs
  rw [poissonMeasure, Measure.sum_apply _ hs]
  refine (tsum_eq_single 0 ?_).trans ?_
  · intro n hn
    rw [Measure.smul_apply, smul_eq_mul]
    simp [zero_pow hn]
  · simp

lemma finiteMarkedPoissonSampleLaw_zero_local
    {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (R : Measure ℝ) [IsProbabilityMeasure R] :
    finiteMarkedPoissonSampleLaw P R 0 =
      finiteMarkedPoissonSampleLaw Q R 0 := by
  unfold finiteMarkedPoissonSampleLaw finitePoissonSampleLaw
    poissonIIDStreamLaw
  rw [poissonMeasure_zero_local]
  have hconst : (streamToFiniteSample ∘ fun y : ℕ → X × ℝ => (0, y)) =
        fun _ => fixedSizeEmbed 0 (fun i => Fin.elim0 i) := by
    funext y
    have hf : (fun i : Fin 0 => y i) = (fun i => Fin.elim0 i) :=
      Subsingleton.elim _ _
    exact congrArg (Sigma.mk 0) hf
  calc
    Measure.map streamToFiniteSample
        ((Measure.dirac 0).prod (iidStreamLaw (P.prod R))) =
        Measure.map (streamToFiniteSample ∘ Prod.mk 0)
          (iidStreamLaw (P.prod R)) := by
      rw [Measure.dirac_prod]
      exact Measure.map_map measurable_streamToFiniteSample
        (measurable_const.prodMk measurable_id)
    _ = Measure.dirac (fixedSizeEmbed 0 (fun i => Fin.elim0 i)) := by
      rw [hconst, Measure.map_const, measure_univ, one_smul]
    _ = Measure.map (streamToFiniteSample ∘ Prod.mk 0)
          (iidStreamLaw (Q.prod R)) := by
      rw [hconst, Measure.map_const, measure_univ, one_smul]
    _ = Measure.map streamToFiniteSample
        ((Measure.dirac 0).prod (iidStreamLaw (Q.prod R))) := by
      rw [Measure.dirac_prod]
      exact (Measure.map_map measurable_streamToFiniteSample
        (measurable_const.prodMk measurable_id)).symm

lemma finiteMeasureMarkedPoissonLaw_smul_probability_eq
    {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    (P₀ : Measure X) [IsProbabilityMeasure P₀]
    (R : Measure ℝ) [IsProbabilityMeasure R] (r : ℝ≥0) :
    finiteMeasureMarkedPoissonLaw (r • P) P₀ R 1 =
      finiteMarkedPoissonSampleLaw P R r := by
  classical
  by_cases hr : r = 0
  · subst r
    unfold finiteMeasureMarkedPoissonLaw
    simp only [normalizedFiniteMeasure, finiteMeasureMass, zero_smul,
      Measure.coe_zero, Pi.zero_apply, ENNReal.toNNReal_zero, one_mul]
    exact finiteMarkedPoissonSampleLaw_zero_local P₀ P R
  · have hmeasure : (r • P : Measure X) ≠ 0 := by
      intro h
      have hu := congrArg (fun μ : Measure X => μ Set.univ) h
      simp [Measure.smul_apply, hr] at hu
    have hnorm : normalizedFiniteMeasure (r • P) P₀ = P := by
      unfold normalizedFiniteMeasure
      rw [dif_neg hmeasure]
      ext s hs
      rw [Measure.smul_apply, Measure.smul_apply]
      simp only [measure_univ]
      change (((r : ℝ≥0∞) * 1)⁻¹) * ((r : ℝ≥0∞) * P s) = P s
      rw [mul_one, ← mul_assoc]
      rw [ENNReal.inv_mul_cancel]
      · simp
      · exact_mod_cast hr
      · simp
    have hmass : ((r • P : Measure X) Set.univ).toNNReal = r := by
      simp [Measure.smul_apply]
    unfold finiteMeasureMarkedPoissonLaw
    simpa only [hnorm, finiteMeasureMass, hmass, one_mul]

lemma finiteMeasureMarkedPoissonLaw_congr
    {X : Type*} [MeasurableSpace X]
    {ν μ : Measure X} [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    (h : ν = μ)
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R] (r : ℝ≥0) :
    finiteMeasureMarkedPoissonLaw ν P R r =
      finiteMeasureMarkedPoissonLaw μ P R r := by
  subst μ
  rfl

lemma canonicalRecurrenceLawOf_map_stopAt_restrict
    (x : ℝ) (ν : Measure ℝ) [IsFiniteMeasure ν]
    (P₀ : Measure ℝ) [IsProbabilityMeasure P₀] :
    Measure.map (RecurConfig.stopAt x) (canonicalRecurrenceLawOf ν) =
      finiteMeasureMarkedPoissonLaw (ν.restrict (Set.Iic x))
        P₀ (Measure.dirac 0) 1 := by
  let P := normalizedFiniteMeasure ν (Measure.dirac 0)
  let p := timeCutPartition x
  have hrecover : finiteMeasureMass ν • P = ν := by
    exact normalizedFiniteMeasure_reconstruct ν (Measure.dirac 0)
  have hrestricted :
      (finiteMeasureMass ν * p.cellMass P true) • p.cellObservationLaw P true =
        ν.restrict (Set.Iic x) := by
    rw [← timeCutPartition_cellSet_true x]
    calc
      _ = finiteMeasureMass ν •
          (p.cellMass P true • p.cellObservationLaw P true) := by
            rw [mul_smul]
      _ = finiteMeasureMass ν • P.restrict (p.cellSet true) := by
            rw [cellMass_smul_cellObservationLaw]
      _ = (finiteMeasureMass ν • P).restrict (p.cellSet true) := by
            rw [Measure.restrict_smul]
      _ = ν.restrict (p.cellSet true) := congrArg
            (fun μ : Measure ℝ => μ.restrict (p.cellSet true)) hrecover
  rw [canonicalRecurrenceLawOf_map_stopAt]
  calc
    _ = finiteMeasureMarkedPoissonLaw
        ((finiteMeasureMass ν * p.cellMass P true) •
          p.cellObservationLaw P true)
        P₀ (Measure.dirac 0) 1 :=
      (finiteMeasureMarkedPoissonLaw_smul_probability_eq
        (p.cellObservationLaw P true) P₀ (Measure.dirac 0)
        (finiteMeasureMass ν * p.cellMass P true)).symm
    _ = finiteMeasureMarkedPoissonLaw (ν.restrict (Set.Iic x))
        P₀ (Measure.dirac 0) 1 :=
      finiteMeasureMarkedPoissonLaw_congr hrestricted
        P₀ (Measure.dirac 0) 1

/-! ## Common exit-record chain rule -/

/-- The part of an observed history that is shared by the baseline and a
recurrence-only perturbation: assignment, exit time, and death indicator. -/
abbrev ExitRecord := Arm × (ℝ × Bool)

/-- Assemble a shared exit record and a stopped recurrence configuration into
an observed history. -/
def ObsHistory.ofExitRecur (q : ExitRecord × RecurConfig) : ObsHistory where
  treatment := q.1.1
  exit := q.1.2.1
  deathInd := q.1.2.2
  recur := q.2

/-- Split an observed history into its shared exit record and stopped
recurrence configuration. -/
def ObsHistory.toExitRecur (o : ObsHistory) : ExitRecord × RecurConfig :=
  ((o.treatment, o.exit, o.deathInd), o.recur)

@[simp]
lemma ObsHistory.toExitRecur_ofExitRecur (q : ExitRecord × RecurConfig) :
    ObsHistory.toExitRecur (ObsHistory.ofExitRecur q) = q := rfl

@[simp]
lemma ObsHistory.ofExitRecur_toExitRecur (o : ObsHistory) :
    ObsHistory.ofExitRecur (ObsHistory.toExitRecur o) = o := by
  cases o
  rfl

/-- Assembly of the exit record and stopped recurrence is measurable. -/
@[fun_prop]
lemma ObsHistory.measurable_ofExitRecur : Measurable ObsHistory.ofExitRecur := by
  rw [show Measurable ObsHistory.ofExitRecur ↔
      Measurable (ObsHistory.toCoordinates ∘ ObsHistory.ofExitRecur) by
    exact ⟨fun h => measurable_obsHistory_toCoordinates.comp h,
      fun h => by
        rw [measurable_iff_comap_le]
        change MeasurableSpace.comap ObsHistory.ofExitRecur
          (MeasurableSpace.comap ObsHistory.toCoordinates inferInstance) ≤ _
        rw [MeasurableSpace.comap_comp]
        exact h.comap_le⟩]
  exact (measurable_fst.comp measurable_fst).prodMk
    (((measurable_fst.comp measurable_snd).comp measurable_fst).prodMk
      (((measurable_snd.comp measurable_snd).comp measurable_fst).prodMk
        measurable_snd))

/-- Splitting an observed history into exit and recurrence coordinates is
measurable. -/
@[fun_prop]
lemma ObsHistory.measurable_toExitRecur :
    Measurable ObsHistory.toExitRecur := by
  have h := measurable_obsHistory_toCoordinates
  exact ((measurable_fst.comp h).prodMk
    ((measurable_fst.comp (measurable_snd.comp h)).prodMk
      (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp h))))).prodMk
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp h)))

/-- Assembly is a measurable embedding, so it preserves KL exactly. -/
lemma ObsHistory.measurableEmbedding_ofExitRecur :
    MeasurableEmbedding ObsHistory.ofExitRecur := by
  apply MeasurableEmbedding.of_measurable_inverse
    ObsHistory.measurable_ofExitRecur
  · rw [Set.range_eq_univ.mpr]
    · exact MeasurableSet.univ
    · intro o
      exact ⟨ObsHistory.toExitRecur o, ObsHistory.ofExitRecur_toExitRecur o⟩
  · exact ObsHistory.measurable_toExitRecur
  · exact ObsHistory.toExitRecur_ofExitRecur

/-- The assignment, exit time, and death indicator extracted from a latent
subject's observed history. -/
noncomputable def latentExitRecord (z : LatentSubject) : ExitRecord :=
  (ObsHistory.toExitRecur (observe z)).1

/-- The stopped assigned-arm recurrence extracted from a latent subject. -/
noncomputable def latentStoppedRecur (z : LatentSubject) : RecurConfig :=
  (ObsHistory.toExitRecur (observe z)).2

@[fun_prop]
lemma measurable_latentExitRecord : Measurable latentExitRecord :=
  measurable_fst.comp (ObsHistory.measurable_toExitRecur.comp measurable_observe)

@[fun_prop]
lemma measurable_latentStoppedRecur : Measurable latentStoppedRecur :=
  measurable_snd.comp (ObsHistory.measurable_toExitRecur.comp measurable_observe)

/-- The exit-record marginal of a subject law. -/
noncomputable def exitRecordLaw (P : SubjectLaw) : Measure ExitRecord :=
  P.latent.map latentExitRecord

/-- The joint exit-record/stopped-recurrence law before reassembling the
observed-history structure. -/
noncomputable def exitStoppedLaw (P : SubjectLaw) :
    Measure (ExitRecord × RecurConfig) :=
  P.latent.map (fun z => (latentExitRecord z, latentStoppedRecur z))

/-- The exit-record law is the first marginal of the joint exit and stopped
recurrence law. -/
lemma exitRecordLaw_eq_fst_exitStoppedLaw (P : SubjectLaw) :
    exitRecordLaw P = (exitStoppedLaw P).fst := by
  unfold exitRecordLaw exitStoppedLaw Measure.fst
  rw [Measure.map_map measurable_fst
    (measurable_latentExitRecord.prodMk measurable_latentStoppedRecur)]
  rfl

/-- Every observed law is exactly the assembly pushforward of its joint exit
record and stopped recurrence law. -/
lemma observedLaw_eq_map_exitStoppedLaw (P : SubjectLaw) :
    observedLaw P = (exitStoppedLaw P).map ObsHistory.ofExitRecur := by
  unfold observedLaw exitStoppedLaw
  rw [Measure.map_map ObsHistory.measurable_ofExitRecur
    (measurable_latentExitRecord.prodMk measurable_latentStoppedRecur)]
  congr 1

/-- With a common assignment/death/censor exit law, exact observed-history KL
is the common-base average of the stopped-recurrence fibre KL. -/
lemma klDiv_common_exit_recurrence_chainRule
    (m : Measure ExitRecord) [IsFiniteMeasure m]
    (κ η : Kernel ExitRecord RecurConfig)
    [IsFiniteKernel κ] [IsFiniteKernel η]
    (hκη : ∀ᵐ e ∂m, κ e ≪ η e) :
    InformationTheory.klDiv
        ((m ⊗ₘ κ).map ObsHistory.ofExitRecur)
        ((m ⊗ₘ η).map ObsHistory.ofExitRecur) =
      ∫⁻ e, InformationTheory.klDiv (κ e) (η e) ∂m := by
  calc
    _ = InformationTheory.klDiv (m ⊗ₘ κ) (m ⊗ₘ η) :=
      Causalean.Mathlib.InformationTheory.Measure.klDiv_map_measurableEmbedding
        (μ := m ⊗ₘ κ) (ν := m ⊗ₘ η)
        ObsHistory.measurableEmbedding_ofExitRecur
    _ = _ :=
      Causalean.Mathlib.InformationTheory.Measure.klDiv_compProd_right_of_forall_ac
        (μ := m) (κ := κ) (η := η) hκη

/-! ## Canonical stopped-recurrence kernels -/

/-- The arm-indexed kernel of canonical full recurrence configurations. -/
noncomputable def canonicalArmRecurrenceKernel
    (ν : Arm → Measure ℝ)
    (hfinite : ∀ a, IsFiniteMeasure (ν a)) : Kernel Arm RecurConfig := by
  letI : ∀ a, IsFiniteMeasure (ν a) := hfinite
  exact Kernel.ofFunOfCountable (fun a => canonicalRecurrenceLawOf (ν a))

lemma canonicalArmRecurrenceKernel_apply
    (ν : Arm → Measure ℝ) (hfinite : ∀ a, IsFiniteMeasure (ν a)) (a : Arm) :
    canonicalArmRecurrenceKernel ν hfinite a = canonicalRecurrenceLawOf (ν a) := by
  simp [canonicalArmRecurrenceKernel, Kernel.ofFunOfCountable, Kernel.coe_mk]

lemma canonicalArmRecurrenceKernel_isMarkov
    (ν : Arm → Measure ℝ) (hfinite : ∀ a, IsFiniteMeasure (ν a)) :
    IsMarkovKernel (canonicalArmRecurrenceKernel ν hfinite) := by
  refine ⟨fun a => ?_⟩
  rw [canonicalArmRecurrenceKernel_apply]
  letI : IsFiniteMeasure (ν a) := hfinite a
  unfold canonicalRecurrenceLawOf
  infer_instance

/-- Jointly measurable stopping of an exit-record/configuration pair. -/
@[fun_prop]
lemma measurable_exitStop :
    Measurable (fun q : ExitRecord × RecurConfig => q.2.stopAt q.1.2.1) := by
  exact RecurConfig.measurable_stopAt.comp
    (((measurable_fst.comp measurable_snd).comp measurable_fst).prodMk measurable_snd)

/-- Given an exit record, select its assigned-arm canonical recurrence law and
stop the resulting configuration at the recorded exit time. -/
noncomputable def stoppedRecurrenceKernel
    (ν : Arm → Measure ℝ)
    (hfinite : ∀ a, IsFiniteMeasure (ν a)) : Kernel ExitRecord RecurConfig :=
  let armKernel := canonicalArmRecurrenceKernel ν hfinite
  let selected := armKernel.comap (fun e : ExitRecord => e.1) measurable_fst
  (Kernel.id.prod selected).map
    (fun q : ExitRecord × RecurConfig => q.2.stopAt q.1.2.1)

lemma stoppedRecurrenceKernel_isMarkov
    (ν : Arm → Measure ℝ) (hfinite : ∀ a, IsFiniteMeasure (ν a)) :
    IsMarkovKernel (stoppedRecurrenceKernel ν hfinite) := by
  letI : IsMarkovKernel (canonicalArmRecurrenceKernel ν hfinite) :=
    canonicalArmRecurrenceKernel_isMarkov ν hfinite
  let hfst : Measurable (fun e : ExitRecord => e.1) := measurable_fst
  let selected : Kernel ExitRecord RecurConfig :=
    (canonicalArmRecurrenceKernel ν hfinite).comap
      (fun e : ExitRecord => e.1) hfst
  letI : IsMarkovKernel selected := inferInstance
  exact Kernel.IsMarkovKernel.map (Kernel.id.prod selected) measurable_exitStop

/-- Each stopped-recurrence kernel fibre is the fixed-exit pushforward of the
assigned arm's canonical full recurrence law. -/
lemma stoppedRecurrenceKernel_apply
    (ν : Arm → Measure ℝ) (hfinite : ∀ a, IsFiniteMeasure (ν a))
    (e : ExitRecord) :
    stoppedRecurrenceKernel ν hfinite e =
      Measure.map (RecurConfig.stopAt e.2.1) (canonicalRecurrenceLawOf (ν e.1)) := by
  letI : ∀ a, IsFiniteMeasure (ν a) := hfinite
  letI : IsMarkovKernel (canonicalArmRecurrenceKernel ν hfinite) :=
    canonicalArmRecurrenceKernel_isMarkov ν hfinite
  let hfst : Measurable (fun e : ExitRecord => e.1) := measurable_fst
  letI : IsMarkovKernel ((canonicalArmRecurrenceKernel ν hfinite).comap
      (fun e : ExitRecord => e.1) hfst) := inferInstance
  letI : IsFiniteMeasure (ν e.1) := hfinite e.1
  letI : IsProbabilityMeasure (canonicalRecurrenceLawOf (ν e.1)) := by
    unfold canonicalRecurrenceLawOf
    infer_instance
  unfold stoppedRecurrenceKernel
  rw [Kernel.map_apply _ measurable_exitStop, Kernel.prod_apply,
    Kernel.id_apply, Kernel.comap_apply, canonicalArmRecurrenceKernel_apply,
    Measure.dirac_prod]
  calc
    _ = Measure.map
        ((fun q : ExitRecord × RecurConfig => q.2.stopAt q.1.2.1) ∘ Prod.mk e)
        (canonicalRecurrenceLawOf (ν e.1)) :=
      Measure.map_map measurable_exitStop measurable_prodMk_left
    _ = _ := rfl

/-- Averaging a cumulative nonnegative cost through a random exit equals the
tail-probability-weighted integral of its local cost.  This is the Tonelli step
that turns fixed-exit restricted-intensity KL into the survival-retention
integral once the exit tail is identified. -/
lemma lintegral_setLIntegral_Iic_eq_tail
    (μ : Measure ℝ) [SFinite μ]
    (k : ℝ → ℝ≥0∞) (hk : Measurable k) :
    (∫⁻ x, ∫⁻ t in Set.Iic x, k t ∂volume ∂μ) =
      ∫⁻ t, μ (Set.Ici t) * k t ∂volume := by
  let f : ℝ → ℝ → ℝ≥0∞ := fun x t => if t ≤ x then k t else 0
  have hf : Measurable (Function.uncurry f) := by
    apply Measurable.ite
    · exact measurableSet_le measurable_snd measurable_fst
    · exact hk.comp measurable_snd
    · exact measurable_const
  calc
    _ = ∫⁻ x, ∫⁻ t, f x t ∂volume ∂μ := by
      congr 1
      funext x
      rw [← MeasureTheory.lintegral_indicator measurableSet_Iic]
      apply MeasureTheory.lintegral_congr
      intro t
      simp [f, Set.indicator, Set.mem_Iic]
    _ = ∫⁻ t, ∫⁻ x, f x t ∂μ ∂volume :=
      MeasureTheory.lintegral_lintegral_swap hf.aemeasurable
    _ = _ := by
      congr 1
      funext t
      have hfun : (fun x => f x t) =
          (Set.Ici t).indicator (fun _ => k t) := by
        funext x
        simp [f, Set.indicator, Set.mem_Ici]
      rw [hfun]
      rw [MeasureTheory.lintegral_indicator measurableSet_Ici]
      simp [mul_comm]

/-- The scalar censoring horizon map, separated from the latent record. -/
noncomputable def censorHorizonValue (c : ENNReal) : ℝ :=
  if c = ⊤ then 1 else min c.toReal 1

@[fun_prop]
lemma measurable_censorHorizonValue : Measurable censorHorizonValue := by
  unfold censorHorizonValue
  apply Measurable.ite
  · exact measurableSet_eq_fun measurable_id measurable_const
  · exact measurable_const
  · exact Measurable.min ENNReal.measurable_toReal measurable_const

lemma censorHorizon_eq_value (z : LatentSubject) (a : Arm) :
    censorHorizon z a = censorHorizonValue (z.censor a) := rfl

/-- On the study horizon, surviving the finite censor horizon is equivalent
to surviving the original extended nonnegative censor time. -/
lemma le_censorHorizonValue_iff (c : ENNReal) (t : ℝ)
    (_ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t ≤ censorHorizonValue c ↔ ENNReal.ofReal t ≤ c := by
  unfold censorHorizonValue
  by_cases hc : c = ⊤
  · simp [hc, ht1]
  · rw [if_neg hc, le_min_iff]
    constructor
    · intro h
      exact (ENNReal.ofReal_le_iff_le_toReal hc).2 h.1
    · intro h
      exact ⟨(ENNReal.ofReal_le_iff_le_toReal hc).1 h, ht1⟩

/-- Under the model's death/censor independence, the probability of remaining
under observation through time `t` is exactly survival times retention. -/
lemma exitTail_eq_survival_mul_retention
    (P : SubjectLaw) (hdeath : DeathHazard P)
    (hcensor : IndependentCensoring P)
    (a : Arm) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    P.latent.real {z | t ≤ min (z.death a) (censorHorizon z a)} =
      survival P a t * retention P a t := by
  have hind : IndepFun (fun z : LatentSubject => censorHorizon z a)
      (fun z => z.death a) P.latent := by
    have h := (hcensor a).comp measurable_censorHorizonValue measurable_snd
    simpa only [Function.comp_def, censorHorizon_eq_value] using h
  have hevent : {z : LatentSubject | t ≤ min (z.death a) (censorHorizon z a)} =
      (fun z => censorHorizon z a) ⁻¹' Set.Ici t ∩
        (fun z => z.death a) ⁻¹' Set.Ici t := by
    ext z
    simp [and_comm]
  have hprod := hind.measure_inter_preimage_eq_mul
    (Set.Ici t) (Set.Ici t) measurableSet_Ici measurableSet_Ici
  rw [hevent, measureReal_def, hprod, ENNReal.toReal_mul]
  · have hcset : (fun z : LatentSubject => censorHorizon z a) ⁻¹' Set.Ici t =
        {z | ENNReal.ofReal t ≤ z.censor a} := by
      ext z
      exact le_censorHorizonValue_iff (z.censor a) t ht.1 ht.2
    rw [hcset]
    change P.latent.real {z | ENNReal.ofReal t ≤ z.censor a} *
      P.latent.real ((fun z => z.death a) ⁻¹' Set.Ici t) = _
    have hd := hdeath.2.2.2.1 a t ht
    change P.latent.real ((fun z => z.death a) ⁻¹' Set.Ici t) =
      survival P a t at hd
    rw [hd]
    simp only [retention]
    ring

/-! ## Product-constructor graph factorization -/

/-- Compute the observed exit record directly from assignment, death, and
censor blocks, without introducing recurrence coordinates. -/
noncomputable def rawExitRecord
    (q : Arm × ((Arm → ℝ) × (Arm → ENNReal))) : ExitRecord :=
  let a := q.1
  let x := min (q.2.1 a) (censorHorizonValue (q.2.2 a))
  (a, x, decide (q.2.1 a ≤ censorHorizonValue (q.2.2 a)))

@[fun_prop]
lemma measurable_rawExitRecord : Measurable rawExitRecord := by
  unfold rawExitRecord
  have ha : Measurable
      (fun q : Arm × ((Arm → ℝ) × (Arm → ENNReal)) => q.1) := measurable_fst
  have hevalD : Measurable (fun q : (Arm → ℝ) × Arm => q.1 q.2) := by
    apply measurable_from_prod_countable_left
    intro a
    exact measurable_pi_apply a
  have hd : Measurable
      (fun q : Arm × ((Arm → ℝ) × (Arm → ENNReal)) => q.2.1 q.1) :=
    hevalD.comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)
  have hevalC : Measurable (fun q : (Arm → ENNReal) × Arm => q.1 q.2) := by
    apply measurable_from_prod_countable_left
    intro a
    exact measurable_pi_apply a
  have hc : Measurable
      (fun q : Arm × ((Arm → ℝ) × (Arm → ENNReal)) =>
        censorHorizonValue (q.2.2 q.1)) :=
    measurable_censorHorizonValue.comp
      (hevalC.comp ((measurable_snd.comp measurable_snd).prodMk measurable_fst))
  exact ha.prodMk ((hd.min hc).prodMk
    (Measurable.ite (measurableSet_le hd hc) measurable_const measurable_const))

/-- Select the assigned recurrence configuration from a recurrence family and
stop it at the supplied exit record. -/
noncomputable def stoppedFamilyMechanism
    (q : ExitRecord × (Arm → RecurConfig)) : RecurConfig :=
  (q.2 q.1.1).stopAt q.1.2.1

@[fun_prop]
lemma measurable_stoppedFamilyMechanism : Measurable stoppedFamilyMechanism := by
  have heval0 : Measurable
      (fun q : (Arm → RecurConfig) × Arm => q.1 q.2) := by
    apply measurable_from_prod_countable_left
    intro a
    exact measurable_pi_apply a
  have heval : Measurable
      (fun q : ExitRecord × (Arm → RecurConfig) => q.2 q.1.1) :=
    heval0.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
  exact RecurConfig.measurable_stopAt.comp
    (((measurable_fst.comp measurable_snd).comp measurable_fst).prodMk heval)

/-- The graph-mechanism kernel generated by an independent canonical
recurrence family is exactly the concrete stopped-recurrence kernel. -/
lemma mechanismKernel_pi_eq_stoppedRecurrenceKernel
    (ν : Arm → Measure ℝ) (hfinite : ∀ a, IsFiniteMeasure (ν a)) :
    Causalean.Mathlib.GraphMapProd.mechanismKernel
        (Measure.pi (fun a => @canonicalRecurrenceLawOf (ν a) (hfinite a)))
        stoppedFamilyMechanism =
      stoppedRecurrenceKernel ν hfinite := by
  let recurLaw : Arm → Measure RecurConfig := fun a =>
    @canonicalRecurrenceLawOf (ν a) (hfinite a)
  have hrecur : ∀ a, IsProbabilityMeasure (recurLaw a) := by
    intro a
    dsimp [recurLaw, canonicalRecurrenceLawOf]
    infer_instance
  letI : ∀ a, IsProbabilityMeasure (recurLaw a) := hrecur
  letI : IsProbabilityMeasure (Measure.pi recurLaw) := inferInstance
  ext e s hs
  rw [Causalean.Mathlib.GraphMapProd.mechanismKernel_apply
    (Measure.pi recurLaw) measurable_stoppedFamilyMechanism]
  rw [stoppedRecurrenceKernel_apply]
  have hmeasure :
      Measure.map (fun l => stoppedFamilyMechanism (e, l)) (Measure.pi recurLaw) =
        Measure.map (RecurConfig.stopAt e.2.1)
          (canonicalRecurrenceLawOf (ν e.1)) := by
    calc
      Measure.map (fun l => stoppedFamilyMechanism (e, l)) (Measure.pi recurLaw) =
          Measure.map (RecurConfig.stopAt e.2.1 ∘ Function.eval e.1)
            (Measure.pi recurLaw) := rfl
      _ = Measure.map (RecurConfig.stopAt e.2.1)
            (Measure.map (Function.eval e.1) (Measure.pi recurLaw)) :=
        (Measure.map_map
          (RecurConfig.measurable_stopAt.comp
            (measurable_const.prodMk measurable_id))
          (measurable_pi_apply e.1)).symm
      _ = Measure.map (RecurConfig.stopAt e.2.1) (recurLaw e.1) := by
        rw [Measure.pi_map_eval]
        simp only [measure_univ, Finset.prod_const_one, one_smul]
      _ = _ := rfl
  exact congrArg (fun μ : Measure RecurConfig => μ s) hmeasure

/-- Pushing independent assignment/death/censor blocks and a canonical
recurrence-family block through the observed graph gives exactly the
composition product of the exit law and stopped-recurrence kernel. -/
lemma rawExit_graph_eq_compProd
    (base : Measure (Arm × ((Arm → ℝ) × (Arm → ENNReal)))) [SFinite base]
    (ν : Arm → Measure ℝ) (hfinite : ∀ a, IsFiniteMeasure (ν a)) :
    Measure.map
        (fun q : (Arm × ((Arm → ℝ) × (Arm → ENNReal))) × (Arm → RecurConfig) =>
          (rawExitRecord q.1,
            stoppedFamilyMechanism (rawExitRecord q.1, q.2)))
        (base.prod (Measure.pi
          (fun a => @canonicalRecurrenceLawOf (ν a) (hfinite a)))) =
      (Measure.map rawExitRecord base).compProd
        (stoppedRecurrenceKernel ν hfinite) := by
  let recurLaw : Arm → Measure RecurConfig := fun a =>
    @canonicalRecurrenceLawOf (ν a) (hfinite a)
  have hrecur : ∀ a, IsProbabilityMeasure (recurLaw a) := by
    intro a
    dsimp [recurLaw, canonicalRecurrenceLawOf]
    infer_instance
  letI : ∀ a, IsProbabilityMeasure (recurLaw a) := hrecur
  letI : IsProbabilityMeasure (Measure.pi recurLaw) := inferInstance
  let graph : (ExitRecord × (Arm → RecurConfig)) → ExitRecord × RecurConfig :=
    fun q => (q.1, stoppedFamilyMechanism q)
  have hgraph : Measurable graph :=
    measurable_fst.prodMk measurable_stoppedFamilyMechanism
  calc
    _ = Measure.map graph
        (Measure.map (Prod.map rawExitRecord id)
          (base.prod (Measure.pi recurLaw))) := by
      rw [Measure.map_map hgraph
        (measurable_rawExitRecord.prodMap measurable_id)]
      rfl
    _ = Measure.map graph
        ((Measure.map rawExitRecord base).prod (Measure.pi recurLaw)) := by
      congr 1
      simpa only [Measure.map_id] using
        (Measure.map_prod_map base (Measure.pi recurLaw)
          measurable_rawExitRecord measurable_id).symm
    _ = (Measure.map rawExitRecord base).compProd
        (Causalean.Mathlib.GraphMapProd.mechanismKernel
          (Measure.pi recurLaw) stoppedFamilyMechanism) := by
      exact Causalean.Mathlib.GraphMapProd.map_graph_prod_eq_compProd
        (Measure.map rawExitRecord base) (Measure.pi recurLaw)
        measurable_stoppedFamilyMechanism
    _ = _ := by rw [mechanismKernel_pi_eq_stoppedRecurrenceKernel]

/-- The exact joint exit/stopped-recurrence law generated by the four-block
latent product constructor is the exit-law composition product with the
canonical stopped-recurrence kernel. -/
lemma latentProductLaw_exitStopped_eq_compProd
    (assignment : Measure Arm) [IsProbabilityMeasure assignment]
    (deathLaw : Measure (Arm → ℝ)) [IsProbabilityMeasure deathLaw]
    (censorLaw : Measure (Arm → ENNReal)) [IsProbabilityMeasure censorLaw]
    (ν : Arm → Measure ℝ) (hfinite : ∀ a, IsFiniteMeasure (ν a)) :
    Measure.map (fun z : LatentSubject =>
        (latentExitRecord z, latentStoppedRecur z))
        (latentProductLaw assignment
          (fun a => @canonicalRecurrenceLawOf (ν a) (hfinite a))
          deathLaw censorLaw) =
      (Measure.map rawExitRecord
        (assignment.prod (deathLaw.prod censorLaw))).compProd
          (stoppedRecurrenceKernel ν hfinite) := by
  let recurLaw : Arm → Measure RecurConfig := fun a =>
    @canonicalRecurrenceLawOf (ν a) (hfinite a)
  have hrecur : ∀ a, IsProbabilityMeasure (recurLaw a) := by
    intro a
    dsimp [recurLaw, canonicalRecurrenceLawOf]
    infer_instance
  letI : ∀ a, IsProbabilityMeasure (recurLaw a) := hrecur
  let recurFamilyLaw := Measure.pi recurLaw
  let dcLaw := deathLaw.prod censorLaw
  let base := assignment.prod dcLaw
  let perm : Arm × ((Arm → RecurConfig) × ((Arm → ℝ) × (Arm → ENNReal))) →
      (Arm × ((Arm → ℝ) × (Arm → ENNReal))) × (Arm → RecurConfig) :=
    fun q => ((q.1, q.2.2), q.2.1)
  have hperm : Measurable perm := by fun_prop
  have hreorder : Measure.map perm (assignment.prod (recurFamilyLaw.prod dcLaw)) =
      base.prod recurFamilyLaw := by
    calc
      _ = Measure.map MeasurableEquiv.prodAssoc.symm
          (Measure.map (Prod.map id Prod.swap)
            (assignment.prod (recurFamilyLaw.prod dcLaw))) := by
        rw [Measure.map_map]
        · rfl
        · fun_prop
        · fun_prop
      _ = Measure.map MeasurableEquiv.prodAssoc.symm
          (assignment.prod (dcLaw.prod recurFamilyLaw)) := by
        congr 1
        rw [← Measure.map_prod_map assignment (recurFamilyLaw.prod dcLaw)
          measurable_id measurable_swap]
        rw [Measure.map_id, Measure.prod_swap]
      _ = base.prod recurFamilyLaw := by
        have hassoc := Measure.prodAssoc_prod
          (μ := assignment) (ν := dcLaw) (τ := recurFamilyLaw)
        rw [← hassoc, Measure.map_map
          MeasurableEquiv.prodAssoc.symm.measurable
          MeasurableEquiv.prodAssoc.measurable]
        simp [base]
  unfold latentProductLaw
  rw [Measure.map_map
    (measurable_latentExitRecord.prodMk measurable_latentStoppedRecur)
    LatentSubject.measurable_ofBlocks]
  let out : (Arm × ((Arm → ℝ) × (Arm → ENNReal))) × (Arm → RecurConfig) →
      ExitRecord × RecurConfig := fun q =>
    (rawExitRecord q.1, stoppedFamilyMechanism (rawExitRecord q.1, q.2))
  have hout : Measurable out := by
    exact measurable_rawExitRecord.comp measurable_fst |>.prodMk
      (measurable_stoppedFamilyMechanism.comp
        ((measurable_rawExitRecord.comp measurable_fst).prodMk measurable_snd))
  calc
    _ = Measure.map out
        (Measure.map perm (assignment.prod (recurFamilyLaw.prod dcLaw))) := by
      rw [Measure.map_map hout hperm]
      rfl
    _ = Measure.map out (base.prod recurFamilyLaw) := by rw [hreorder]
    _ = _ := rawExit_graph_eq_compProd base ν hfinite

/-- The common exit-record law used by the explicit constant baseline. -/
noncomputable def SubjectLaw.baselineExitRecordLaw
    (reference : SubjectLaw) (d0 : ℝ) : Measure ExitRecord :=
  Measure.map rawExitRecord
    ((reference.latent.map LatentSubject.treatment).prod
      ((Measure.pi (fun _ : Arm => expMeasure d0)).prod
      (reference.latent.map LatentSubject.censor)))

/-- The explicit baseline exit-record carrier is a probability law. -/
lemma SubjectLaw.baselineExitRecordLaw_isProbability
    (reference : SubjectLaw) (d0 : ℝ) (hd0 : 0 < d0) :
    IsProbabilityMeasure (SubjectLaw.baselineExitRecordLaw reference d0) := by
  letI : IsProbabilityMeasure reference.latent := ⟨reference.prob⟩
  letI : ∀ _a : Arm, IsProbabilityMeasure (expMeasure d0) := fun _ =>
    isProbabilityMeasure_expMeasure hd0
  letI : IsProbabilityMeasure (reference.latent.map LatentSubject.treatment) :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_treatment.aemeasurable
  letI : IsProbabilityMeasure (reference.latent.map LatentSubject.censor) :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_censorFamily.aemeasurable
  letI : IsProbabilityMeasure (Measure.pi (fun _ : Arm => expMeasure d0)) :=
    inferInstance
  letI : IsProbabilityMeasure
      ((Measure.pi (fun _ : Arm => expMeasure d0)).prod
        (reference.latent.map LatentSubject.censor)) := inferInstance
  letI : IsProbabilityMeasure
      ((reference.latent.map LatentSubject.treatment).prod
        ((Measure.pi (fun _ : Arm => expMeasure d0)).prod
          (reference.latent.map LatentSubject.censor))) := inferInstance
  unfold SubjectLaw.baselineExitRecordLaw
  exact Measure.isProbabilityMeasure_map measurable_rawExitRecord.aemeasurable

/-- The explicit baseline's joint exit/stopped-recurrence law is exactly its
common exit law composed with the canonical stopped baseline kernel. -/
lemma SubjectLaw.baseline_exitStoppedLaw_eq_compProd
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0) :
    exitStoppedLaw (SubjectLaw.baseline reference lambda0 d0 hd0) =
      (SubjectLaw.baselineExitRecordLaw reference d0).compProd
        (stoppedRecurrenceKernel
          (fun _ : Arm => baselineRecurrenceIntensity lambda0)
          (fun _ => baselineRecurrenceIntensity_isFinite lambda0)) := by
  letI : IsProbabilityMeasure reference.latent := ⟨reference.prob⟩
  letI : ∀ _a : Arm, IsProbabilityMeasure (expMeasure d0) := fun _ =>
    isProbabilityMeasure_expMeasure hd0
  letI : IsProbabilityMeasure (reference.latent.map LatentSubject.treatment) :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_treatment.aemeasurable
  letI : IsProbabilityMeasure (reference.latent.map LatentSubject.censor) :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_censorFamily.aemeasurable
  letI : IsProbabilityMeasure (Measure.pi (fun _ : Arm => expMeasure d0)) :=
    inferInstance
  unfold exitStoppedLaw SubjectLaw.baseline SubjectLaw.baselineExitRecordLaw
  dsimp only
  exact latentProductLaw_exitStopped_eq_compProd
    (reference.latent.map LatentSubject.treatment)
    (Measure.pi (fun _ : Arm => expMeasure d0))
    (reference.latent.map LatentSubject.censor)
    (fun _ : Arm => baselineRecurrenceIntensity lambda0)
    (fun _ => baselineRecurrenceIntensity_isFinite lambda0)

/-- The named baseline exit law is exactly the exit-record marginal of the
explicit baseline constructor. -/
lemma SubjectLaw.baselineExitRecordLaw_eq_exitRecordLaw
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0) :
    SubjectLaw.baselineExitRecordLaw reference d0 =
      exitRecordLaw (SubjectLaw.baseline reference lambda0 d0 hd0) := by
  letI : IsProbabilityMeasure reference.latent := ⟨reference.prob⟩
  letI : IsProbabilityMeasure (reference.latent.map LatentSubject.treatment) :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_treatment.aemeasurable
  letI : ∀ _a : Arm, IsProbabilityMeasure (expMeasure d0) := fun _ =>
    isProbabilityMeasure_expMeasure hd0
  letI : IsProbabilityMeasure (Measure.pi (fun _ : Arm => expMeasure d0)) :=
    inferInstance
  letI : IsProbabilityMeasure (reference.latent.map LatentSubject.censor) :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_censorFamily.aemeasurable
  letI : IsProbabilityMeasure
      ((Measure.pi (fun _ : Arm => expMeasure d0)).prod
        (reference.latent.map LatentSubject.censor)) := inferInstance
  letI : IsProbabilityMeasure
      ((reference.latent.map LatentSubject.treatment).prod
        ((Measure.pi (fun _ : Arm => expMeasure d0)).prod
          (reference.latent.map LatentSubject.censor))) := inferInstance
  letI : IsProbabilityMeasure (SubjectLaw.baselineExitRecordLaw reference d0) := by
    unfold SubjectLaw.baselineExitRecordLaw
    exact Measure.isProbabilityMeasure_map measurable_rawExitRecord.aemeasurable
  letI : IsMarkovKernel
      (stoppedRecurrenceKernel
        (fun _ : Arm => baselineRecurrenceIntensity lambda0)
        (fun _ => baselineRecurrenceIntensity_isFinite lambda0)) :=
    stoppedRecurrenceKernel_isMarkov _ _
  rw [exitRecordLaw_eq_fst_exitStoppedLaw,
    SubjectLaw.baseline_exitStoppedLaw_eq_compProd,
    Measure.fst_compProd]

/-- The baseline's joint death-family marginal is the iid exponential product
used in its constructor. -/
lemma SubjectLaw.baseline_map_deathFamily
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0) :
    (SubjectLaw.baseline reference lambda0 d0 hd0).latent.map
      LatentSubject.death = Measure.pi (fun _ : Arm => expMeasure d0) := by
  letI : IsProbabilityMeasure reference.latent := ⟨reference.prob⟩
  let assignment := reference.latent.map LatentSubject.treatment
  let censorLaw := reference.latent.map LatentSubject.censor
  let recurLaw : Arm → Measure RecurConfig := fun _ =>
    @canonicalRecurrenceLawOf (baselineRecurrenceIntensity lambda0)
      (baselineRecurrenceIntensity_isFinite lambda0)
  let deathLaw : Measure (Arm → ℝ) := Measure.pi (fun _ => expMeasure d0)
  letI : IsProbabilityMeasure assignment :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_treatment.aemeasurable
  letI : IsProbabilityMeasure censorLaw :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_censorFamily.aemeasurable
  have hrecur : ∀ a, IsProbabilityMeasure (recurLaw a) := fun _ => by
    dsimp [recurLaw, canonicalRecurrenceLawOf]
    infer_instance
  letI : ∀ _a : Arm, IsProbabilityMeasure (expMeasure d0) := fun _ =>
    isProbabilityMeasure_expMeasure hd0
  letI : IsProbabilityMeasure deathLaw := by
    dsimp [deathLaw]
    infer_instance
  change (latentProductLaw assignment recurLaw deathLaw censorLaw).map
    LatentSubject.death = deathLaw
  exact latentProductLaw_map_death assignment recurLaw deathLaw censorLaw hrecur

/-- A treatment recurrence perturbation has the exact composition-product
representation over the base law's preserved assignment/death/censor blocks. -/
lemma SubjectLaw.perturbTreatment_exitStoppedLaw_eq_compProd
    (base : SubjectLaw) (lam1 : ℝ → ℝ)
    (hfinite : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity base lam1 a)) :
    exitStoppedLaw (SubjectLaw.perturbTreatment base lam1 hfinite) =
      (Measure.map rawExitRecord
        ((base.latent.map LatentSubject.treatment).prod
          ((base.latent.map LatentSubject.death).prod
            (base.latent.map LatentSubject.censor)))).compProd
        (stoppedRecurrenceKernel
          (fun a => treatmentPerturbIntensity base lam1 a) hfinite) := by
  letI : IsProbabilityMeasure base.latent := ⟨base.prob⟩
  letI : IsProbabilityMeasure (base.latent.map LatentSubject.treatment) :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_treatment.aemeasurable
  letI : IsProbabilityMeasure (base.latent.map LatentSubject.death) :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_deathFamily.aemeasurable
  letI : IsProbabilityMeasure (base.latent.map LatentSubject.censor) :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_censorFamily.aemeasurable
  unfold exitStoppedLaw SubjectLaw.perturbTreatment
  dsimp only
  exact latentProductLaw_exitStopped_eq_compProd
    (base.latent.map LatentSubject.treatment)
    (base.latent.map LatentSubject.death)
    (base.latent.map LatentSubject.censor)
    (fun a => treatmentPerturbIntensity base lam1 a) hfinite

/-- A perturbation of the explicit baseline uses exactly the same exit-record
base measure as that baseline. -/
lemma SubjectLaw.baselinePerturb_exitStoppedLaw_eq_compProd
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0)
    (lam1 : ℝ → ℝ)
    (hfinite : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity
        (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 a)) :
    exitStoppedLaw (SubjectLaw.perturbTreatment
      (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 hfinite) =
      (SubjectLaw.baselineExitRecordLaw reference d0).compProd
        (stoppedRecurrenceKernel
          (fun a => treatmentPerturbIntensity
            (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 a)
          hfinite) := by
  rw [SubjectLaw.perturbTreatment_exitStoppedLaw_eq_compProd]
  congr 2
  have hpres := SubjectLaw.baseline_preserves_marginals
    reference lambda0 d0 hd0
  rw [hpres.1, SubjectLaw.baseline_map_deathFamily, hpres.2]

/-- The explicit baseline observed law is the observed-history assembly of
the common exit law and its canonical stopped recurrence kernel. -/
lemma SubjectLaw.baseline_observedLaw_eq_compProd
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0) :
    observedLaw (SubjectLaw.baseline reference lambda0 d0 hd0) =
      ((SubjectLaw.baselineExitRecordLaw reference d0).compProd
        (stoppedRecurrenceKernel
          (fun _ : Arm => baselineRecurrenceIntensity lambda0)
          (fun _ => baselineRecurrenceIntensity_isFinite lambda0))).map
            ObsHistory.ofExitRecur := by
  rw [observedLaw_eq_map_exitStoppedLaw,
    SubjectLaw.baseline_exitStoppedLaw_eq_compProd]

/-- A treatment perturbation of the explicit baseline has the same observed
exit base and differs only through its canonical stopped recurrence kernel. -/
lemma SubjectLaw.baselinePerturb_observedLaw_eq_compProd
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0)
    (lam1 : ℝ → ℝ)
    (hfinite : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity
        (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 a)) :
    observedLaw (SubjectLaw.perturbTreatment
      (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 hfinite) =
      ((SubjectLaw.baselineExitRecordLaw reference d0).compProd
        (stoppedRecurrenceKernel
          (fun a => treatmentPerturbIntensity
            (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 a)
          hfinite)).map ObsHistory.ofExitRecur := by
  rw [observedLaw_eq_map_exitStoppedLaw,
    SubjectLaw.baselinePerturb_exitStoppedLaw_eq_compProd]

/-- Structural common-exit chain rule for the explicit baseline treatment
perturbation.  Keeping this constructor reduction separate prevents the
analytic fixed-exit proof from repeatedly unfolding the latent product law. -/
lemma SubjectLaw.baselinePerturb_observedKL_eq_fixedExitIntegral
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0)
    (lam1 : ℝ → ℝ)
    (hfinite : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity
        (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 a))
    (hac : ∀ᵐ e ∂SubjectLaw.baselineExitRecordLaw reference d0,
      stoppedRecurrenceKernel
          (fun a => treatmentPerturbIntensity
            (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 a)
          hfinite e ≪
        stoppedRecurrenceKernel
          (fun _ : Arm => baselineRecurrenceIntensity lambda0)
          (fun _ => baselineRecurrenceIntensity_isFinite lambda0) e) :
    InformationTheory.klDiv
        (observedLaw (SubjectLaw.perturbTreatment
          (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 hfinite))
        (observedLaw (SubjectLaw.baseline reference lambda0 d0 hd0)) =
      ∫⁻ e, InformationTheory.klDiv
        (stoppedRecurrenceKernel
          (fun a => treatmentPerturbIntensity
            (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 a)
          hfinite e)
        (stoppedRecurrenceKernel
          (fun _ : Arm => baselineRecurrenceIntensity lambda0)
          (fun _ => baselineRecurrenceIntensity_isFinite lambda0) e)
        ∂SubjectLaw.baselineExitRecordLaw reference d0 := by
  letI : IsProbabilityMeasure
      (SubjectLaw.baselineExitRecordLaw reference d0) :=
    SubjectLaw.baselineExitRecordLaw_isProbability reference d0 hd0
  letI : IsMarkovKernel
      (stoppedRecurrenceKernel
        (fun a => treatmentPerturbIntensity
          (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 a)
        hfinite) := stoppedRecurrenceKernel_isMarkov _ _
  letI : IsMarkovKernel
      (stoppedRecurrenceKernel
        (fun _ : Arm => baselineRecurrenceIntensity lambda0)
        (fun _ => baselineRecurrenceIntensity_isFinite lambda0)) :=
    stoppedRecurrenceKernel_isMarkov _ _
  rw [SubjectLaw.baselinePerturb_observedLaw_eq_compProd,
    SubjectLaw.baseline_observedLaw_eq_compProd]
  exact klDiv_common_exit_recurrence_chainRule
    (SubjectLaw.baselineExitRecordLaw reference d0)
    (stoppedRecurrenceKernel
      (fun a => treatmentPerturbIntensity
        (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 a)
      hfinite)
    (stoppedRecurrenceKernel
      (fun _ : Arm => baselineRecurrenceIntensity lambda0)
      (fun _ => baselineRecurrenceIntensity_isFinite lambda0)) hac

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

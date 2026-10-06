module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.CorrectionMoments

/-! Joint outcome-vector law obtained by splitting one full observed Poisson sample. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

variable {S : Type*} [MeasurableSpace S]

/-- Regrouping a product indexed by cell and Boolean arm gives the product,
over cells, of the two arm-coordinate product laws. -/
lemma map_groupBool_pi {n : ℕ} (nu : Fin n × Bool → Measure S)
    [∀ j, IsProbabilityMeasure (nu j)] :
    Measure.map (fun z : (Fin n × Bool) → S => fun k =>
        (z (k, false), z (k, true))) (Measure.pi nu) =
      Measure.pi (fun k : Fin n => (nu (k, false)).prod (nu (k, true))) := by
  let pred : Fin n × Bool → Prop := fun j => j.2 = false
  let ef : Fin n ≃ Subtype pred := {
    toFun k := ⟨(k, false), rfl⟩
    invFun j := j.1.1
    left_inv k := rfl
    right_inv j := by
      apply Subtype.ext
      rcases j with ⟨⟨k, a⟩, ha⟩
      simp only [pred] at ha
      subst a
      rfl }
  let et : Fin n ≃ Subtype (fun j => ¬ pred j) := {
    toFun k := ⟨(k, true), by simp [pred]⟩
    invFun j := j.1.1
    left_inv k := rfl
    right_inv j := by
      apply Subtype.ext
      rcases j with ⟨⟨k, a⟩, ha⟩
      cases a <;> simp [pred] at ha ⊢ }
  let hs := measurePreserving_piEquivPiSubtypeProd nu pred
  let hf := (measurePreserving_piCongrLeft
    (fun j : Subtype pred => nu j.1) ef).symm
  let ht := (measurePreserving_piCongrLeft
    (fun j : Subtype (fun j => ¬ pred j) => nu j.1) et).symm
  let hp := MeasurePreserving.prod hf ht
  let hg := (measurePreserving_arrowProdEquivProdArrow S S (Fin n)
    (fun k => nu (k, false)) (fun k => nu (k, true))).symm
  have hcomp := hg.comp (hp.comp hs)
  rw [← hcomp.map_eq]
  congr 1

private lemma poissonMeasure_zero_local : poissonMeasure 0 = Measure.dirac 0 := by
  ext s hs
  rw [poissonMeasure, Measure.sum_apply _ hs]
  refine (tsum_eq_single 0 ?_).trans ?_
  · intro m hm
    rw [Measure.smul_apply, smul_eq_mul]
    simp [zero_pow hm]
  · simp

/-- At intensity zero, a finite Poisson sample does not depend on its base
probability law. -/
lemma finitePoissonSampleLaw_zero_base_eq
    {X : Type*} [MeasurableSpace X]
    (Q R : Measure X) [IsProbabilityMeasure Q] [IsProbabilityMeasure R] :
    finitePoissonSampleLaw Q 0 = finitePoissonSampleLaw R 0 := by
  unfold finitePoissonSampleLaw poissonIIDStreamLaw
  rw [poissonMeasure_zero_local]
  have hconst : (streamToFiniteSample ∘ fun y : ℕ → X => (0, y)) =
      fun _ => fixedSizeEmbed 0 (fun i => Fin.elim0 i) := by
    funext y
    have hf : (fun i : Fin 0 => y i) = (fun i => Fin.elim0 i) :=
      Subsingleton.elim _ _
    exact congrArg (Sigma.mk 0) hf
  calc
    Measure.map streamToFiniteSample
        ((Measure.dirac 0).prod (iidStreamLaw Q)) =
        Measure.map (streamToFiniteSample ∘ Prod.mk 0) (iidStreamLaw Q) := by
      rw [Measure.dirac_prod]
      exact Measure.map_map measurable_streamToFiniteSample
        (measurable_const.prodMk measurable_id)
    _ = Measure.dirac (fixedSizeEmbed 0 (fun i => Fin.elim0 i)) := by
      rw [hconst, Measure.map_const, measure_univ, one_smul]
    _ = Measure.map (streamToFiniteSample ∘ Prod.mk 0) (iidStreamLaw R) := by
      rw [hconst, Measure.map_const, measure_univ, one_smul]
    _ = Measure.map streamToFiniteSample
        ((Measure.dirac 0).prod (iidStreamLaw R)) := by
      rw [Measure.dirac_prod]
      exact (Measure.map_map measurable_streamToFiniteSample
        (measurable_const.prodMk measurable_id)).symm

noncomputable def fullMarkOutcomeVector {n : ℕ}
    (s : FiniteSample (FullObservedMark n × ℝ)) :
    Fin n → (FiniteSample ℝ × FiniteSample ℝ) := fun k =>
  (finiteSampleMap (fun z : FullObservedMark n × ℝ => z.1.2.2)
      ((fullMarkArmCellPartition n).restrictCell (k, false) s),
   finiteSampleMap (fun z : FullObservedMark n × ℝ => z.1.2.2)
      ((fullMarkArmCellPartition n).restrictCell (k, true) s))

lemma measurable_fullMarkOutcomeVector (n : ℕ) :
    Measurable (fullMarkOutcomeVector (n := n)) := by
  apply measurable_pi_lambda
  intro k
  exact (measurable_finiteSampleMap _ (by fun_prop) |>.comp
    ((fullMarkArmCellPartition n).measurable_restrictCell (k, false))).prodMk
    (measurable_finiteSampleMap _ (by fun_prop) |>.comp
      ((fullMarkArmCellPartition n).measurable_restrictCell (k, true)))

/-- The complete vector of arm/cell outcome samples has the independent
per-cell two-arm Poisson law, including cells of zero mass. -/
lemma map_fullMarkOutcomeVector {n : ℕ} (P : Law n) (lam : ℝ≥0)
    (hoverlap : FixedOverlap P) :
    Measure.map fullMarkOutcomeVector
        (finiteMarkedPoissonSampleLaw (fullObservedMarkLaw P)
          (Measure.dirac 0) lam) =
      Measure.pi (fun k : Fin n =>
        (@finitePoissonSampleLaw ℝ _ (P.outcomeLaw false k)
          (P.outcome_isProbability false k)
          (lam * Real.toNNReal (armMass P false k))).prod
        (@finitePoissonSampleLaw ℝ _ (P.outcomeLaw true k)
          (P.outcome_isProbability true k)
          (lam * Real.toNNReal (armMass P true k)))) := by
  let p := fullMarkArmCellPartition n
  let mu := finiteMarkedPoissonSampleLaw (fullObservedMarkLaw P)
    (Measure.dirac 0) lam
  let nu : Fin n × Bool → Measure (FiniteSample (FullObservedMark n × ℝ)) :=
    fun j => finiteMarkedPoissonSampleLaw
      (p.cellObservationLaw (fullObservedMarkLaw P) j) (Measure.dirac 0)
      (lam * p.cellMass (fullObservedMarkLaw P) j)
  let F := finiteSampleMap (fun z : FullObservedMark n × ℝ => z.1.2.2)
  have hF : Measurable F := measurable_finiteSampleMap _ (by fun_prop)
  have hsplit : Measure.map p.restrictPartition mu = Measure.pi nu :=
    map_restrictPartition_fullMarkPoisson P lam
  have hgroup : Measure.map (fun z : (Fin n × Bool) →
      FiniteSample (FullObservedMark n × ℝ) => fun k =>
        (z (k, false), z (k, true))) (Measure.pi nu) =
      Measure.pi (fun k : Fin n => (nu (k, false)).prod (nu (k, true))) :=
    map_groupBool_pi nu
  have hcoord (k : Fin n) (a : Bool) : Measure.map F (nu (k, a)) =
      @finitePoissonSampleLaw ℝ _ (P.outcomeLaw a k)
        (P.outcome_isProbability a k)
        (lam * Real.toNNReal (armMass P a k)) := by
    by_cases hp : 0 < P.cellMass k
    · have hov := hoverlap k hp
      have ha : 0 < armMass P a k := by
        unfold armMass
        cases a <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · apply mul_pos hp
          nlinarith [hov.2]
        · apply mul_pos hp
          nlinarith [hov.1]
      have hmass : (fullMarkArmCellPartition n).cellMass
          (fullObservedMarkLaw P) (k, a) =
          Real.toNNReal (armMass P a k) := by
        apply NNReal.eq
        simpa only [Real.coe_toNNReal _ ha.le] using
          fullMarkArmCellPartition_cellMass P k a
      unfold F
      simpa only [nu, p, hmass] using
        map_cellFinitePoisson_outcomes P a k ha
          (lam * (fullMarkArmCellPartition n).cellMass
            (fullObservedMarkLaw P) (k, a))
    · have hp0 : P.cellMass k = 0 := le_antisymm (le_of_not_gt hp)
        (P.cellMass_range k).1
      have ha0 : armMass P a k = 0 := by
        unfold armMass
        rw [hp0]
        simp
      have hrate : lam * p.cellMass (fullObservedMarkLaw P) (k, a) = 0 := by
        apply fullMarkArmCellPartition_scaledIntensity_eq_zero
        exact ha0
      have htarget : lam * Real.toNNReal (armMass P a k) = 0 := by rw [ha0]; simp
      rw [show nu (k, a) = finitePoissonSampleLaw
          ((p.cellObservationLaw (fullObservedMarkLaw P) (k, a)).prod
            (Measure.dirac 0)) 0 by
        unfold nu finiteMarkedPoissonSampleLaw
        rw [hrate]]
      let g : FullObservedMark n × ℝ → ℝ := fun z => z.1.2.2
      have hg : Measurable g := by fun_prop
      letI : IsProbabilityMeasure (Measure.map g
          ((p.cellObservationLaw (fullObservedMarkLaw P) (k, a)).prod
            (Measure.dirac 0))) :=
        Measure.isProbabilityMeasure_map hg.aemeasurable
      unfold F
      rw [show (fun z : FullObservedMark n × ℝ => z.1.2.2) = g by rfl,
        map_finitePoissonSampleLaw_finiteSampleMap_local _ g hg 0,
        htarget]
      letI : IsProbabilityMeasure (P.outcomeLaw a k) :=
        P.outcome_isProbability a k
      apply finitePoissonSampleLaw_zero_base_eq
  rw [show Measure.map fullMarkOutcomeVector mu =
      Measure.map (fun z : (Fin n × Bool) →
        FiniteSample (FullObservedMark n × ℝ) => fun k =>
          (F (z (k, false)), F (z (k, true))))
        (Measure.map p.restrictPartition mu) by
    rw [Measure.map_map (by fun_prop) p.measurable_restrictPartition]
    rfl, hsplit]
  rw [show (fun z : (Fin n × Bool) → FiniteSample (FullObservedMark n × ℝ) =>
      fun k => (F (z (k, false)), F (z (k, true)))) =
      (fun q : Fin n → (FiniteSample (FullObservedMark n × ℝ) ×
        FiniteSample (FullObservedMark n × ℝ)) => fun k =>
          (F (q k).1, F (q k).2)) ∘
        (fun z => fun k => (z (k, false), z (k, true))) by rfl]
  rw [← Measure.map_map (by fun_prop) (by fun_prop), hgroup]
  change Measure.map (fun q k => Prod.map F F (q k))
      (Measure.pi fun k : Fin n => (nu (k, false)).prod (nu (k, true))) = _
  rw [Measure.pi_map_pi (fun _ => (hF.prodMap hF).aemeasurable)]
  congr 1
  funext k
  rw [← Measure.map_prod_map _ _ hF hF, hcoord k false, hcoord k true]

noncomputable def observedOutcomeVector {n : ℕ}
    (s : FiniteSample (SampleObs n)) :
    Fin n → (FiniteSample ℝ × FiniteSample ℝ) :=
  fullMarkOutcomeVector
    (finiteSampleMap (fun o => (toFullObservedMark o, 0)) s)

lemma measurable_observedOutcomeVector (n : ℕ) :
    Measurable (observedOutcomeVector (n := n)) := by
  exact (measurable_fullMarkOutcomeVector n).comp
    (measurable_finiteSampleMap _
      (measurable_toFullObservedMark.prodMk measurable_const))

/-- Direct form used by the finite-prefix transport: partitioning a raw
observed Poisson sample yields the independent vector of arm/cell outcomes. -/
lemma map_observedOutcomeVector {n : ℕ} (P : Law n) (lam : ℝ≥0)
    (hoverlap : FixedOverlap P) :
    Measure.map observedOutcomeVector (finitePoissonSampleLaw P.observedLaw lam) =
      Measure.pi (fun k : Fin n =>
        (@finitePoissonSampleLaw ℝ _ (P.outcomeLaw false k)
          (P.outcome_isProbability false k)
          (lam * Real.toNNReal (armMass P false k))).prod
        (@finitePoissonSampleLaw ℝ _ (P.outcomeLaw true k)
          (P.outcome_isProbability true k)
          (lam * Real.toNNReal (armMass P true k)))) := by
  let g : SampleObs n → FullObservedMark n × ℝ :=
    fun o => (toFullObservedMark o, 0)
  have hg : Measurable g := measurable_toFullObservedMark.prodMk measurable_const
  have hbase : Measure.map g P.observedLaw =
      (fullObservedMarkLaw P).prod (Measure.dirac 0) := by
    rw [Measure.prod_dirac]
    unfold fullObservedMarkLaw
    rw [Measure.map_map (by fun_prop) measurable_toFullObservedMark]
    rfl
  have hsample : Measure.map (finiteSampleMap g)
      (finitePoissonSampleLaw P.observedLaw lam) =
      finiteMarkedPoissonSampleLaw (fullObservedMarkLaw P)
        (Measure.dirac 0) lam := by
    unfold finiteMarkedPoissonSampleLaw
    rw [map_finitePoissonSampleLaw_finiteSampleMap_local P.observedLaw g hg lam]
    congr 1
  unfold observedOutcomeVector
  change Measure.map (fullMarkOutcomeVector ∘ finiteSampleMap g)
      (finitePoissonSampleLaw P.observedLaw lam) = _
  rw [← Measure.map_map (measurable_fullMarkOutcomeVector n)
    (measurable_finiteSampleMap g hg), hsample]
  exact map_fullMarkOutcomeVector P lam hoverlap

/-- Specialization at the estimator block intensity, in the existing
`cellOutcomePoissonLaw` notation. -/
lemma map_observedOutcomeVector_blockMean {n : ℕ} (P : Law n)
    (hoverlap : FixedOverlap P) :
    Measure.map observedOutcomeVector
        (finitePoissonSampleLaw P.observedLaw
          (Real.toNNReal (blockMean n))) =
      Measure.pi (fun k : Fin n => cellOutcomePoissonLaw P k) := by
  have hm : 0 ≤ blockMean n := by unfold blockMean; positivity
  simpa only [cellOutcomePoissonLaw, Real.toNNReal_mul hm] using
    map_observedOutcomeVector P (Real.toNNReal (blockMean n)) hoverlap

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

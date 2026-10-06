module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.Representation
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.Audit
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Partition.Splitting
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Partition.CellLaws

/-! Arm-cell Poisson splitting while retaining the outcome coordinate. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

abbrev FullObservedMark (n : ℕ) := Fin n × Bool × ℝ

def toFullObservedMark {n : ℕ} (o : SampleObs n) : FullObservedMark n :=
  (o.x, o.a, o.y)

lemma measurable_toFullObservedMark {n : ℕ} :
    Measurable (toFullObservedMark : SampleObs n → FullObservedMark n) := by
  rw [measurable_iff_comap_le]
  rfl

noncomputable def fullObservedMarkLaw (P : Law n) : Measure (FullObservedMark n) :=
  Measure.map toFullObservedMark P.observedLaw

noncomputable instance fullObservedMarkLaw_isProbabilityMeasure (P : Law n) :
    IsProbabilityMeasure (fullObservedMarkLaw P) :=
  Measure.isProbabilityMeasure_map measurable_toFullObservedMark.aemeasurable

def fullMarkArmCellPartition (n : ℕ) :
    FiniteMeasurablePartition (FullObservedMark n) (Fin n × Bool) where
  cell := fun z => (z.1, z.2.1)
  measurable_cell := measurable_fst.prodMk measurable_snd.fst

lemma fullMarkArmCellPartition_cellSet (n : ℕ) (k : Fin n) (a : Bool) :
    (fullMarkArmCellPartition n).cellSet (k, a) =
      {z : FullObservedMark n | z.1 = k ∧ z.2.1 = a} := by
  ext z
  simp [FiniteMeasurablePartition.cellSet, fullMarkArmCellPartition]

/-- The partition cell mass is the audit arm mass. -/
lemma fullMarkArmCellPartition_cellMass (P : Law n) (k : Fin n) (a : Bool) :
    ((fullMarkArmCellPartition n).cellMass (fullObservedMarkLaw P) (k, a) : ℝ) =
      armMass P a k := by
  have hfactor := P.arm_outcome_factorization a k Set.univ MeasurableSet.univ
  letI : IsProbabilityMeasure (P.outcomeLaw a k) := P.outcome_isProbability a k
  have hout : DiscreteAteHeterogeneityFrontier.realMass
      (P.outcomeLaw a k) Set.univ = 1 := by
    simp [DiscreteAteHeterogeneityFrontier.realMass]
  rw [hout, mul_one] at hfactor
  unfold FiniteMeasurablePartition.cellMass
  rw [← ENNReal.coe_toReal,
    ENNReal.coe_toNNReal (measure_ne_top (fullObservedMarkLaw P) _)]
  rw [fullMarkArmCellPartition_cellSet]
  unfold fullObservedMarkLaw
  rw [Measure.map_apply measurable_toFullObservedMark
    (by
      have hs := (fullMarkArmCellPartition n).measurableSet_cellSet (k, a)
      rwa [fullMarkArmCellPartition_cellSet] at hs)]
  change (P.observedLaw {o : SampleObs n | o.x = k ∧ o.a = a}).toReal = _
  rw [show {o : SampleObs n | o.x = k ∧ o.a = a} =
      {o : SampleObs n | o.x = k ∧ o.a = a ∧ o.y ∈ Set.univ} by ext o; simp]
  simpa [armMass, DiscreteAteHeterogeneityFrontier.realMass] using hfactor.symm

/-- Exact independent arm-cell splitting for the full `(x,a,y)` observation
marks.  A dummy real mark is appended only to reuse the generic theorem. -/
lemma map_restrictPartition_fullMarkPoisson (P : Law n) (lam : ℝ≥0) :
    Measure.map (fullMarkArmCellPartition n).restrictPartition
        (finiteMarkedPoissonSampleLaw (fullObservedMarkLaw P) (Measure.dirac 0) lam) =
      Measure.pi (fun j : Fin n × Bool =>
        finiteMarkedPoissonSampleLaw
          ((fullMarkArmCellPartition n).cellObservationLaw (fullObservedMarkLaw P) j)
          (Measure.dirac 0)
          (lam * (fullMarkArmCellPartition n).cellMass (fullObservedMarkLaw P) j)) := by
  exact FiniteMeasurablePartition.map_restrictPartition_finiteMarkedPoissonSampleLaw
    (fullMarkArmCellPartition n) (fullObservedMarkLaw P) (Measure.dirac 0) lam

/-- On every positive arm-cell, the retained outcome coordinate has exactly
the model's stipulated conditional outcome law. -/
lemma map_outcome_cellObservationLaw (P : Law n) (k : Fin n) (a : Bool)
    (harm : 0 < armMass P a k) :
    Measure.map (fun z : FullObservedMark n => z.2.2)
        ((fullMarkArmCellPartition n).cellObservationLaw
          (fullObservedMarkLaw P) (k, a)) =
      P.outcomeLaw a k := by
  letI : IsProbabilityMeasure (P.outcomeLaw a k) := P.outcome_isProbability a k
  let p := fullMarkArmCellPartition n
  let Q := fullObservedMarkLaw P
  let A := p.cellSet (k, a)
  have hQtop (s : Set (FullObservedMark n)) : Q s ≠ ⊤ := measure_ne_top Q s
  have hAreal : (Q A).toReal = armMass P a k := by
    rw [← fullMarkArmCellPartition_cellMass P k a]
    unfold FiniteMeasurablePartition.cellMass
    rw [← ENNReal.coe_toReal, ENNReal.coe_toNNReal (hQtop A)]
  have hA : Q A ≠ 0 := by
    intro hzero
    rw [hzero] at hAreal
    simp only [ENNReal.toReal_zero] at hAreal
    linarith
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply measurable_snd.snd hs]
  unfold FiniteMeasurablePartition.cellObservationLaw
  rw [dif_neg hA, Measure.smul_apply,
    Measure.restrict_apply (hs.preimage measurable_snd.snd)]
  have hfactor := P.arm_outcome_factorization a k s hs
  have hnum : (Q ((fun z : FullObservedMark n => z.2.2) ⁻¹' s ∩ A)).toReal =
      armMass P a k * (P.outcomeLaw a k s).toReal := by
    unfold Q fullObservedMarkLaw
    rw [Measure.map_apply measurable_toFullObservedMark
      ((hs.preimage measurable_snd.snd).inter
        (p.measurableSet_cellSet (k, a)))]
    rw [show toFullObservedMark ⁻¹'
          ((fun z : FullObservedMark n => z.2.2) ⁻¹' s ∩ A) =
        {o : SampleObs n | o.x = k ∧ o.a = a ∧ o.y ∈ s} by
      ext o
      simp only [mem_inter_iff, mem_preimage, mem_setOf_eq,
        toFullObservedMark, A, p, fullMarkArmCellPartition_cellSet]
      aesop]
    simpa [armMass, DiscreteAteHeterogeneityFrontier.realMass] using hfactor.symm
  have hreal : ((Q A)⁻¹ * Q
      ((fun z : FullObservedMark n => z.2.2) ⁻¹' s ∩ A)).toReal =
      (P.outcomeLaw a k s).toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, hAreal, hnum]
    field_simp
  rcases (ENNReal.toReal_eq_toReal_iff _ _).mp hreal with heq | hbad | hbad
  · exact heq
  · exact False.elim ((measure_ne_top (P.outcomeLaw a k) s) hbad.2)
  · exact False.elim
      ((ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hA)
        (hQtop ((fun z : FullObservedMark n => z.2.2) ⁻¹' s ∩ A))) hbad.1)

/-- A zero audit arm mass gives zero partition intensity, so the arbitrary
zero-cell fallback in `cellObservationLaw` is never sampled. -/
lemma fullMarkArmCellPartition_cellMass_eq_zero (P : Law n) (k : Fin n) (a : Bool)
    (harm : armMass P a k = 0) :
    (fullMarkArmCellPartition n).cellMass (fullObservedMarkLaw P) (k, a) = 0 := by
  apply NNReal.eq
  change (((fullMarkArmCellPartition n).cellMass
    (fullObservedMarkLaw P) (k, a) : ℝ)) = 0
  rw [fullMarkArmCellPartition_cellMass, harm]

lemma fullMarkArmCellPartition_scaledIntensity_eq_zero (P : Law n)
    (lam : ℝ≥0) (k : Fin n) (a : Bool) (harm : armMass P a k = 0) :
    lam * (fullMarkArmCellPartition n).cellMass
      (fullObservedMarkLaw P) (k, a) = 0 := by
  rw [fullMarkArmCellPartition_cellMass_eq_zero P k a harm, mul_zero]

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

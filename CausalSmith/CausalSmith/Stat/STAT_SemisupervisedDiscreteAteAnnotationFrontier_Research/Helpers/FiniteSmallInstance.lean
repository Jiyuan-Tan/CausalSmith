module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.Estimator
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.CommonMarginalPrior
public import Causalean.Stat.Minimax.TotalVariation
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! The explicit two-cell diagnostic calculation. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory
open scoped BigOperators ENNReal

-- @node: smallNullAtomMass
/-- The null diagnostic law is uniform on `(X,A)` and has outcome zero.  [the stated conditions](hyp:z) [the stated conclusion](goal). -/
noncomputable def smallNullAtomMass (z : Obs 2) : ENNReal :=
  if z.2.2 then 0 else 1 / 4

-- @node: smallAlternativeAtomMass
/-- The alternative diagnostic law changes only the treated outcome in cell zero.  [the stated conditions](hyp:z) [the stated conclusion](goal). -/
noncomputable def smallAlternativeAtomMass (z : Obs 2) : ENNReal :=
  if z.2.2 = (z.2.1 && decide (z.1 = 0)) then 1 / 4 else 0

-- @node: smallNullLaw
/-- The explicit null law in the two-cell diagnostic.  [the stated conclusion](goal). -/
noncomputable def smallNullLaw : DiscreteLaw 2 :=
  ⟨PMF.ofFintype smallNullAtomMass (by
    norm_num [smallNullAtomMass, Fintype.sum_prod_type]
    rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
    norm_num [ENNReal.toReal_add, ENNReal.toReal_inv])⟩

-- @node: smallAlternativeLaw
/-- The explicit alternative law in the two-cell diagnostic.  [the stated conclusion](goal). -/
noncomputable def smallAlternativeLaw : DiscreteLaw 2 :=
  ⟨PMF.ofFintype smallAlternativeAtomMass (by
    norm_num [smallAlternativeAtomMass, Fintype.sum_prod_type]
    rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
    norm_num [ENNReal.toReal_add, ENNReal.toReal_inv])⟩

/-- The displayed `n=m=1` mixed indicator statistic.  [the stated conditions](hyp:z) [the stated conclusion](goal). -/
def smallMixedStatistic (z : Sample 1 1 2) : Real :=
  2 * (if z.1 0 = (0, true, true) then 1 else 0) *
    ((if z.2 0 = (0, false) then 1 else 0) +
      (if z.2 0 = (0, true) then 1 else 0))

/-- The prescribed laws and identities comprising the finite diagnostic calculation. -/
structure FiniteCalculationWitness where
  Pi0Small : Measure (DiscreteLaw 2)
  Pi1Small : Measure (DiscreteLaw 2)
  law0 : DiscreteLaw 2
  law1 : DiscreteLaw 2
  prior0_dirac : Pi0Small = Measure.dirac law0
  prior1_dirac : Pi1Small = Measure.dirac law1
  class0 : ModelClass 2 (1 / 4) law0
  class1 : ModelClass 2 (1 / 4) law1
  cellMass0 : ∀ x, cellMass law0 x = 1 / 2
  cellMass1 : ∀ x, cellMass law1 x = 1 / 2
  propensity0 : ∀ x, propensity law0 x = 1 / 2
  propensity1 : ∀ x, propensity law1 x = 1 / 2
  controlMean0 : ∀ x, outcomeMean law0 false x = 0
  controlMean1 : ∀ x, outcomeMean law1 false x = 0
  treatedMean0 : ∀ x, outcomeMean law0 true x = 0
  treatedMean1_first : outcomeMean law1 true 0 = 1
  treatedMean1_second : outcomeMean law1 true 1 = 0
  uniformAux0 : ∀ z, auxTableOf law0 z = 1 / 4
  uniformAux1 : ∀ z, auxTableOf law1 z = 1 / 4
  uniformAux : auxTableOf law0 = auxTableOf law1
  target0 : ateFunctional law0 = 0
  target1 : ateFunctional law1 = 1 / 2
  expectationIdentity :
    ∫ z, smallMixedStatistic z ∂annotationLaw law1 1 1 =
      2 * markedMass law1 0 true * cellMass law1 0
  expectationValue :
    2 * markedMass law1 0 true * cellMass law1 0 = 1 / 4
  treatedCellTarget : cellMass law1 0 * outcomeMean law1 true 0 = 1 / 2
  labeledTV : ∀ n : Nat,
    Causalean.Stat.tvDist (labeledProductLaw law0 n) (labeledProductLaw law1 n) =
      1 - (3 / 4 : Real) ^ n

-- @node: integral_pi_fin_one
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma integral_pi_fin_one {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [Fintype X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → Real) :
    ∫ x : Fin 1 → X, f (x 0) ∂Measure.pi (fun _ : Fin 1 ↦ μ) = ∫ x, f x ∂μ := by
  have hmap : Measure.map (fun x : Fin 1 → X ↦ x 0)
      (Measure.pi (fun _ : Fin 1 ↦ μ)) = μ := by
    simpa using Measure.pi_map_eval (fun _ : Fin 1 ↦ μ) 0
  calc
    _ = ∫ x, f x ∂Measure.map (fun x : Fin 1 → X ↦ x 0)
        (Measure.pi (fun _ : Fin 1 ↦ μ)) := by
      rw [integral_map (measurable_pi_apply 0).aemeasurable
        (measurable_of_countable f).aestronglyMeasurable]
    _ = _ := by rw [hmap]

-- @node: tvDist_le_one_sub_common
/-- [the stated conditions](hyp:hE,hres,hμ,hν) establishes [the stated conclusion](goal). -/
lemma tvDist_le_one_sub_common {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Set X} (hE : MeasurableSet E) (hres : μ.restrict E = ν.restrict E)
    {q : Real} (hμ : μ.real E = q) (hν : ν.real E = q) :
    Causalean.Stat.tvDist μ ν ≤ 1 - q := by
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  rintro ⟨A, hA⟩
  have hcommon : μ.real (A ∩ E) = ν.real (A ∩ E) := by
    have h := congrArg (fun ξ : Measure X ↦ ξ.real A) hres
    change ((μ.restrict E) A).toReal = ((ν.restrict E) A).toReal at h
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA] at h
    rw [measureReal_def, measureReal_def]
    simpa [Set.inter_comm] using h
  have hμcompl : μ.real Eᶜ = 1 - q := by
    rw [measureReal_compl hE, probReal_univ, hμ]
  have hνcompl : ν.real Eᶜ = 1 - q := by
    rw [measureReal_compl hE, probReal_univ, hν]
  have hsubset : A ⊆ (A ∩ E) ∪ Eᶜ := by
    intro x hx
    by_cases hxe : x ∈ E
    · exact Or.inl ⟨hx, hxe⟩
    · exact Or.inr hxe
  have hμb : μ.real A ≤ μ.real (A ∩ E) + μ.real Eᶜ :=
    (measureReal_mono hsubset (measure_ne_top μ _)).trans (measureReal_union_le _ _)
  have hνb : ν.real A ≤ ν.real (A ∩ E) + ν.real Eᶜ :=
    (measureReal_mono hsubset (measure_ne_top ν _)).trans (measureReal_union_le _ _)
  have hμl : μ.real (A ∩ E) ≤ μ.real A :=
    measureReal_mono Set.inter_subset_left (measure_ne_top μ _)
  have hνl : ν.real (A ∩ E) ≤ ν.real A :=
    measureReal_mono Set.inter_subset_left (measure_ne_top ν _)
  rw [abs_le]
  constructor <;> linarith

-- @node: smallAlternative_auxMarginal
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma smallAlternative_auxMarginal (z : AuxObs 2) :
    (auxMarginal smallAlternativeLaw z).toReal = 1 / 4 := by
  rcases z with ⟨x, a⟩
  unfold auxMarginal
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases x <;> cases a <;>
    norm_num [smallAlternativeLaw, smallAlternativeAtomMass,
      Fintype.sum_prod_type, ENNReal.toReal_add, ENNReal.toReal_inv]

-- @node: smallCommonAtom
/-- This declaration defines [the specified object](goal). -/
def smallCommonAtom : Set (Obs 2) := {z | z.1 ≠ 0 ∨ z.2.1 ≠ true}

-- @node: smallCommonSample
/-- [the stated conditions](hyp:n) defines [the specified object](goal). -/
def smallCommonSample (n : Nat) : Set (Fin n → Obs 2) :=
  Set.pi Set.univ (fun _ ↦ smallCommonAtom)

-- @node: smallCommonNullMass
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma smallCommonNullMass :
    obsLaw smallNullLaw smallCommonAtom = (3 / 4 : ENNReal) := by
  rw [obsLaw, PMF.toMeasure_apply_fintype]
  norm_num [smallCommonAtom, Set.indicator, smallNullLaw, smallNullAtomMass,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_add, ENNReal.toReal_inv]

-- @node: smallCommonAlternativeMass
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma smallCommonAlternativeMass :
    obsLaw smallAlternativeLaw smallCommonAtom = (3 / 4 : ENNReal) := by
  rw [obsLaw, PMF.toMeasure_apply_fintype]
  norm_num [smallCommonAtom, Set.indicator, smallAlternativeLaw,
    smallAlternativeAtomMass, Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_add, ENNReal.toReal_inv]

-- @node: smallCommonProductMassNull
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma smallCommonProductMassNull (n : Nat) :
    (labeledProductLaw smallNullLaw n).real (smallCommonSample n) =
      (3 / 4 : Real) ^ n := by
  rw [measureReal_def, labeledProductLaw, smallCommonSample, Measure.pi_pi]
  simp_rw [smallCommonNullMass]
  rw [ENNReal.toReal_prod]
  norm_num [ENNReal.toReal_div]
  rw [div_pow]

-- @node: smallCommonProductMassAlternative
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma smallCommonProductMassAlternative (n : Nat) :
    (labeledProductLaw smallAlternativeLaw n).real (smallCommonSample n) =
      (3 / 4 : Real) ^ n := by
  rw [measureReal_def, labeledProductLaw, smallCommonSample, Measure.pi_pi]
  simp_rw [smallCommonAlternativeMass]
  rw [ENNReal.toReal_prod]
  norm_num [ENNReal.toReal_div]
  rw [div_pow]

-- @node: smallAtomEqOfCommon
/-- [the stated conditions](hyp:hz) establishes [the stated conclusion](goal). -/
lemma smallAtomEqOfCommon (z : Obs 2) (hz : z ∈ smallCommonAtom) :
    smallNullLaw.pmf z = smallAlternativeLaw.pmf z := by
  rcases z with ⟨x, a, y⟩
  fin_cases x <;> cases a <;> cases y <;>
    simp [smallCommonAtom, smallNullLaw, smallAlternativeLaw, smallNullAtomMass,
      smallAlternativeAtomMass, PMF.ofFintype_apply] at hz ⊢

-- @node: smallCommonRestrictEq
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma smallCommonRestrictEq (n : Nat) :
    (labeledProductLaw smallNullLaw n).restrict (smallCommonSample n) =
      (labeledProductLaw smallAlternativeLaw n).restrict (smallCommonSample n) := by
  apply Measure.ext_of_singleton
  intro s
  rw [Measure.restrict_apply (measurableSet_singleton s),
    Measure.restrict_apply (measurableSet_singleton s)]
  by_cases hs : s ∈ smallCommonSample n
  · have hinter : ({s} : Set (Fin n → Obs 2)) ∩ smallCommonSample n = {s} := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      aesop
    rw [hinter]
    simp only [labeledProductLaw, Measure.pi_singleton]
    apply Finset.prod_congr rfl
    intro i _
    rw [obsLaw, obsLaw, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    exact smallAtomEqOfCommon (s i) (hs i (Set.mem_univ i))
  · have hinter : ({s} : Set (Fin n → Obs 2)) ∩ smallCommonSample n = ∅ := by
      ext z
      constructor
      · rintro ⟨rfl, hzs⟩
        exact (hs hzs).elim
      · intro hz
        exact hz.elim
    rw [hinter]
    simp

-- @node: smallAvoidNullAtom
/-- This declaration defines [the specified object](goal). -/
def smallAvoidNullAtom : Set (Obs 2) := {z | z ≠ (0, true, false)}

-- @node: smallAvoidNullSample
/-- [the stated conditions](hyp:n) defines [the specified object](goal). -/
def smallAvoidNullSample (n : Nat) : Set (Fin n → Obs 2) :=
  Set.pi Set.univ (fun _ ↦ smallAvoidNullAtom)

-- @node: smallAvoidNullMass
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma smallAvoidNullMass :
    obsLaw smallNullLaw smallAvoidNullAtom = (3 / 4 : ENNReal) := by
  rw [obsLaw, PMF.toMeasure_apply_fintype]
  norm_num [smallAvoidNullAtom, Set.indicator, smallNullLaw, smallNullAtomMass,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_add, ENNReal.toReal_inv]

-- @node: smallAvoidAlternativeMass
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma smallAvoidAlternativeMass :
    obsLaw smallAlternativeLaw smallAvoidNullAtom = 1 := by
  rw [obsLaw, PMF.toMeasure_apply_fintype]
  norm_num [smallAvoidNullAtom, Set.indicator, smallAlternativeLaw,
    smallAlternativeAtomMass, Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_add, ENNReal.toReal_inv]

-- @node: smallAvoidProductMassNull
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma smallAvoidProductMassNull (n : Nat) :
    (labeledProductLaw smallNullLaw n).real (smallAvoidNullSample n) =
      (3 / 4 : Real) ^ n := by
  rw [measureReal_def, labeledProductLaw, smallAvoidNullSample, Measure.pi_pi]
  simp_rw [smallAvoidNullMass]
  rw [ENNReal.toReal_prod]
  norm_num [ENNReal.toReal_div]
  rw [div_pow]

-- @node: smallAvoidProductMassAlternative
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma smallAvoidProductMassAlternative (n : Nat) :
    (labeledProductLaw smallAlternativeLaw n).real (smallAvoidNullSample n) = 1 := by
  rw [measureReal_def, labeledProductLaw, smallAvoidNullSample, Measure.pi_pi]
  simp_rw [smallAvoidAlternativeMass]
  simp

-- @node: smallLabeledTV
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma smallLabeledTV (n : Nat) :
    Causalean.Stat.tvDist (labeledProductLaw smallNullLaw n)
      (labeledProductLaw smallAlternativeLaw n) = 1 - (3 / 4 : Real) ^ n := by
  letI : IsProbabilityMeasure (labeledProductLaw smallNullLaw n) := by
    unfold labeledProductLaw
    infer_instance
  letI : IsProbabilityMeasure (labeledProductLaw smallAlternativeLaw n) := by
    unfold labeledProductLaw
    infer_instance
  apply le_antisymm
  · exact tvDist_le_one_sub_common (Set.toFinite _ |>.measurableSet)
      (smallCommonRestrictEq n) (smallCommonProductMassNull n)
      (smallCommonProductMassAlternative n)
  · have hA : MeasurableSet (smallAvoidNullSample n)ᶜ := Set.toFinite _ |>.measurableSet
    have hgap := Causalean.Stat.abs_measureReal_sub_le_tvDist
      (μ := labeledProductLaw smallNullLaw n)
      (ν := labeledProductLaw smallAlternativeLaw n) hA
    rw [measureReal_compl (Set.toFinite _ |>.measurableSet), probReal_univ,
      smallAvoidProductMassNull,
      measureReal_compl (Set.toFinite _ |>.measurableSet), probReal_univ,
      smallAvoidProductMassAlternative] at hgap
    norm_num only [sub_self, sub_zero] at hgap
    have hpow : (3 / 4 : Real) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    rw [abs_of_nonneg (sub_nonneg.mpr hpow)] at hgap
    exact hgap

-- @node: smallNullCellMass
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma smallNullCellMass (x : Fin 2) : cellMass smallNullLaw x = 1 / 2 := by
  fin_cases x <;>
    norm_num [cellMass, jointMass, smallNullLaw, smallNullAtomMass,
      PMF.ofFintype_apply, ENNReal.toReal_inv]

-- @node: smallAlternativeCellMass
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma smallAlternativeCellMass (x : Fin 2) :
    cellMass smallAlternativeLaw x = 1 / 2 := by
  fin_cases x <;>
    norm_num [cellMass, jointMass, smallAlternativeLaw, smallAlternativeAtomMass,
      PMF.ofFintype_apply, ENNReal.toReal_inv]

-- @node: smallNullPropensity
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma smallNullPropensity (x : Fin 2) : propensity smallNullLaw x = 1 / 2 := by
  fin_cases x <;>
    norm_num [propensity, armMass, cellMass, jointMass, smallNullLaw,
      smallNullAtomMass, PMF.ofFintype_apply, ENNReal.toReal_inv]

-- @node: smallAlternativePropensity
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma smallAlternativePropensity (x : Fin 2) :
    propensity smallAlternativeLaw x = 1 / 2 := by
  fin_cases x <;>
    norm_num [propensity, armMass, cellMass, jointMass, smallAlternativeLaw,
      smallAlternativeAtomMass, PMF.ofFintype_apply, ENNReal.toReal_inv]

-- @node: smallNullControlMean
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma smallNullControlMean (x : Fin 2) : outcomeMean smallNullLaw false x = 0 := by
  fin_cases x <;>
    norm_num [outcomeMean, armMass, jointMass, smallNullLaw,
      smallNullAtomMass, PMF.ofFintype_apply, ENNReal.toReal_inv]

-- @node: smallAlternativeControlMean
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma smallAlternativeControlMean (x : Fin 2) :
    outcomeMean smallAlternativeLaw false x = 0 := by
  fin_cases x <;>
    norm_num [outcomeMean, armMass, jointMass, smallAlternativeLaw,
      smallAlternativeAtomMass, PMF.ofFintype_apply, ENNReal.toReal_inv]

-- @node: smallNullTreatedMean
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma smallNullTreatedMean (x : Fin 2) : outcomeMean smallNullLaw true x = 0 := by
  fin_cases x <;>
    norm_num [outcomeMean, armMass, jointMass, smallNullLaw,
      smallNullAtomMass, PMF.ofFintype_apply, ENNReal.toReal_inv]

-- @node: smallAlternativeTreatedMeanFirst
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma smallAlternativeTreatedMeanFirst : outcomeMean smallAlternativeLaw true 0 = 1 := by
  norm_num [outcomeMean, armMass, jointMass, smallAlternativeLaw,
    smallAlternativeAtomMass, PMF.ofFintype_apply, ENNReal.toReal_inv]

-- @node: smallAlternativeTreatedMeanSecond
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma smallAlternativeTreatedMeanSecond : outcomeMean smallAlternativeLaw true 1 = 0 := by
  norm_num [outcomeMean, armMass, jointMass, smallAlternativeLaw,
    smallAlternativeAtomMass, PMF.ofFintype_apply, ENNReal.toReal_inv]

-- @node: smallNullAuxTable
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma smallNullAuxTable (z : AuxObs 2) : auxTableOf smallNullLaw z = 1 / 4 := by
  rcases z with ⟨x, a⟩
  fin_cases x <;> cases a <;>
    norm_num [auxTableOf, auxMarginal, armMass, jointMass,
      smallNullLaw, smallNullAtomMass,
      PMF.map_apply, PMF.ofFintype_apply, ENNReal.toReal_inv]

-- @node: smallAlternativeAuxTable
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma smallAlternativeAuxTable (z : AuxObs 2) :
    auxTableOf smallAlternativeLaw z = 1 / 4 := by
  rcases z with ⟨x, a⟩
  fin_cases x <;> cases a <;>
    norm_num [auxTableOf, auxMarginal, armMass, jointMass,
      smallAlternativeLaw, smallAlternativeAtomMass,
      PMF.map_apply, PMF.ofFintype_apply, ENNReal.toReal_inv]

-- @node: smallNullTarget
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma smallNullTarget : ateFunctional smallNullLaw = 0 := by
  norm_num [ateFunctional, cellMass, outcomeMean, armMass, jointMass,
    smallNullLaw, smallNullAtomMass, PMF.ofFintype_apply, ENNReal.toReal_inv]

-- @node: smallAlternativeTarget
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma smallAlternativeTarget : ateFunctional smallAlternativeLaw = 1 / 2 := by
  norm_num [ateFunctional, cellMass, outcomeMean, armMass, jointMass,
    smallAlternativeLaw, smallAlternativeAtomMass, PMF.ofFintype_apply,
    ENNReal.toReal_inv]

-- @node: smallAlternativeAuxIntegral
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma smallAlternativeAuxIntegral :
    (∫ y : Fin 1 → AuxObs 2,
      ((if y 0 = (0, false) then 1 else 0) +
        (if y 0 = (0, true) then 1 else 0) : Real)
      ∂auxProductLaw smallAlternativeLaw 1) = 1 / 2 := by
  rw [auxProductLaw]
  let f : AuxObs 2 → Real := fun z ↦
    (if z = (0, false) then 1 else 0) + (if z = (0, true) then 1 else 0)
  calc
    _ = ∫ z, f z ∂(auxMarginal smallAlternativeLaw).toMeasure :=
      integral_pi_fin_one _ f
    _ = _ := by
      rw [PMF.integral_eq_sum]
      simp_rw [smallAlternative_auxMarginal]
      norm_num [f, Fintype.sum_prod_type]

-- @node: smallAlternativeLabelIntegral
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma smallAlternativeLabelIntegral :
    (∫ x : Fin 1 → Obs 2,
      (if x 0 = (0, true, true) then 1 else 0 : Real)
      ∂labeledProductLaw smallAlternativeLaw 1) = 1 / 4 := by
  rw [labeledProductLaw]
  let f : Obs 2 → Real := fun z ↦ if z = (0, true, true) then 1 else 0
  calc
    _ = ∫ z, f z ∂obsLaw smallAlternativeLaw := integral_pi_fin_one _ f
    _ = _ := by
      rw [show obsLaw smallAlternativeLaw = smallAlternativeLaw.pmf.toMeasure from rfl,
        PMF.integral_eq_sum]
      norm_num [f, smallAlternativeLaw, smallAlternativeAtomMass,
        PMF.ofFintype_apply, ENNReal.toReal_inv]

-- @node: smallAlternativeExpectationIdentity
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma smallAlternativeExpectationIdentity :
    ∫ z, smallMixedStatistic z ∂annotationLaw smallAlternativeLaw 1 1 =
      2 * markedMass smallAlternativeLaw 0 true * cellMass smallAlternativeLaw 0 := by
  letI : IsProbabilityMeasure (labeledProductLaw smallAlternativeLaw 1) := by
    unfold labeledProductLaw
    infer_instance
  letI : IsProbabilityMeasure (auxProductLaw smallAlternativeLaw 1) := by
    unfold auxProductLaw
    infer_instance
  rw [annotationLaw, MeasureTheory.integral_prod]
  all_goals try exact Integrable.of_finite
  simp only [smallMixedStatistic]
  have hinner (x : Fin 1 → Obs 2) :
      (∫ y : Fin 1 → AuxObs 2,
        (2 * if x 0 = (0, true, true) then 1 else 0) *
          ((if y 0 = (0, false) then 1 else 0) +
            (if y 0 = (0, true) then 1 else 0))
        ∂auxProductLaw smallAlternativeLaw 1) =
      (2 * if x 0 = (0, true, true) then 1 else 0) * (1 / 2 : Real) := by
    rw [integral_const_mul, smallAlternativeAuxIntegral]
  simp_rw [hinner]
  have hid : (fun x : Fin 1 → Obs 2 ↦
      (2 * if x 0 = (0, true, true) then 1 else 0) * (1 / 2 : Real)) =
      fun x ↦ (if x 0 = (0, true, true) then 1 else 0 : Real) := by
    funext x
    split_ifs <;> norm_num
  rw [hid, smallAlternativeLabelIntegral]
  norm_num [markedMass, cellMass, jointMass, smallAlternativeLaw,
    smallAlternativeAtomMass, PMF.ofFintype_apply, ENNReal.toReal_inv]
/-- The formal statement establishes [the stated conclusion](goal). -/

lemma exists_finiteSmallInstance : Nonempty FiniteCalculationWitness := by
  refine ⟨{
    Pi0Small := Measure.dirac smallNullLaw
    Pi1Small := Measure.dirac smallAlternativeLaw
    law0 := smallNullLaw
    law1 := smallAlternativeLaw
    prior0_dirac := rfl
    prior1_dirac := rfl
    class0 := ?_
    class1 := ?_
    cellMass0 := smallNullCellMass
    cellMass1 := smallAlternativeCellMass
    propensity0 := smallNullPropensity
    propensity1 := smallAlternativePropensity
    controlMean0 := smallNullControlMean
    controlMean1 := smallAlternativeControlMean
    treatedMean0 := smallNullTreatedMean
    treatedMean1_first := smallAlternativeTreatedMeanFirst
    treatedMean1_second := smallAlternativeTreatedMeanSecond
    uniformAux0 := smallNullAuxTable
    uniformAux1 := smallAlternativeAuxTable
    uniformAux := by funext z; rw [smallNullAuxTable, smallAlternativeAuxTable]
    target0 := smallNullTarget
    target1 := smallAlternativeTarget
    expectationIdentity := smallAlternativeExpectationIdentity
    expectationValue := by
      norm_num [markedMass, cellMass, jointMass, smallAlternativeLaw,
        smallAlternativeAtomMass, PMF.ofFintype_apply, ENNReal.toReal_inv]
    treatedCellTarget := by
      norm_num [cellMass, outcomeMean, armMass, jointMass, smallAlternativeLaw,
        smallAlternativeAtomMass, PMF.ofFintype_apply, ENNReal.toReal_inv]
    labeledTV := smallLabeledTV }⟩
  · refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
    intro x _
    rw [smallNullPropensity]
    constructor <;> norm_num
  · refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
    intro x _
    rw [smallAlternativePropensity]
    constructor <;> norm_num

-- @node: def:finite-small-instance
/-- The explicit `d=2`, `epsilon=1/4`, `n=m=1` common-marginal calculation.  [the stated conclusion](goal). -/
noncomputable def finiteSmallInstance : FiniteCalculationWitness :=
  Classical.choice exists_finiteSmallInstance
  -- @realizes \Pi_0^{\mathrm{small}}(point mass at the null two-cell law)
  -- @realizes \Pi_1^{\mathrm{small}}(point mass at the alternative two-cell law)
  -- @realizes \mathfrak C_{\mathrm{small}}(mixed identity, common marginal, ATE gap, labeled TV)

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

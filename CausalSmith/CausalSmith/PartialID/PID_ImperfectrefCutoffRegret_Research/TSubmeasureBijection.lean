import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Helpers.SlicePasting
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Helpers.DerivedMargins
import Mathlib.MeasureTheory.Measure.Sub

/-! Bijection between compatible completion laws and dominated allocations. -/

open MeasureTheory
open scoped BigOperators

namespace CausalSmith.PartialID.ImperfectrefCutoffRegret

noncomputable section

def completionAllocation (Q : Measure (ℝ × Bool × Bool)) : Bool → Measure ℝ :=
  fun r => (Q.restrict {z | z.2.1 = r ∧ z.2.2 = true}).map Prod.fst

def allocationCurve (M : ImperfectReferenceModel) (ν : Bool → Measure ℝ) :
    Cutoff M → ℝ × ℝ × ℝ :=
  fun t =>
    ((∑ r : Bool, (ν r).real (referSet t.1)) / prevalence M,
      ((∑ r : Bool, stratumMass M r (referSet t.1)) -
        ∑ r : Bool, (ν r).real (referSet t.1)) / (1 - prevalence M),
      (M.b + M.c) * (∑ r : Bool, (ν r).real (referSet t.1)) -
        M.c * ∑ r : Bool, stratumMass M r (referSet t.1))

-- @node: measureReal_bool_partition
lemma measureReal_bool_partition {X : Type*} [MeasurableSpace X]
    (Q : Measure X) [IsFiniteMeasure Q] (A : Set X) (hA : MeasurableSet A)
    (d : X → Bool) (hd : Measurable d) :
    Q.real A = Q.real (A ∩ {x | d x = false}) +
      Q.real (A ∩ {x | d x = true}) := by
  rw [← measureReal_union]
  · congr 1
    ext x
    constructor
    · intro hx
      cases hdx : d x <;> simp [hx, hdx]
    · rintro (hx | hx) <;> exact hx.1
  · exact Set.disjoint_left.2 (by
      intro x hx0 hx1
      exact Bool.false_ne_true (hx0.2.symm.trans hx1.2))
  · exact hA.inter (hd (MeasurableSet.singleton true))

-- @node: completionAllocation_apply
lemma completionAllocation_apply (Q : Measure (ℝ × Bool × Bool))
    [IsFiniteMeasure Q] (r : Bool) (B : Set ℝ) (hB : MeasurableSet B) :
    (completionAllocation Q r).real B =
      Q.real {z | z.1 ∈ B ∧ z.2.1 = r ∧ z.2.2 = true} := by
  unfold completionAllocation
  rw [map_measureReal_apply measurable_fst hB,
    measureReal_restrict_apply (hB.preimage measurable_fst)]
  congr 1

-- @node: compatible_disease_probability
lemma compatible_disease_probability (M : ImperfectReferenceModel)
    (Q : Measure (ℝ × Bool × Bool)) (hQ : CompatibleLaw M Q) :
    Q.real {z | z.2.2 = true} = prevalence M := by
  letI := hQ.probability
  have hq1 : obsMass M true = Q.real {z | z.2.1 = true} := by
    rw [obsMass_eq_reference_event, ← hQ.observed]
    have hf : Measurable (fun z : ℝ × Bool × Bool => (z.1, z.2.1)) := by
      fun_prop
    change (Q.map (fun z => (z.1, z.2.1))).real
      (Prod.snd ⁻¹' {true}) = _
    rw [map_measureReal_apply hf
      (measurable_snd (MeasurableSet.singleton true))]
    rfl
  have hruniv : Q.real Set.univ = 1 := by simp
  have hdpart := measureReal_bool_partition Q Set.univ MeasurableSet.univ
    (fun z => z.2.2) (by fun_prop)
  have hr1part := measureReal_bool_partition Q {z | z.2.1 = true}
    ((measurable_fst.comp measurable_snd) (MeasurableSet.singleton true))
    (fun z => z.2.2) (by fun_prop)
  have hd0part := measureReal_bool_partition Q {z | z.2.2 = false}
    ((measurable_snd.comp measurable_snd) (MeasurableSet.singleton false))
    (fun z => z.2.1) (by fun_prop)
  simp only [Set.univ_inter, Set.mem_setOf_eq] at hdpart
  have hr1part' : Q.real {z | z.2.1 = true} =
      Q.real {z | z.2.1 = true ∧ z.2.2 = false} +
      Q.real {z | z.2.1 = true ∧ z.2.2 = true} := by
    simpa [Set.inter_def] using hr1part
  have hd0part' : Q.real {z | z.2.2 = false} =
      Q.real {z | z.2.1 = false ∧ z.2.2 = false} +
      Q.real {z | z.2.1 = true ∧ z.2.2 = false} := by
    simpa [Set.inter_def, and_left_comm, and_comm] using hd0part
  rw [hQ.sensitivity] at hr1part'
  rw [hQ.specificity] at hd0part'
  have hhealthy : Q.real {z | z.2.2 = false} =
      1 - Q.real {z | z.2.2 = true} := by linarith
  have hr1d0 : Q.real {z | z.2.1 = true ∧ z.2.2 = false} =
      (1 - M.beta) * Q.real {z | z.2.2 = false} := by
    linarith [hd0part']
  have hq1formula : obsMass M true =
      M.alpha * Q.real {z | z.2.2 = true} +
        (1 - M.beta) * Q.real {z | z.2.2 = false} := by
    rw [hq1, hr1part', hr1d0]
    ring
  have hg0 : youden M ≠ 0 := ne_of_gt hQ.informative
  rw [hhealthy] at hq1formula
  unfold prevalence
  field_simp [hg0]
  unfold youden at *
  nlinarith

-- @node: compatible_allocation
lemma compatible_allocation (M : ImperfectReferenceModel)
    (Q : Measure (ℝ × Bool × Bool)) (hQ : CompatibleLaw M Q) :
    DominatedAllocation M (completionAllocation Q) := by
  letI := hQ.probability
  constructor
  · intro r
    letI : IsFiniteMeasure (completionAllocation Q r) := by
      unfold completionAllocation
      infer_instance
    rw [Measure.le_iff]
    intro B hB
    rw [← ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)]
    change (completionAllocation Q r).real B ≤ (obsMeasure M r).real B
    rw [completionAllocation_apply Q r B hB]
    have hobs : (obsMeasure M r).real B =
        Q.real {z | z.1 ∈ B ∧ z.2.1 = r} := by
      change ((M.P.restrict {z | z.2 = r}).map Prod.fst).real B = _
      rw [map_measureReal_apply measurable_fst hB,
        measureReal_restrict_apply (hB.preimage measurable_fst), ← hQ.observed]
      have hf : Measurable (fun z : ℝ × Bool × Bool => (z.1, z.2.1)) := by
        fun_prop
      let A : Set (ℝ × Bool) := {z | z.1 ∈ B ∧ z.2 = r}
      have hA : MeasurableSet A :=
        (hB.preimage measurable_fst).inter
          (measurable_snd (MeasurableSet.singleton r))
      change (Q.map (fun z => (z.1, z.2.1))).real A = _
      rw [map_measureReal_apply hf hA]
      rfl
    rw [hobs]
    exact measureReal_mono (by aesop)
  · intro r
    rw [completionAllocation_apply Q r Set.univ MeasurableSet.univ]
    have hp := compatible_disease_probability M Q hQ
    cases r
    · have hdpart := measureReal_bool_partition Q {z | z.2.2 = true}
        ((measurable_snd.comp measurable_snd) (MeasurableSet.singleton true))
        (fun z => z.2.1) (by fun_prop)
      have hdpart' : Q.real {z | z.2.2 = true} =
          Q.real {z | z.2.1 = false ∧ z.2.2 = true} +
          Q.real {z | z.2.1 = true ∧ z.2.2 = true} := by
        simpa [Set.inter_def, and_left_comm, and_comm] using hdpart
      rw [hQ.sensitivity, hp] at hdpart'
      simp only [diseaseMass, Bool.false_eq_true, ↓reduceIte]
      simpa using (show Q.real {z | z.2.1 = false ∧ z.2.2 = true} =
          (1 - M.alpha) * prevalence M by linarith)
    · simp only [Set.mem_univ, true_and]
      rw [hQ.sensitivity, hp]
      rfl

-- @node: allocationSlices
noncomputable def allocationSlices (M : ImperfectReferenceModel)
    (ν : Bool → Measure ℝ) : Bool → Bool → Measure ℝ :=
  fun r d => if d then ν r else obsMeasure M r - ν r

-- @node: allocationCompletion
noncomputable def allocationCompletion (M : ImperfectReferenceModel)
    (ν : Bool → Measure ℝ) : Measure (ℝ × Bool × Bool) :=
  pasteSlices (allocationSlices M ν)

-- @node: allocationCompletion_slice_apply
lemma allocationCompletion_slice_apply (M : ImperfectReferenceModel)
    (ν : Bool → Measure ℝ) (hν : DominatedAllocation M ν)
    (r d : Bool) (B : Set ℝ) (hB : MeasurableSet B) :
    (allocationCompletion M ν).real
        {z | z.1 ∈ B ∧ z.2.1 = r ∧ z.2.2 = d} =
      if d then (ν r).real B
      else (obsMeasure M r).real B - (ν r).real B := by
  letI : IsFiniteMeasure (ν r) :=
    isFiniteMeasure_of_le (obsMeasure M r) (hν.domination r)
  have hfin (r d : Bool) : IsFiniteMeasure (allocationSlices M ν r d) := by
    unfold allocationSlices
    split
    · exact isFiniteMeasure_of_le (obsMeasure M r) (hν.domination r)
    · infer_instance
  rw [allocationCompletion, pasteSlices_slice_apply _ r d B hB hfin]
  unfold allocationSlices
  split
  · rfl
  · rw [measureReal_def, Measure.sub_apply hB (hν.domination r)]
    rw [ENNReal.toReal_sub_of_le (hν.domination r B) (measure_ne_top _ _)]
    rfl

-- @node: allocationCompletion_allocation
lemma allocationCompletion_allocation (M : ImperfectReferenceModel)
    (ν : Bool → Measure ℝ) (hν : DominatedAllocation M ν) :
    completionAllocation (allocationCompletion M ν) = ν := by
  funext r
  ext B hB
  letI : IsFiniteMeasure (ν r) :=
    isFiniteMeasure_of_le (obsMeasure M r) (hν.domination r)
  have hfin (r d : Bool) : IsFiniteMeasure (allocationSlices M ν r d) := by
    unfold allocationSlices
    split
    · exact isFiniteMeasure_of_le (obsMeasure M r) (hν.domination r)
    · infer_instance
  letI : IsFiniteMeasure (allocationCompletion M ν) := by
    letI := hfin true true
    letI := hfin true false
    letI := hfin false true
    letI := hfin false false
    unfold allocationCompletion pasteSlices
    infer_instance
  letI : IsFiniteMeasure
      (completionAllocation (allocationCompletion M ν) r) := by
    unfold completionAllocation
    infer_instance
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)]
  change (completionAllocation (allocationCompletion M ν) r).real B = (ν r).real B
  rw [completionAllocation_apply _ r B hB,
    allocationCompletion_slice_apply M ν hν r true B hB]
  rfl

-- @node: allocationCompletion_probability
lemma allocationCompletion_probability (M : ImperfectReferenceModel)
    (ν : Bool → Measure ℝ) (hν : DominatedAllocation M ν) :
    IsProbabilityMeasure (allocationCompletion M ν) := by
  apply pasteSlices_probability
  have hfin (r : Bool) : IsFiniteMeasure (ν r) :=
    isFiniteMeasure_of_le (obsMeasure M r) (hν.domination r)
  simp only [allocationSlices, Fintype.sum_bool, Bool.false_eq_true,
    ↓reduceIte]
  have hcancel (r : Bool) : (obsMeasure M r - ν r) Set.univ + ν r Set.univ =
      obsMeasure M r Set.univ := by
    letI := hfin r
    rw [← Measure.add_apply, Measure.sub_add_cancel_of_le (hν.domination r)]
  rw [add_comm (ν true Set.univ), hcancel true,
    add_comm (ν false Set.univ), hcancel false]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by simp)).mp
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  change obsMass M true + obsMass M false = 1
  simpa [add_comm] using obsMass_false_add_true M

-- @node: obsMeasure_section_apply
lemma obsMeasure_section_apply (M : ImperfectReferenceModel) (r : Bool)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (obsMeasure M r).real B = M.P.real {z | z.1 ∈ B ∧ z.2 = r} := by
  change ((M.P.restrict {z | z.2 = r}).map Prod.fst).real B = _
  rw [map_measureReal_apply measurable_fst hB,
    measureReal_restrict_apply (hB.preimage measurable_fst)]
  rfl

-- @node: allocationCompletion_observed
lemma allocationCompletion_observed (M : ImperfectReferenceModel)
    (ν : Bool → Measure ℝ) (hν : DominatedAllocation M ν) :
    ObservedMargin M (allocationCompletion M ν) := by
  have hprob := allocationCompletion_probability M ν hν
  letI := hprob
  rw [ObservedMargin]
  ext A hA
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)]
  have hf : Measurable (fun z : ℝ × Bool × Bool => (z.1, z.2.1)) := by
    fun_prop
  change ((allocationCompletion M ν).map
      (fun z => (z.1, z.2.1))).real A = M.P.real A
  rw [map_measureReal_apply hf hA]
  let B : Bool → Set ℝ := fun r => (fun s : ℝ => (s, r)) ⁻¹' A
  have hB (r : Bool) : MeasurableSet (B r) := by
    exact hA.preimage (measurable_id.prodMk measurable_const)
  have hr := measureReal_bool_partition (allocationCompletion M ν)
    ((fun z : ℝ × Bool × Bool => (z.1, z.2.1)) ⁻¹' A)
    (hA.preimage hf) (fun z => z.2.1) (by fun_prop)
  have hrd (r : Bool) := measureReal_bool_partition (allocationCompletion M ν)
    (((fun z : ℝ × Bool × Bool => (z.1, z.2.1)) ⁻¹' A) ∩
      {z | z.2.1 = r})
    ((hA.preimage hf).inter
      ((measurable_fst.comp measurable_snd) (MeasurableSet.singleton r)))
    (fun z => z.2.2) (by fun_prop)
  have hs (r : Bool) :
      ((fun z : ℝ × Bool × Bool => (z.1, z.2.1)) ⁻¹' A) ∩
          {z | z.2.1 = r} = {z | z.1 ∈ B r ∧ z.2.1 = r} := by
    ext z
    rcases z with ⟨s, ⟨r', d⟩⟩
    change ((s, r') ∈ A ∧ r' = r) ↔ ((s, r) ∈ A ∧ r' = r)
    constructor
    · rintro ⟨hz, rfl⟩
      exact ⟨hz, rfl⟩
    · rintro ⟨hz, rfl⟩
      exact ⟨hz, rfl⟩
  have hrd' (r : Bool) :
      (allocationCompletion M ν).real
          {z | z.1 ∈ B r ∧ z.2.1 = r} =
        (allocationCompletion M ν).real
            {z | z.1 ∈ B r ∧ z.2.1 = r ∧ z.2.2 = false} +
        (allocationCompletion M ν).real
            {z | z.1 ∈ B r ∧ z.2.1 = r ∧ z.2.2 = true} := by
    have h := hrd r
    rw [hs r] at h
    simpa [Set.inter_def, and_assoc] using h
  have hsum (r : Bool) :
      (allocationCompletion M ν).real
          {z | z.1 ∈ B r ∧ z.2.1 = r} = (obsMeasure M r).real (B r) := by
    rw [hrd' r, allocationCompletion_slice_apply M ν hν r false (B r) (hB r),
      allocationCompletion_slice_apply M ν hν r true (B r) (hB r)]
    have hle := ENNReal.toReal_mono (measure_ne_top _ _) (hν.domination r (B r))
    simp only [Bool.false_eq_true, if_false, if_true]
    linarith
  have hr' : (allocationCompletion M ν).real
      ((fun z : ℝ × Bool × Bool => (z.1, z.2.1)) ⁻¹' A) =
        (obsMeasure M false).real (B false) +
        (obsMeasure M true).real (B true) := by
    rw [hs false, hs true] at hr
    rw [hsum false, hsum true] at hr
    exact hr
  rw [hr']
  have hp := measureReal_bool_partition M.P A hA Prod.snd measurable_snd
  have hp' : M.P.real A =
        (obsMeasure M false).real (B false) +
        (obsMeasure M true).real (B true) := by
    rw [obsMeasure_section_apply M false (B false) (hB false),
      obsMeasure_section_apply M true (B true) (hB true)]
    have hsP (r : Bool) : A ∩ {z : ℝ × Bool | z.2 = r} =
        {z | z.1 ∈ B r ∧ z.2 = r} := by
      ext z
      rcases z with ⟨s, b⟩
      change ((s, b) ∈ A ∧ b = r) ↔ ((s, r) ∈ A ∧ b = r)
      constructor
      · rintro ⟨hz, rfl⟩
        exact ⟨hz, rfl⟩
      · rintro ⟨hz, rfl⟩
        exact ⟨hz, rfl⟩
    rw [hsP false, hsP true] at hp
    exact hp
  exact hp'.symm

-- @node: allocationCompletion_disease_probability
lemma allocationCompletion_disease_probability (M : ImperfectReferenceModel)
    (ν : Bool → Measure ℝ) (hν : DominatedAllocation M ν) :
    (allocationCompletion M ν).real {z | z.2.2 = true} = prevalence M := by
  letI := allocationCompletion_probability M ν hν
  have hpart := measureReal_bool_partition (allocationCompletion M ν)
    {z | z.2.2 = true}
    ((measurable_snd.comp measurable_snd) (MeasurableSet.singleton true))
    (fun z => z.2.1) (by fun_prop)
  have hpart' : (allocationCompletion M ν).real {z | z.2.2 = true} =
      (allocationCompletion M ν).real
          {z | z.1 ∈ Set.univ ∧ z.2.1 = false ∧ z.2.2 = true} +
      (allocationCompletion M ν).real
          {z | z.1 ∈ Set.univ ∧ z.2.1 = true ∧ z.2.2 = true} := by
    simpa [Set.inter_def, and_left_comm, and_comm, and_assoc] using hpart
  rw [hpart', allocationCompletion_slice_apply M ν hν false true Set.univ
      MeasurableSet.univ,
    allocationCompletion_slice_apply M ν hν true true Set.univ MeasurableSet.univ]
  simp only [if_pos rfl]
  rw [hν.mass false, hν.mass true]
  simpa [Fintype.sum_bool, add_comm] using diseaseMass_sum M

-- @node: allocationCompletion_compatible
lemma allocationCompletion_compatible (M : ImperfectReferenceModel)
    (hg : InformativeReference M) (hπ : InteriorPrevalence M)
    (ν : Bool → Measure ℝ) (hν : DominatedAllocation M ν) :
    CompatibleLaw M (allocationCompletion M ν) := by
  let hprob := allocationCompletion_probability M ν hν
  letI := hprob
  have hp := allocationCompletion_disease_probability M ν hν
  refine
    { probability := hprob
      observed := allocationCompletion_observed M ν hν
      sensitivity := ?_
      specificity := ?_
      informative := hg
      interior := hπ }
  · rw [ReferenceSensitivity]
    rw [show (allocationCompletion M ν).real
          {z | z.2.1 = true ∧ z.2.2 = true} =
        (allocationCompletion M ν).real
          {z | z.1 ∈ Set.univ ∧ z.2.1 = true ∧ z.2.2 = true} by
      congr 1; ext z; simp]
    rw [allocationCompletion_slice_apply M ν hν true true Set.univ
      MeasurableSet.univ]
    simp only [if_pos rfl]
    rw [hν.mass true, hp]
    simp [diseaseMass]
  · rw [ReferenceSpecificity]
    rw [show (allocationCompletion M ν).real
          {z | z.2.1 = false ∧ z.2.2 = false} =
        (allocationCompletion M ν).real
          {z | z.1 ∈ Set.univ ∧ z.2.1 = false ∧ z.2.2 = false} by
      congr 1; ext z; simp]
    rw [allocationCompletion_slice_apply M ν hν false false Set.univ
      MeasurableSet.univ]
    simp only [if_neg Bool.false_ne_true]
    rw [hν.mass false]
    have hdpart := measureReal_bool_partition (allocationCompletion M ν)
      Set.univ MeasurableSet.univ (fun z => z.2.2) (by fun_prop)
    simp only [Set.univ_inter] at hdpart
    have hhealthy : (allocationCompletion M ν).real {z | z.2.2 = false} =
        1 - prevalence M := by
      have huniv : (allocationCompletion M ν).real Set.univ = 1 := by simp
      linarith
    rw [hhealthy]
    change obsMass M false - diseaseMass M false =
      M.beta * (1 - prevalence M)
    exact observed_minus_disease_false M hg

-- @node: compatible_slice_apply
lemma compatible_slice_apply (M : ImperfectReferenceModel)
    (Q : Measure (ℝ × Bool × Bool)) (hQ : CompatibleLaw M Q)
    (r d : Bool) (B : Set ℝ) (hB : MeasurableSet B) :
    Q.real {z | z.1 ∈ B ∧ z.2.1 = r ∧ z.2.2 = d} =
      if d then (completionAllocation Q r).real B
      else (obsMeasure M r).real B - (completionAllocation Q r).real B := by
  letI := hQ.probability
  cases d
  · simp only [Bool.false_eq_true, if_false]
    have hobs : (obsMeasure M r).real B =
        Q.real {z | z.1 ∈ B ∧ z.2.1 = r} := by
      rw [obsMeasure_section_apply M r B hB, ← hQ.observed]
      have hf : Measurable (fun z : ℝ × Bool × Bool => (z.1, z.2.1)) := by
        fun_prop
      let A : Set (ℝ × Bool) := {z | z.1 ∈ B ∧ z.2 = r}
      have hA : MeasurableSet A :=
        (hB.preimage measurable_fst).inter
          (measurable_snd (MeasurableSet.singleton r))
      change (Q.map (fun z => (z.1, z.2.1))).real A = _
      rw [map_measureReal_apply hf hA]
      rfl
    have hpart := measureReal_bool_partition Q
      {z | z.1 ∈ B ∧ z.2.1 = r}
      ((hB.preimage measurable_fst).inter
        ((measurable_fst.comp measurable_snd) (MeasurableSet.singleton r)))
      (fun z => z.2.2) (by fun_prop)
    have hpart' : Q.real {z | z.1 ∈ B ∧ z.2.1 = r} =
        Q.real {z | z.1 ∈ B ∧ z.2.1 = r ∧ z.2.2 = false} +
        Q.real {z | z.1 ∈ B ∧ z.2.1 = r ∧ z.2.2 = true} := by
      simpa [Set.inter_def, and_assoc] using hpart
    rw [completionAllocation_apply Q r B hB]
    linarith
  · simp only [if_true]
    exact (completionAllocation_apply Q r B hB).symm

-- @node: compatibleLaw_injective_allocation
lemma compatibleLaw_injective_allocation (M : ImperfectReferenceModel)
    (Q₁ Q₂ : Measure (ℝ × Bool × Bool))
    (hQ₁ : CompatibleLaw M Q₁) (hQ₂ : CompatibleLaw M Q₂)
    (heq : completionAllocation Q₁ = completionAllocation Q₂) : Q₁ = Q₂ := by
  letI := hQ₁.probability
  letI := hQ₂.probability
  ext A hA
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)]
  let B : Bool → Bool → Set ℝ := fun r d =>
    (fun s : ℝ => (s, r, d)) ⁻¹' A
  have hB (r d : Bool) : MeasurableSet (B r d) := by
    exact hA.preimage (measurable_id.prodMk
      (measurable_const.prodMk measurable_const))
  have hslice (r d : Bool) :
      Q₁.real {z | z.1 ∈ B r d ∧ z.2.1 = r ∧ z.2.2 = d} =
        Q₂.real {z | z.1 ∈ B r d ∧ z.2.1 = r ∧ z.2.2 = d} := by
    rw [compatible_slice_apply M Q₁ hQ₁ r d (B r d) (hB r d),
      compatible_slice_apply M Q₂ hQ₂ r d (B r d) (hB r d), heq]
  have hsliceSet (r d : Bool) :
      (A ∩ {z | z.2.1 = r}) ∩ {z | z.2.2 = d} =
        {z | z.1 ∈ B r d ∧ z.2.1 = r ∧ z.2.2 = d} := by
    ext z
    rcases z with ⟨s, ⟨r', d'⟩⟩
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    change (((s, r', d') ∈ A ∧ r' = r) ∧ d' = d) ↔
      ((s, r, d) ∈ A ∧ r' = r ∧ d' = d)
    constructor
    · rintro ⟨⟨hz, rfl⟩, rfl⟩
      exact ⟨hz, rfl, rfl⟩
    · rintro ⟨hz, rfl, rfl⟩
      exact ⟨⟨hz, rfl⟩, rfl⟩
  have expand (Q : Measure (ℝ × Bool × Bool)) [IsFiniteMeasure Q] :
      Q.real A =
        Q.real {z | z.1 ∈ B false false ∧ z.2.1 = false ∧ z.2.2 = false} +
        Q.real {z | z.1 ∈ B false true ∧ z.2.1 = false ∧ z.2.2 = true} +
        (Q.real {z | z.1 ∈ B true false ∧ z.2.1 = true ∧ z.2.2 = false} +
         Q.real {z | z.1 ∈ B true true ∧ z.2.1 = true ∧ z.2.2 = true}) := by
    have hr := measureReal_bool_partition Q A hA (fun z => z.2.1) (by fun_prop)
    have hrd (r : Bool) := measureReal_bool_partition Q (A ∩ {z | z.2.1 = r})
      (hA.inter ((measurable_fst.comp measurable_snd) (MeasurableSet.singleton r)))
      (fun z => z.2.2) (by fun_prop)
    rw [hr]
    rw [hrd false, hrd true]
    rw [hsliceSet false false, hsliceSet false true,
      hsliceSet true false, hsliceSet true true]
  change Q₁.real A = Q₂.real A
  rw [expand Q₁, expand Q₂]
  rw [hslice false false, hslice false true, hslice true false, hslice true true]

-- @node: allocationCurve_probability_bounds
lemma allocationCurve_probability_bounds (M : ImperfectReferenceModel)
    (hπ : InteriorPrevalence M) (ν : Bool → Measure ℝ)
    (hν : DominatedAllocation M ν) (t : Cutoff M) :
    (allocationCurve M ν t).1 ∈ Set.Icc (0 : ℝ) 1 ∧
      (allocationCurve M ν t).2.1 ∈ Set.Icc (0 : ℝ) 1 := by
  let I := referSet t.1
  have hnum0 : 0 ≤ ∑ r : Bool, (ν r).real I :=
    Finset.sum_nonneg fun _ _ => measureReal_nonneg
  have hnumle : ∑ r : Bool, (ν r).real I ≤ prevalence M := by
    calc
      _ ≤ ∑ r : Bool, (ν r).real Set.univ :=
        Finset.sum_le_sum fun r _ => by
          letI : IsFiniteMeasure (ν r) :=
            isFiniteMeasure_of_le (obsMeasure M r) (hν.domination r)
          exact measureReal_mono (Set.subset_univ _)
      _ = ∑ r : Bool, diseaseMass M r := by
        apply Finset.sum_congr rfl
        intro r _
        exact hν.mass r
      _ = prevalence M := diseaseMass_sum M
  have hres0 (r : Bool) :
      0 ≤ (obsMeasure M r).real I - (ν r).real I := by
    have hfin : IsFiniteMeasure (ν r) :=
      isFiniteMeasure_of_le (obsMeasure M r) (hν.domination r)
    exact sub_nonneg.mpr
      (ENNReal.toReal_mono (measure_ne_top _ _) (hν.domination r I))
  have hresle (r : Bool) :
      (obsMeasure M r).real I - (ν r).real I ≤
        obsMass M r - diseaseMass M r := by
    letI : IsFiniteMeasure (ν r) :=
      isFiniteMeasure_of_le (obsMeasure M r) (hν.domination r)
    have hc := ENNReal.toReal_mono (measure_ne_top _ _)
      (hν.domination r ((I : Set ℝ)ᶜ))
    change (ν r).real (I : Set ℝ)ᶜ ≤
      (obsMeasure M r).real (I : Set ℝ)ᶜ at hc
    rw [measureReal_compl I.property, measureReal_compl I.property,
      hν.mass r] at hc
    change diseaseMass M r - (ν r).real I ≤
      obsMass M r - (obsMeasure M r).real I at hc
    linarith
  have hresle' :
      (∑ r : Bool, stratumMass M r I) - ∑ r : Bool, (ν r).real I ≤
        1 - prevalence M := by
    simp only [Fintype.sum_bool]
    have hq := obsMass_false_add_true M
    have ha := diseaseMass_sum M
    simp only [Fintype.sum_bool] at ha
    change ((obsMeasure M true).real I + (obsMeasure M false).real I) -
      ((ν true).real I + (ν false).real I) ≤ 1 - prevalence M
    linarith [hresle true, hresle false, hq, ha]
  have hresnonneg : 0 ≤
      (∑ r : Bool, stratumMass M r I) - ∑ r : Bool, (ν r).real I := by
    simp only [Fintype.sum_bool]
    change 0 ≤ ((obsMeasure M true).real I + (obsMeasure M false).real I) -
      ((ν true).real I + (ν false).real I)
    linarith [hres0 true, hres0 false]
  simp only [allocationCurve]
  constructor
  · exact ⟨div_nonneg hnum0 (le_of_lt hπ.1),
      (div_le_one (hπ.1)).2 hnumle⟩
  · exact ⟨div_nonneg hresnonneg (sub_nonneg.mpr (le_of_lt hπ.2)),
      (div_le_one (sub_pos.mpr hπ.2)).2 hresle'⟩

def SubmeasureBijectionConclusion (M : ImperfectReferenceModel) : Prop :=
  Set.BijOn completionAllocation (compatibleLaws M) (dominatedAllocations M) ∧
  (∀ ν ∈ dominatedAllocations M, ∃ Q ∈ compatibleLaws M,
    completionAllocation Q = ν ∧
    ∀ r B, MeasurableSet B →
      Q.real {z | z.1 ∈ B ∧ z.2.1 = r ∧ z.2.2 = true} = (ν r).real B ∧
      Q.real {z | z.1 ∈ B ∧ z.2.1 = r ∧ z.2.2 = false} =
        (obsMeasure M r).real B - (ν r).real B) ∧
  jointCurveSet M = allocationCurve M '' dominatedAllocations M

-- @node: thm:submeasure-bijection
theorem submeasure_bijection (M : ImperfectReferenceModel)
    (hg : InformativeReference M) (hπ : InteriorPrevalence M)
    (Q : Measure (ℝ × Bool × Bool)) (hQ : CompatibleLaw M Q) :
    SubmeasureBijectionConclusion M := by
  have hcurve (Q' : Measure (ℝ × Bool × Bool))
      (hQ' : CompatibleLaw M Q') :
      (fun t => (tprCurve M ⟨Q', hQ'⟩ t, fprCurve M ⟨Q', hQ'⟩ t,
        netValueAt M ⟨Q', hQ'⟩ t.1)) =
        allocationCurve M (completionAllocation Q') := by
    funext t
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · exact netValue_allocation_identity M ⟨Q', hQ'⟩ t.1
  have hsurj : Set.SurjOn completionAllocation (compatibleLaws M)
      (dominatedAllocations M) := by
    intro ν hν
    let Qν := allocationCompletion M ν
    have hQν : CompatibleLaw M Qν :=
      allocationCompletion_compatible M hg hπ ν hν
    letI := hQν.probability
    exact ⟨Qν, hQν, allocationCompletion_allocation M ν hν⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, hsurj⟩
    · intro Q' hQ'
      exact compatible_allocation M Q' hQ'
    · intro Q₁ hQ₁ Q₂ hQ₂ heq
      exact compatibleLaw_injective_allocation M Q₁ Q₂ hQ₁ hQ₂ heq
  · intro ν hν
    let Qν := allocationCompletion M ν
    have hQν : CompatibleLaw M Qν :=
      allocationCompletion_compatible M hg hπ ν hν
    letI := hQν.probability
    refine ⟨Qν, hQν, allocationCompletion_allocation M ν hν, ?_⟩
    intro r B hB
    constructor
    · rw [← completionAllocation_apply Qν r B hB,
        allocationCompletion_allocation M ν hν]
    · exact allocationCompletion_slice_apply M ν hν r false B hB
  · ext curve
    constructor
    · rintro ⟨⟨Q', hQ'⟩, rfl, hbounds⟩
      exact ⟨completionAllocation Q', compatible_allocation M Q' hQ',
        (hcurve Q' hQ').symm⟩
    · rintro ⟨ν, hν, rfl⟩
      let Qν := allocationCompletion M ν
      have hQν : CompatibleLaw M Qν :=
        allocationCompletion_compatible M hg hπ ν hν
      have halloc : completionAllocation Qν = ν :=
        allocationCompletion_allocation M ν hν
      refine ⟨⟨Qν, hQν⟩, ?_, ?_⟩
      · rw [hcurve Qν hQν, halloc]
      · intro t
        have hbounds := allocationCurve_probability_bounds M hπ ν hν t
        change (allocationCurve M (completionAllocation Qν) t).1 ∈
            Set.Icc (0 : ℝ) 1 ∧
          (allocationCurve M (completionAllocation Qν) t).2.1 ∈
            Set.Icc (0 : ℝ) 1
        rw [halloc]
        exact hbounds

end
end CausalSmith.PartialID.ImperfectrefCutoffRegret

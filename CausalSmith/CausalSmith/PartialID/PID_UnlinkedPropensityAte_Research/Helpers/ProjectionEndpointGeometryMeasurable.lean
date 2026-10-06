module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionEndpointMeasurable

/-!
Closed convex hull geometry for unions of real intervals.

The main theorem identifies the closed convex hull of a nonempty bounded union
of intervals with the interval between the infimum of its active lower endpoints
and the supremum of its active upper endpoints.  Empty intervals are discarded.
-/

@[expose] public section

open Set

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- For [the specified mathematical inputs](hyp:ι,I,l,u), [this definition](goal) introduces the corresponding object. -/
@[no_expose]
def activeIntervalIndices {ι : Type*} (I : Set ι) (l u : ι → ℝ) : Set ι :=
  {i ∈ I | l i ≤ u i}

/-- For [the specified mathematical inputs](hyp:ι,I,l,u), [this definition](goal) introduces the corresponding object. -/
@[no_expose]
def intervalFamilyUnion {ι : Type*} (I : Set ι) (l u : ι → ℝ) : Set ℝ :=
  ⋃ i ∈ I, Set.Icc (l i) (u i)

/-- Given [the stated mathematical inputs and assumptions](hyp:ι,I,l,u), this result [establishes the stated mathematical conclusion](goal). -/
lemma intervalFamilyUnion_eq_active {ι : Type*} (I : Set ι) (l u : ι → ℝ) :
    intervalFamilyUnion I l u = intervalFamilyUnion (activeIntervalIndices I l u) l u := by
  ext z
  simp only [intervalFamilyUnion, activeIntervalIndices, Set.mem_iUnion,
    Set.mem_Icc, Set.mem_sep_iff]
  constructor
  · rintro ⟨i, hi, hlz, hzu⟩
    exact ⟨i, ⟨hi, hlz.trans hzu⟩, hlz, hzu⟩
  · rintro ⟨i, ⟨hi, _⟩, hlz, hzu⟩
    exact ⟨i, hi, hlz, hzu⟩

/-- Given [the stated mathematical inputs and assumptions](hyp:ι,I,l,u,hne,hbelow,habove), this result [establishes the stated mathematical conclusion](goal). -/
lemma closure_convexHull_intervalFamilyUnion_eq_Icc {ι : Type*}
    (I : Set ι) (l u : ι → ℝ)
    (hne : (activeIntervalIndices I l u).Nonempty)
    (hbelow : BddBelow (l '' activeIntervalIndices I l u))
    (habove : BddAbove (u '' activeIntervalIndices I l u)) :
    closure (convexHull ℝ (intervalFamilyUnion I l u)) =
      Set.Icc (sInf (l '' activeIntervalIndices I l u))
        (sSup (u '' activeIntervalIndices I l u)) := by
  let A := activeIntervalIndices I l u
  let R := intervalFamilyUnion I l u
  let L := sInf (l '' A)
  let U := sSup (u '' A)
  have hneL : (l '' A).Nonempty := hne.image l
  have hneU : (u '' A).Nonempty := hne.image u
  have hRactive : R = intervalFamilyUnion A l u :=
    intervalFamilyUnion_eq_active I l u
  have hRsub : R ⊆ Set.Icc L U := by
    rw [hRactive]
    intro z hz
    simp only [intervalFamilyUnion, Set.mem_iUnion, Set.mem_Icc] at hz
    obtain ⟨i, hiA, hlz, hzu⟩ := hz
    have hli : L ≤ l i := by
      exact csInf_le hbelow ⟨i, hiA, rfl⟩
    have hui : u i ≤ U := by
      exact le_csSup habove ⟨i, hiA, rfl⟩
    exact ⟨hli.trans hlz, hzu.trans hui⟩
  have hforward : closure (convexHull ℝ R) ⊆ Set.Icc L U :=
    closure_minimal (convexHull_min hRsub (convex_Icc L U)) isClosed_Icc
  have hLmem : L ∈ closure (convexHull ℝ R) := by
    have hLclosure : L ∈ closure (l '' A) := csInf_mem_closure hneL hbelow
    apply closure_mono _ hLclosure
    intro z hz
    obtain ⟨i, hiA, rfl⟩ := hz
    apply subset_convexHull ℝ
    rw [hRactive]
    simp only [intervalFamilyUnion, Set.mem_iUnion, Set.mem_Icc]
    exact ⟨i, hiA, le_rfl, hiA.2⟩
  have hUmem : U ∈ closure (convexHull ℝ R) := by
    have hUclosure : U ∈ closure (u '' A) := csSup_mem_closure hneU habove
    apply closure_mono _ hUclosure
    intro z hz
    obtain ⟨i, hiA, rfl⟩ := hz
    apply subset_convexHull ℝ
    rw [hRactive]
    simp only [intervalFamilyUnion, Set.mem_iUnion, Set.mem_Icc]
    exact ⟨i, hiA, hiA.2, le_rfl⟩
  have hLU : L ≤ U := by
    obtain ⟨i, hiA⟩ := hne
    exact (csInf_le hbelow ⟨i, hiA, rfl⟩).trans
      (hiA.2.trans (le_csSup habove ⟨i, hiA, rfl⟩))
  have hreverse : Set.Icc L U ⊆ closure (convexHull ℝ R) := by
    rw [← segment_eq_Icc hLU]
    exact (convex_convexHull ℝ R).closure.segment_subset hLmem hUmem
  exact Set.Subset.antisymm hforward hreverse

/-- For [the specified mathematical inputs](hyp:ε,J,n,m,g,α,x), [this definition](goal) introduces the corresponding object. -/
@[no_expose]
def activeSievedProjectionCandidates {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (x : ExternalSample ε J n m) :
    Set (ArmCellArray J OutcomeSpace × ArmCellArray J (ScoreSpace ε)) :=
  activeIntervalIndices (sievedProjectionCandidates g α x)
    projectedATEIntervalLower projectedATEIntervalUpper

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,x,b), this result [establishes the stated mathematical conclusion](goal). -/
lemma mem_activeSievedProjectionCandidates_iff {ε : ℝ} {J n m : ℕ}
    {g : ScoreSpace ε → LabelSpace J} {α : ℝ}
    {x : ExternalSample ε J n m}
    {b : ArmCellArray J OutcomeSpace × ArmCellArray J (ScoreSpace ε)} :
    b ∈ activeSievedProjectionCandidates g α x ↔
      b ∈ sievedProjectionCandidates g α x ∧
        projectedATEIntervalLower b ≤ projectedATEIntervalUpper b := by
  rfl

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,x,hne,hbelow,habove), this result [establishes the stated mathematical conclusion](goal). -/
lemma closure_convexHull_sievedProjectionIntervals_eq_Icc
    {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (x : ExternalSample ε J n m)
    (hne : (activeSievedProjectionCandidates g α x).Nonempty)
    (hbelow : BddBelow
      (projectedATEIntervalLower '' activeSievedProjectionCandidates g α x))
    (habove : BddAbove
      (projectedATEIntervalUpper '' activeSievedProjectionCandidates g α x)) :
    closure (convexHull ℝ
      (⋃ b ∈ sievedProjectionCandidates g α x,
        projectedATEInterval b.1 b.2)) =
      Set.Icc
        (sInf (projectedATEIntervalLower ''
          activeSievedProjectionCandidates g α x))
        (sSup (projectedATEIntervalUpper ''
          activeSievedProjectionCandidates g α x)) := by
  have h := closure_convexHull_intervalFamilyUnion_eq_Icc
    (sievedProjectionCandidates g α x)
    projectedATEIntervalLower projectedATEIntervalUpper hne hbelow habove
  simpa only [intervalFamilyUnion, activeSievedProjectionCandidates,
    projectedATEInterval_eq_Icc_endpoints] using h

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,x,hne,hbelow,habove), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalProjectionCI_eq_explicit_endpoints
    {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (x : ExternalSample ε J n m)
    (hne : (activeSievedProjectionCandidates g α x).Nonempty)
    (hbelow : BddBelow
      (projectedATEIntervalLower '' activeSievedProjectionCandidates g α x))
    (habove : BddAbove
      (projectedATEIntervalUpper '' activeSievedProjectionCandidates g α x)) :
    let L := sInf (projectedATEIntervalLower ''
      activeSievedProjectionCandidates g α x)
    let U := sSup (projectedATEIntervalUpper ''
      activeSievedProjectionCandidates g α x)
    sievedTotalizedProjectionCI g α x =
      if max (-1) L ≤ min 1 U then
        Set.Icc (max (-1) L) (min 1 U)
      else {0} := by
  dsimp only
  have hraw := closure_convexHull_sievedProjectionIntervals_eq_Icc
    g α x hne hbelow habove
  have hB : (sievedProjectionCandidates g α x).Nonempty := by
    obtain ⟨b, hb, _⟩ := hne
    exact ⟨b, hb⟩
  have hclip : Set.Icc (-1 : ℝ) 1 ∩
      Set.Icc
        (sInf (projectedATEIntervalLower ''
          activeSievedProjectionCandidates g α x))
        (sSup (projectedATEIntervalUpper ''
          activeSievedProjectionCandidates g α x)) =
      Set.Icc
        (max (-1) (sInf (projectedATEIntervalLower ''
          activeSievedProjectionCandidates g α x)))
        (min 1 (sSup (projectedATEIntervalUpper ''
          activeSievedProjectionCandidates g α x))) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_Icc]
    constructor
    · rintro ⟨⟨hzneg, hzone⟩, hzL, hzU⟩
      exact ⟨max_le hzneg hzL, le_min hzone hzU⟩
    · rintro ⟨hzL, hzU⟩
      exact ⟨⟨le_trans (le_max_left _ _) hzL,
        le_trans hzU (min_le_left _ _)⟩,
        le_trans (le_max_right _ _) hzL,
        le_trans hzU (min_le_right _ _)⟩
  rw [sievedTotalizedProjectionCI]
  rw [hraw, hclip]
  simp only [hB, Set.nonempty_Icc, true_and]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,hOverlap,g,hg,α), this result [establishes the stated mathematical conclusion](goal). -/
lemma measurableSet_activeSievedProjectionCandidates_nonempty
    {ε : ℝ} {J n m : ℕ}
    (hOverlap : Overlap ε) (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g) (α : ℝ) :
    MeasurableSet {x : ExternalSample ε J n m |
      (activeSievedProjectionCandidates g α x).Nonempty} := by
  let S := {b ∈ rationalArraySieve ε J |
    projectedATEIntervalLower b ≤ projectedATEIntervalUpper b}
  have hS : S.Countable :=
    (countable_rationalArraySieve ε J).mono (Set.sep_subset _ _)
  have hmeas : MeasurableSet
      (⋃ b ∈ S, {x : ExternalSample ε J n m |
        b ∈ projectionCandidates g α x}) := by
    exact MeasurableSet.biUnion hS fun b _ =>
      measurableSet_mem_projectionCandidates hOverlap g hg α b
  have heq : {x : ExternalSample ε J n m |
      (activeSievedProjectionCandidates g α x).Nonempty} =
      ⋃ b ∈ S, {x | b ∈ projectionCandidates g α x} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.nonempty_def,
      activeSievedProjectionCandidates, activeIntervalIndices,
      sievedProjectionCandidates, Set.mem_inter_iff, S]
    aesop
  rw [heq]
  exact hmeas

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,hOverlap,g,hg,α,hbelow), this result [establishes the stated mathematical conclusion](goal). -/
@[fun_prop]
lemma measurable_sInf_activeSievedProjectionCandidates
    {ε : ℝ} {J n m : ℕ}
    (hOverlap : Overlap ε) (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g) (α : ℝ)
    (hbelow : ∀ x : ExternalSample ε J n m, BddBelow
      (projectedATEIntervalLower '' activeSievedProjectionCandidates g α x)) :
    Measurable (fun x : ExternalSample ε J n m =>
      sInf (projectedATEIntervalLower ''
        activeSievedProjectionCandidates g α x)) := by
  apply measurable_of_Iio
  intro q
  let N : Set (ExternalSample ε J n m) :=
    {x | (activeSievedProjectionCandidates g α x).Nonempty}
  let E : Set (ExternalSample ε J n m) :=
    {x | ∃ b ∈ sievedProjectionCandidates g α x,
      projectedATEIntervalLower b ≤ projectedATEIntervalUpper b ∧
        projectedATEIntervalLower b < q}
  have hN : MeasurableSet N :=
    measurableSet_activeSievedProjectionCandidates_nonempty hOverlap g hg α
  have hE : MeasurableSet E :=
    measurableSet_exists_sievedCandidate_lower_lt hOverlap g hg α q
  have heq : (fun x : ExternalSample ε J n m =>
      sInf (projectedATEIntervalLower ''
        activeSievedProjectionCandidates g α x)) ⁻¹' Set.Iio q =
      (N ∩ E) ∪ (Nᶜ ∩ if 0 < q then Set.univ else ∅) := by
    ext x
    by_cases hx : (activeSievedProjectionCandidates g α x).Nonempty
    · have himage : (projectedATEIntervalLower ''
          activeSievedProjectionCandidates g α x).Nonempty :=
        hx.image projectedATEIntervalLower
      rw [Set.mem_preimage, Set.mem_Iio,
        csInf_lt_iff (hbelow x) himage]
      constructor
      · rintro ⟨z, ⟨b, hb, rfl⟩, hlt⟩
        apply Set.mem_union_left
        constructor
        · exact hx
        · exact ⟨b, hb.1, hb.2, hlt⟩
      · intro hrhs
        rcases hrhs with hmain | hfallback
        · obtain ⟨b, hb, hord, hlt⟩ := hmain.2
          exact ⟨projectedATEIntervalLower b,
            ⟨b, ⟨hb, hord⟩, rfl⟩, hlt⟩
        · exact False.elim (hfallback.1 hx)
    · have hempty : projectedATEIntervalLower ''
          activeSievedProjectionCandidates g α x = ∅ :=
        Set.image_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hx)
      by_cases hq : 0 < q <;>
        simp [Set.mem_preimage, hempty, N, E, hx, hq]
  rw [heq]
  exact (hN.inter hE).union (hN.compl.inter (by split_ifs <;> measurability))

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,hOverlap,g,hg,α,habove), this result [establishes the stated mathematical conclusion](goal). -/
@[fun_prop]
lemma measurable_sSup_activeSievedProjectionCandidates
    {ε : ℝ} {J n m : ℕ}
    (hOverlap : Overlap ε) (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g) (α : ℝ)
    (habove : ∀ x : ExternalSample ε J n m, BddAbove
      (projectedATEIntervalUpper '' activeSievedProjectionCandidates g α x)) :
    Measurable (fun x : ExternalSample ε J n m =>
      sSup (projectedATEIntervalUpper ''
        activeSievedProjectionCandidates g α x)) := by
  apply measurable_of_Iic
  intro q
  let N : Set (ExternalSample ε J n m) :=
    {x | (activeSievedProjectionCandidates g α x).Nonempty}
  let E : Set (ExternalSample ε J n m) :=
    {x | ∃ b ∈ sievedProjectionCandidates g α x,
      projectedATEIntervalLower b ≤ projectedATEIntervalUpper b ∧
        q < projectedATEIntervalUpper b}
  have hN : MeasurableSet N :=
    measurableSet_activeSievedProjectionCandidates_nonempty hOverlap g hg α
  have hE : MeasurableSet E :=
    measurableSet_exists_sievedCandidate_lt_upper hOverlap g hg α q
  have heq : (fun x : ExternalSample ε J n m =>
      sSup (projectedATEIntervalUpper ''
        activeSievedProjectionCandidates g α x)) ⁻¹' Set.Iic q =
      (N ∩ Eᶜ) ∪ (Nᶜ ∩ if 0 ≤ q then Set.univ else ∅) := by
    ext x
    by_cases hx : (activeSievedProjectionCandidates g α x).Nonempty
    · have himage : (projectedATEIntervalUpper ''
          activeSievedProjectionCandidates g α x).Nonempty :=
        hx.image projectedATEIntervalUpper
      rw [Set.mem_preimage, Set.mem_Iic]
      have hnot : sSup (projectedATEIntervalUpper ''
          activeSievedProjectionCandidates g α x) ≤ q ↔
          ¬q < sSup (projectedATEIntervalUpper ''
            activeSievedProjectionCandidates g α x) := not_lt.symm
      rw [hnot, lt_csSup_iff (habove x) himage]
      constructor
      · intro hno
        apply Set.mem_union_left
        refine ⟨hx, ?_⟩
        intro hE_mem
        obtain ⟨b, hb, hord, hlt⟩ := hE_mem
        exact hno ⟨projectedATEIntervalUpper b,
          ⟨b, ⟨hb, hord⟩, rfl⟩, hlt⟩
      · intro hrhs hex
        obtain ⟨z, ⟨b, hb, rfl⟩, hqz⟩ := hex
        rcases hrhs with hmain | hfallback
        · exact hmain.2 ⟨b, hb.1, hb.2, hqz⟩
        · exact False.elim (hfallback.1 hx)
    · have hempty : projectedATEIntervalUpper ''
          activeSievedProjectionCandidates g α x = ∅ :=
        Set.image_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hx)
      by_cases hq : 0 ≤ q <;>
        simp [Set.mem_preimage, hempty, N, E, hx, hq]
  rw [heq]
  exact (hN.inter hE.compl).union
    (hN.compl.inter (by split_ifs <;> measurability))

end
end CausalSmith.PartialID.UnlinkedPropensityAte

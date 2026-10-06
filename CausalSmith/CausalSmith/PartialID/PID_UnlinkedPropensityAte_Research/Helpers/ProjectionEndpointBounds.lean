module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionCandidateStability
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionEndpointGeometryMeasurable

/-!
Samplewise bounds and unconditional measurability for projection endpoints.

The zero pair of cell arrays is a finite compatible reference.  Candidate
stability against this reference uniformly bounds every admitted arm endpoint,
and hence both ATE endpoints, for each fixed external sample.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- For [the specified mathematical inputs](hyp:ε,J,n,m,g,α,x), [this definition](goal) introduces the corresponding object. -/
@[no_expose]
def projectionZeroReferenceRadius {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (x : ExternalSample ε J n m) : ℝ :=
  (ε⁻¹ + (ε ^ 2)⁻¹) *
    (4 * J / (α * Real.sqrt n) +
      (∑ a : ArmSpace, ∑ r : LabelSpace J,
        outcomeCDFDistance (empiricalTrialCells x.1 a r) 0) +
      2 * J * (2 - 2 * ε) / (α * Real.sqrt m) +
      (∑ a : ArmSpace, ∑ r : LabelSpace J,
        scoreCDFDistance (empiricalScoreCells g x.2 a r) 0))

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,a,upper), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectedArmEndpoint_zero {ε : ℝ} {J : ℕ}
    (a : ArmSpace) (upper : Bool) :
    projectedArmEndpoint (J := J)
      (fun _ : ArmSpace => fun _ : LabelSpace J => (0 : Measure OutcomeSpace))
      (fun _ : ArmSpace => fun _ : LabelSpace J =>
        (0 : Measure (ScoreSpace ε))) a upper = 0 := by
  simp [projectedArmEndpoint, Measure.real]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,hOverlap,x,b,hb,a,upper), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectionCandidate_armEndpoint_abs_le_zeroReference
    {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (hOverlap : Overlap ε) (x : ExternalSample ε J n m)
    (b : ArmCellArray J OutcomeSpace × ArmCellArray J (ScoreSpace ε))
    (hb : b ∈ projectionCandidates g α x)
    (a : ArmSpace) (upper : Bool) :
    |projectedArmEndpoint b.1 b.2 a upper| ≤
      projectionZeroReferenceRadius g α x := by
  let lam : ArmCellArray J OutcomeSpace := fun _ _ => 0
  let σ : ArmCellArray J (ScoreSpace ε) := fun _ _ => 0
  have hfinLam : ∀ a r, IsFiniteMeasure (lam a r) := by
    intro a r
    dsimp [lam]
    infer_instance
  have hfinσ : ∀ a r, IsFiniteMeasure (σ a r) := by
    intro a r
    dsimp [σ]
    infer_instance
  have hcompat : ProjectionCompatible lam σ := by
    intro a r
    simp [lam, σ, Measure.real]
  have h := projectionCandidate_armEndpoint_abs_le g α hOverlap x b lam σ
    hb hfinLam hfinσ hcompat a upper
  rw [show projectedArmEndpoint lam σ a upper = 0 by
    exact projectedArmEndpoint_zero a upper] at h
  simpa only [sub_zero, projectionZeroReferenceRadius, lam, σ] using h

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,hOverlap,x,b,hb), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectionCandidate_ATEEndpoints_abs_le_zeroReference
    {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (hOverlap : Overlap ε) (x : ExternalSample ε J n m)
    (b : ArmCellArray J OutcomeSpace × ArmCellArray J (ScoreSpace ε))
    (hb : b ∈ projectionCandidates g α x) :
    |projectedArmEndpoint b.1 b.2 true false -
      projectedArmEndpoint b.1 b.2 false true| ≤
        2 * projectionZeroReferenceRadius g α x ∧
      |projectedArmEndpoint b.1 b.2 true true -
        projectedArmEndpoint b.1 b.2 false false| ≤
          2 * projectionZeroReferenceRadius g α x := by
  have hbound (a : ArmSpace) (upper : Bool) :=
    projectionCandidate_armEndpoint_abs_le_zeroReference
      g α hOverlap x b hb a upper
  constructor
  · exact (abs_sub _ _).trans (by linarith [hbound true false, hbound false true])
  · exact (abs_sub _ _).trans (by linarith [hbound true true, hbound false false])

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,hOverlap,x), this result [establishes the stated mathematical conclusion](goal). -/
lemma bddBelow_projectedATEIntervalLower_active
    {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (hOverlap : Overlap ε) (x : ExternalSample ε J n m) :
    BddBelow (projectedATEIntervalLower ''
      activeSievedProjectionCandidates g α x) := by
  refine ⟨-2 * projectionZeroReferenceRadius g α x, ?_⟩
  intro z hz
  obtain ⟨b, hb, rfl⟩ := hz
  rw [mem_activeSievedProjectionCandidates_iff] at hb
  have hcand : b ∈ projectionCandidates g α x := hb.1.1
  have habs := (projectionCandidate_ATEEndpoints_abs_le_zeroReference
    g α hOverlap x b hcand).1
  have hmem : projectedATEIntervalLower b ∈ projectedATEInterval b.1 b.2 := by
    rw [projectedATEInterval_eq_Icc_endpoints]
    exact ⟨le_rfl, hb.2⟩
  change projectedATEIntervalLower b ∈ Set.Icc
    (projectedArmEndpoint b.1 b.2 true false -
      projectedArmEndpoint b.1 b.2 false true)
    (projectedArmEndpoint b.1 b.2 true true -
      projectedArmEndpoint b.1 b.2 false false) at hmem
  linarith [neg_le_of_abs_le habs, hmem.1]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,hOverlap,x), this result [establishes the stated mathematical conclusion](goal). -/
lemma bddAbove_projectedATEIntervalUpper_active
    {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (hOverlap : Overlap ε) (x : ExternalSample ε J n m) :
    BddAbove (projectedATEIntervalUpper ''
      activeSievedProjectionCandidates g α x) := by
  refine ⟨2 * projectionZeroReferenceRadius g α x, ?_⟩
  intro z hz
  obtain ⟨b, hb, rfl⟩ := hz
  rw [mem_activeSievedProjectionCandidates_iff] at hb
  have hcand : b ∈ projectionCandidates g α x := hb.1.1
  have habs := (projectionCandidate_ATEEndpoints_abs_le_zeroReference
    g α hOverlap x b hcand).2
  have hmem : projectedATEIntervalUpper b ∈ projectedATEInterval b.1 b.2 := by
    rw [projectedATEInterval_eq_Icc_endpoints]
    exact ⟨hb.2, le_rfl⟩
  change projectedATEIntervalUpper b ∈ Set.Icc
    (projectedArmEndpoint b.1 b.2 true false -
      projectedArmEndpoint b.1 b.2 false true)
    (projectedArmEndpoint b.1 b.2 true true -
      projectedArmEndpoint b.1 b.2 false false) at hmem
  linarith [le_abs_self (projectedArmEndpoint b.1 b.2 true true -
    projectedArmEndpoint b.1 b.2 false false), hmem.2, habs]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,hOverlap,g,hg,α), this result [establishes the stated mathematical conclusion](goal). -/
@[fun_prop]
lemma measurable_projectionActiveLowerInf
    {ε : ℝ} {J n m : ℕ}
    (hOverlap : Overlap ε) (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g) (α : ℝ) :
    Measurable (fun x : ExternalSample ε J n m =>
      sInf (projectedATEIntervalLower ''
        activeSievedProjectionCandidates g α x)) :=
  measurable_sInf_activeSievedProjectionCandidates hOverlap g hg α
    (bddBelow_projectedATEIntervalLower_active g α hOverlap)

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,hOverlap,g,hg,α), this result [establishes the stated mathematical conclusion](goal). -/
@[fun_prop]
lemma measurable_projectionActiveUpperSup
    {ε : ℝ} {J n m : ℕ}
    (hOverlap : Overlap ε) (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g) (α : ℝ) :
    Measurable (fun x : ExternalSample ε J n m =>
      sSup (projectedATEIntervalUpper ''
        activeSievedProjectionCandidates g α x)) :=
  measurable_sSup_activeSievedProjectionCandidates hOverlap g hg α
    (bddAbove_projectedATEIntervalUpper_active g α hOverlap)

/-- For [the specified mathematical inputs](hyp:ε,J,n,m,g,α,x), [this definition](goal) introduces the corresponding object. -/
@[no_expose]
def externalProjectionLower {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (x : ExternalSample ε J n m) : ℝ := by
  classical
  exact
  let A := activeSievedProjectionCandidates g α x
  let L := sInf (projectedATEIntervalLower '' A)
  let U := sSup (projectedATEIntervalUpper '' A)
  if A.Nonempty ∧ max (-1) L ≤ min 1 U then max (-1) L else 0

/-- For [the specified mathematical inputs](hyp:ε,J,n,m,g,α,x), [this definition](goal) introduces the corresponding object. -/
@[no_expose]
def externalProjectionUpper {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (x : ExternalSample ε J n m) : ℝ := by
  classical
  exact
  let A := activeSievedProjectionCandidates g α x
  let L := sInf (projectedATEIntervalLower '' A)
  let U := sSup (projectedATEIntervalUpper '' A)
  if A.Nonempty ∧ max (-1) L ≤ min 1 U then min 1 U else 0

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,hOverlap,g,hg,α), this result [establishes the stated mathematical conclusion](goal). -/
@[fun_prop]
lemma measurable_externalProjectionLower
    {ε : ℝ} {J n m : ℕ}
    (hOverlap : Overlap ε) (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g) (α : ℝ) :
    Measurable (externalProjectionLower (n := n) (m := m) g α) := by
  classical
  have hL := measurable_projectionActiveLowerInf
    (n := n) (m := m) hOverlap g hg α
  have hU := measurable_projectionActiveUpperSup
    (n := n) (m := m) hOverlap g hg α
  have hN := measurableSet_activeSievedProjectionCandidates_nonempty
    (n := n) (m := m) hOverlap g hg α
  have hclip : MeasurableSet {x : ExternalSample ε J n m |
      max (-1) (sInf (projectedATEIntervalLower ''
        activeSievedProjectionCandidates g α x)) ≤
      min 1 (sSup (projectedATEIntervalUpper ''
        activeSievedProjectionCandidates g α x))} :=
    measurableSet_le (measurable_const.max hL) (measurable_const.min hU)
  change Measurable (fun x : ExternalSample ε J n m =>
    if (activeSievedProjectionCandidates g α x).Nonempty ∧
        max (-1) (sInf (projectedATEIntervalLower ''
          activeSievedProjectionCandidates g α x)) ≤
        min 1 (sSup (projectedATEIntervalUpper ''
          activeSievedProjectionCandidates g α x)) then
      max (-1) (sInf (projectedATEIntervalLower ''
        activeSievedProjectionCandidates g α x)) else 0)
  exact (measurable_const.max hL).ite (hN.inter hclip)
    (measurable_const : Measurable (fun _ : ExternalSample ε J n m => (0 : ℝ)))

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,hOverlap,g,hg,α), this result [establishes the stated mathematical conclusion](goal). -/
@[fun_prop]
lemma measurable_externalProjectionUpper
    {ε : ℝ} {J n m : ℕ}
    (hOverlap : Overlap ε) (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g) (α : ℝ) :
    Measurable (externalProjectionUpper (n := n) (m := m) g α) := by
  classical
  have hL := measurable_projectionActiveLowerInf
    (n := n) (m := m) hOverlap g hg α
  have hU := measurable_projectionActiveUpperSup
    (n := n) (m := m) hOverlap g hg α
  have hN := measurableSet_activeSievedProjectionCandidates_nonempty
    (n := n) (m := m) hOverlap g hg α
  have hclip : MeasurableSet {x : ExternalSample ε J n m |
      max (-1) (sInf (projectedATEIntervalLower ''
        activeSievedProjectionCandidates g α x)) ≤
      min 1 (sSup (projectedATEIntervalUpper ''
        activeSievedProjectionCandidates g α x))} :=
    measurableSet_le (measurable_const.max hL) (measurable_const.min hU)
  change Measurable (fun x : ExternalSample ε J n m =>
    if (activeSievedProjectionCandidates g α x).Nonempty ∧
        max (-1) (sInf (projectedATEIntervalLower ''
          activeSievedProjectionCandidates g α x)) ≤
        min 1 (sSup (projectedATEIntervalUpper ''
          activeSievedProjectionCandidates g α x)) then
      min 1 (sSup (projectedATEIntervalUpper ''
        activeSievedProjectionCandidates g α x)) else 0)
  exact (measurable_const.min hU).ite (hN.inter hclip)
    (measurable_const : Measurable (fun _ : ExternalSample ε J n m => (0 : ℝ)))

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,hOverlap,x), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalProjectionCI_eq_selectedEndpoints
    {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (hOverlap : Overlap ε) (x : ExternalSample ε J n m) :
    sievedTotalizedProjectionCI g α x = Set.Icc
      (externalProjectionLower g α x) (externalProjectionUpper g α x) := by
  classical
  by_cases hA : (activeSievedProjectionCandidates g α x).Nonempty
  · rw [externalProjectionCI_eq_explicit_endpoints g α x hA
      (bddBelow_projectedATEIntervalLower_active g α hOverlap x)
      (bddAbove_projectedATEIntervalUpper_active g α hOverlap x)]
    simp only [externalProjectionLower, externalProjectionUpper, hA, true_and]
    split_ifs <;> simp
  · have hunion :
        (⋃ b ∈ sievedProjectionCandidates g α x,
          projectedATEInterval b.1 b.2) = ∅ := by
      ext z
      constructor
      · simp only [Set.mem_iUnion]
        rintro ⟨b, hb, hz⟩
        rw [projectedATEInterval_eq_Icc_endpoints] at hz
        exact hA ⟨b, (mem_activeSievedProjectionCandidates_iff).2
          ⟨hb, hz.1.trans hz.2⟩⟩
      · intro hz
        simpa using hz
    rw [sievedTotalizedProjectionCI]
    simp only [hunion, convexHull_empty, closure_empty, Set.inter_empty,
      Set.not_nonempty_empty, and_false, ↓reduceIte]
    simp [externalProjectionLower, externalProjectionUpper, hA]

/-- For [the specified mathematical inputs](hyp:ε,J,n,m,g,α,hOverlap,hg), [this definition](goal) introduces the corresponding object. -/
@[no_expose]
def externalProjectionIntervalProcedure
    {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (hOverlap : Overlap ε) (hg : Measurable g) :
    ExternalIntervalProcedure ε J n m where
  lo := externalProjectionLower g α
  hi := externalProjectionUpper g α
  measurable_lo := measurable_externalProjectionLower hOverlap g hg α
  measurable_hi := measurable_externalProjectionUpper hOverlap g hg α
  lower_bound := by
    intro x
    have hCI := externalProjectionCI_eq_selectedEndpoints g α hOverlap x
    obtain ⟨z, hz⟩ := externalProjectionCI_nonempty g α x
    rw [hCI] at hz
    have hloMem : externalProjectionLower g α x ∈ sievedTotalizedProjectionCI g α x := by
      rw [hCI]
      exact ⟨le_rfl, hz.1.trans hz.2⟩
    exact (externalProjectionCI_subset_Icc g α x hloMem).1
  ordered := by
    intro x
    have hCI := externalProjectionCI_eq_selectedEndpoints g α hOverlap x
    obtain ⟨z, hz⟩ := externalProjectionCI_nonempty g α x
    rw [hCI] at hz
    exact hz.1.trans hz.2
  upper_bound := by
    intro x
    have hCI := externalProjectionCI_eq_selectedEndpoints g α hOverlap x
    obtain ⟨z, hz⟩ := externalProjectionCI_nonempty g α x
    rw [hCI] at hz
    have hhiMem : externalProjectionUpper g α x ∈ sievedTotalizedProjectionCI g α x := by
      rw [hCI]
      exact ⟨hz.1.trans hz.2, le_rfl⟩
    exact (externalProjectionCI_subset_Icc g α x hhiMem).2

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,hOverlap,hg,x), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalProjectionIntervalProcedure_Icc
    {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (hOverlap : Overlap ε) (hg : Measurable g)
    (x : ExternalSample ε J n m) :
    Set.Icc ((externalProjectionIntervalProcedure g α hOverlap hg).lo x)
      ((externalProjectionIntervalProcedure g α hOverlap hg).hi x) =
        sievedTotalizedProjectionCI g α x := by
  exact (externalProjectionCI_eq_selectedEndpoints g α hOverlap x).symm

end
end CausalSmith.PartialID.UnlinkedPropensityAte

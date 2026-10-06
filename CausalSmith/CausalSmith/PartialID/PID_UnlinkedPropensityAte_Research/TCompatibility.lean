module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Basic
public import Mathlib.Probability.ConditionalProbability
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.CompatibilityFullLawConstruction

/-! Compatibility of a released law with a randomized causal population. -/

public section

open MeasureTheory Set
namespace CausalSmith.PartialID.UnlinkedPropensityAte

-- @node: compatibility_armCellMass_sum
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma compatibility_armCellMass_sum {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    [IsProbabilityMeasure H] (r : LabelSpace J) :
    (∑ a : ArmSpace, armCellMass H g a r) = H.real (cell g r) := by
  have hint : IntegrableOn (fun e : ScoreSpace ε => (e : ℝ)) (cell g r) H := by
    apply Integrable.of_bound (by fun_prop) (|ε| + |1 - ε| + 1)
    filter_upwards [] with e
    change |(e : ℝ)| ≤ |ε| + |1 - ε| + 1
    rcases e.property with ⟨he₁, he₂⟩
    have h₁ := neg_le_abs ε
    have h₂ := le_abs_self (1 - ε)
    have h₃ := neg_le_abs (1 - ε)
    have h₄ := le_abs_self ε
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  simp only [Fintype.sum_bool, armCellMass, armProb, Bool.false_eq_true,
    ↓reduceIte]
  rw [integral_sub (integrable_const 1) hint]
  simp

-- @node: releasedLabelMass_sum_arms
/-- Given [the stated mathematical inputs and assumptions](hyp:J,Prel,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma releasedLabelMass_sum_arms {J : ℕ}
    (Prel : Measure (Observation J)) [IsProbabilityMeasure Prel]
    (r : LabelSpace J) :
    Prel.real {z | z.1 = r} =
      ∑ a : ArmSpace, Prel.real {z | z.1 = r ∧ z.2.1 = a} := by
  let S : Set (Observation J) := {z | z.1 = r}
  let T : Set (Observation J) := {z | z.2.1 = true}
  have hT : MeasurableSet T :=
    measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const
  have h := measureReal_inter_add_sdiff (μ := Prel) (s := S) (t := T) hT
  have hST : S ∩ T = {z | z.1 = r ∧ z.2.1 = true} := by
    ext z
    simp [S, T]
  have hSD : S \ T = {z | z.1 = r ∧ z.2.1 = false} := by
    ext z
    simp [S, T, Bool.not_eq_true]
  rw [hST, hSD] at h
  simpa [S, Fintype.sum_bool] using h.symm

-- @node: compatibleCellMasses_of_label_treated
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hg,h), this result [establishes the stated mathematical conclusion](goal). -/
lemma compatibleCellMasses_of_label_treated {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) [IsProbabilityMeasure H]
    [IsProbabilityMeasure Prel] (hg : Measurable g)
    (h : ∀ r : LabelSpace J,
      Prel.real {z | z.1 = r} = H.real (cell g r) ∧
      Prel.real {z | z.1 = r ∧ z.2.1 = true} = armCellMass H g true r) :
    CompatibleCellMasses H g Prel := by
  refine ⟨inferInstance, inferInstance, hg, ?_⟩
  intro a r
  cases a
  · have hlabel := (h r).1
    have htreated := (h r).2
    have hsum := compatibility_armCellMass_sum H g r
    have hreleased := releasedLabelMass_sum_arms Prel r
    simp only [Fintype.sum_bool] at hsum hreleased
    linarith
  · exact (h r).2

-- @node: armCellMass_lower_overlap
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hOverlap,a,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma armCellMass_lower_overlap {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    [IsProbabilityMeasure H] (hOverlap : Overlap ε)
    (a : ArmSpace) (r : LabelSpace J) :
    ε * H.real (cell g r) ≤ armCellMass H g a r := by
  have hInt : IntegrableOn (fun e : ScoreSpace ε => armProb a e) (cell g r) H := by
    apply Integrable.of_bound (by
      cases a <;> simp only [armProb, Bool.false_eq_true, ↓reduceIte] <;> fun_prop) 1
    filter_upwards [] with e
    rcases e.property with ⟨he₁, he₂⟩
    rcases hOverlap with ⟨hε, hε'⟩
    change |armProb a e| ≤ 1
    cases a <;> simp [armProb, abs_le] <;> constructor <;> linarith
  have hMono : (∫ _ in cell g r, ε ∂H) ≤
      ∫ e in cell g r, armProb a e ∂H := by
    apply integral_mono (integrable_const ε) hInt
    intro e
    rcases e.property with ⟨he₁, he₂⟩
    rcases hOverlap with ⟨hε, hε'⟩
    cases a <;> simp [armProb] <;> linarith
  simpa [armCellMass, Measure.real_def, mul_comm] using hMono

-- @node: armCellMass_pos_of_cellMass_pos
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hOverlap,a,r,hcell), this result [establishes the stated mathematical conclusion](goal). -/
lemma armCellMass_pos_of_cellMass_pos {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    [IsProbabilityMeasure H] (hOverlap : Overlap ε)
    (a : ArmSpace) (r : LabelSpace J)
    (hcell : 0 < H.real (cell g r)) :
    0 < armCellMass H g a r := by
  have hbound := armCellMass_lower_overlap H g hOverlap a r
  exact lt_of_lt_of_le (mul_pos hOverlap.1 hcell) hbound

-- @node: armCellMass_eq_zero_iff_cellMass_eq_zero
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hOverlap,a,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma armCellMass_eq_zero_iff_cellMass_eq_zero {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    [IsProbabilityMeasure H] (hOverlap : Overlap ε)
    (a : ArmSpace) (r : LabelSpace J) :
    armCellMass H g a r = 0 ↔ H.real (cell g r) = 0 := by
  have h₀ := armCellMass_lower_overlap H g hOverlap false r
  have h₁ := armCellMass_lower_overlap H g hOverlap true r
  have hsum := compatibility_armCellMass_sum H g r
  have hmass : 0 ≤ H.real (cell g r) := measureReal_nonneg
  simp only [Fintype.sum_bool] at hsum
  constructor
  · intro h
    by_contra hne
    have hp : 0 < H.real (cell g r) := lt_of_le_of_ne hmass (Ne.symm hne)
    have := armCellMass_pos_of_cellMass_pos H g hOverlap a r hp
    linarith
  · intro h
    rw [h] at h₀ h₁ hsum
    cases a <;> simp_all <;> linarith

-- @node: armCellOutcomeLaw_isProbabilityMeasure
/-- Given [the stated mathematical inputs and assumptions](hyp:J,Prel,a,r,hq), this result [establishes the stated mathematical conclusion](goal). -/
lemma armCellOutcomeLaw_isProbabilityMeasure {J : ℕ}
    (Prel : Measure (Observation J)) [IsProbabilityMeasure Prel]
    (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < Prel.real {z | z.1 = r ∧ z.2.1 = a}) :
    IsProbabilityMeasure (armCellOutcomeLaw Prel inferInstance a r hq) := by
  let C : Set (Observation J) := {z | z.1 = r ∧ z.2.1 = a}
  have hC : Prel C ≠ 0 :=
    (measureReal_ne_zero_iff).mp (ne_of_gt hq)
  have hcond : IsProbabilityMeasure (ProbabilityTheory.cond Prel C) :=
    ProbabilityTheory.cond_isProbabilityMeasure hC
  have hmap : Measurable (fun z : Observation J => (z.2.2 : ℝ)) := by fun_prop
  unfold armCellOutcomeLaw
  change IsProbabilityMeasure
    ((Prel C)⁻¹ • ((Prel.restrict C).map (fun z : Observation J => (z.2.2 : ℝ))))
  rw [← Measure.map_smul]
  exact @Measure.isProbabilityMeasure_map _ _ _ _ _ hcond _ hmap.aemeasurable

-- @node: armCellOutcomeLaw_apply
/-- Given [the stated mathematical inputs and assumptions](hyp:J,Prel,a,r,hq,B,hB), this result [establishes the stated mathematical conclusion](goal). -/
lemma armCellOutcomeLaw_apply {J : ℕ}
    (Prel : Measure (Observation J)) [IsProbabilityMeasure Prel]
    (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < Prel.real {z | z.1 = r ∧ z.2.1 = a})
    (B : Set ℝ) (hB : MeasurableSet B) :
    armCellOutcomeLaw Prel inferInstance a r hq B =
      (Prel {z | z.1 = r ∧ z.2.1 = a})⁻¹ *
        Prel {z | z.1 = r ∧ z.2.1 = a ∧ (z.2.2 : ℝ) ∈ B} := by
  have hm : Measurable (fun z : Observation J => (z.2.2 : ℝ)) := by fun_prop
  have hC : MeasurableSet {z : Observation J | z.1 = r ∧ z.2.1 = a} :=
    (measurableSet_eq_fun measurable_fst measurable_const).inter
      (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const)
  simp only [armCellOutcomeLaw, Measure.smul_apply]
  rw [Measure.map_apply hm hB, Measure.restrict_apply (hm hB)]
  have hset :
      (fun z : Observation J => (z.2.2 : ℝ)) ⁻¹' B ∩
          {z | z.1 = r ∧ z.2.1 = a} =
        {z | z.1 = r ∧ z.2.1 = a ∧ (z.2.2 : ℝ) ∈ B} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    tauto
  rw [hset]
  simp only [smul_eq_mul]

-- @node: prop:compatibility
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hOverlap,hg), this result [establishes the stated mathematical conclusion](goal). -/
theorem compatible_nonempty_iff {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) [IsProbabilityMeasure H]
    -- @realizes H(probability normalization)
    [IsProbabilityMeasure Prel] -- @realizes Prel(probability normalization)
    (hOverlap : Overlap ε)
    (hg : Measurable g) :
    (∃ P : Measure (FullRow ε J), IsProbabilityMeasure P ∧
      CompatibleCausalLaw H g Prel P) ↔
      ∀ r : LabelSpace J,
        Prel.real {z | z.1 = r} = H.real (cell g r) ∧
        Prel.real {z | z.1 = r ∧ z.2.1 = true} =
          armCellMass H g true r := by
  constructor
  · rintro ⟨P, _, hP⟩ r
    have hMass := compatibleCellMasses_of_compatibleCausalLaw H g Prel P hP
    constructor
    · rw [releasedLabelMass_sum_arms]
      simp_rw [hMass.2.2.2]
      exact (compatibility_armCellMass_sum H g r)
    · exact hMass.2.2.2 true r
  · intro h
    have hMass : CompatibleCellMasses H g Prel :=
      compatibleCellMasses_of_label_treated H g Prel hg h
    let P := reconstructedFullLaw H g Prel hg
    refine ⟨P, reconstructedFullLaw_isProbabilityMeasure H g Prel hg hOverlap, ?_⟩
    exact reconstructedFullLaw_compatibleCausalLaw H g Prel hg hMass hOverlap

end CausalSmith.PartialID.UnlinkedPropensityAte

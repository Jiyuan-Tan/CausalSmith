module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.FixedLawMembership

/-!
Assigned-cell mass identity for a compatible fixed released law.

This identifies the mass used to normalize an assigned release-cell coupling
with the score-induced arm-cell mass.
-/

public section

open MeasureTheory Set
open scoped ENNReal
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

private lemma map_fst_withDensity_of_fst {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure (α × β)) (f : α → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity (fun x => f x.1)).map Prod.fst =
      (μ.map Prod.fst).withDensity f := by
  ext B hB
  rw [Measure.map_apply measurable_fst hB,
    withDensity_apply _ (hB.preimage measurable_fst), withDensity_apply _ hB,
    setLIntegral_map hB hf measurable_fst]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,P,hP,hOverlap,a), this result [establishes the stated mathematical conclusion](goal). -/
lemma compatible_assignedScoreLaw_eq_tilt {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (P : Measure (FullRow ε J))
    (hP : CompatibleCausalLaw H g Prel P) (hOverlap : Overlap ε)
    (a : ArmSpace) :
    (P.restrict {ω | arm ω = a}).map score =
      H.withDensity (fun e => ENNReal.ofReal (armProb a e)) := by
  letI : IsProbabilityMeasure P := hP.probability
  have hX : Measurable (latentTriple (ε := ε) (J := J)) := by
    unfold latentTriple score outcome0 outcome1
    fun_prop
  have hscore : Measurable (score (ε := ε) (J := J)) := by
    unfold score
    fun_prop
  have hf : Measurable (fun e : ScoreSpace ε =>
      ENNReal.ofReal (armProb a e)) := by
    cases a <;> simp [armProb] <;> fun_prop
  calc
    (P.restrict {ω | arm ω = a}).map score =
        (assignedLatentLaw P a).map Prod.fst := by
          unfold assignedLatentLaw
          rw [Measure.map_map measurable_fst hX]
          rfl
    _ = (propensityTiltedLatentLaw P a).map Prod.fst :=
      congrArg (fun μ : Measure (ScoreSpace ε × OutcomeSpace × OutcomeSpace) =>
        μ.map Prod.fst)
        (assignedLatentLaw_eq_propensityTiltedLatentLaw P hOverlap
          hP.randomizedAssignment a)
    _ = H.withDensity (fun e => ENNReal.ofReal (armProb a e)) := by
      unfold propensityTiltedLatentLaw
      rw [map_fst_withDensity_of_fst _ _ hf]
      rw [Measure.map_map measurable_fst hX]
      change (P.map score).withDensity _ = _
      rw [hP.scoreMarginal]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,P,hP,hOverlap,a,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma compatible_assignedCellWeightLaw_eq {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (P : Measure (FullRow ε J))
    (hP : CompatibleCausalLaw H g Prel P) (hOverlap : Overlap ε)
    (a : ArmSpace) (r : LabelSpace J) :
    (P.restrict {ω | arm ω = a ∧ g (score ω) = r}).map
        (fun ω => (armProb a (score ω))⁻¹) =
      ((H.withDensity (fun e => ENNReal.ofReal (armProb a e))).restrict
        (cell g r)).map (fun e => (armProb a e)⁻¹) := by
  let w : ScoreSpace ε → ℝ := fun e => (armProb a e)⁻¹
  have hw : Measurable w := by
    cases a <;> simp [w, armProb] <;> fun_prop
  have hscore : Measurable (score (ε := ε) (J := J)) := by
    unfold score
    fun_prop
  have hcell : MeasurableSet (cell g r) :=
    measurableSet_eq_fun hP.measurableRelease measurable_const
  have hS : {ω : FullRow ε J | arm ω = a ∧ g (score ω) = r} =
      {ω | arm ω = a} ∩ score ⁻¹' cell g r := by
    ext ω
    simp [cell]
  have hA : MeasurableSet {ω : FullRow ε J | arm ω = a} :=
    measurableSet_eq_fun (by unfold arm; fun_prop) measurable_const
  have hRestrict :
      (P.restrict {ω | arm ω = a}).restrict (score ⁻¹' cell g r) =
        P.restrict {ω | arm ω = a ∧ g (score ω) = r} := by
    rw [Measure.restrict_restrict' hA, hS, Set.inter_comm]
  calc
    (P.restrict {ω | arm ω = a ∧ g (score ω) = r}).map
        (fun ω => (armProb a (score ω))⁻¹) =
        ((P.restrict {ω | arm ω = a ∧ g (score ω) = r}).map score).map w := by
          rw [Measure.map_map hw hscore]
          rfl
    _ = (((P.restrict {ω | arm ω = a}).map score).restrict (cell g r)).map w := by
      rw [Measure.restrict_map hscore hcell, hRestrict]
    _ = ((H.withDensity (fun e => ENNReal.ofReal (armProb a e))).restrict
        (cell g r)).map (fun e => (armProb a e)⁻¹) := by
      rw [compatible_assignedScoreLaw_eq_tilt H g Prel P hP hOverlap a]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,P,hP,hMass,hOverlap,a,r,hq), this result [establishes the stated mathematical conclusion](goal). -/
lemma compatibleArmCellCoupling_map_snd {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (P : Measure (FullRow ε J))
    (hP : CompatibleCausalLaw H g Prel P)
    (hMass : CompatibleCellMasses H g Prel) (hOverlap : Overlap ε)
    (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) :
    (compatibleArmCellCoupling H g P a r hq).map Prod.snd =
      armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq := by
  unfold compatibleArmCellCoupling armCellWeightLaw armCellScoreLaw
  rw [Measure.map_smul, Measure.map_map (by fun_prop) (by
    cases a <;> simp [armProb, outcome0, outcome1, score] <;> fun_prop),
    Measure.map_smul]
  congr 1
  exact compatible_assignedCellWeightLaw_eq H g Prel P hP hOverlap a r

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,P,hP,hMass,a,r,hq), this result [establishes the stated mathematical conclusion](goal). -/
lemma compatibleArmCellCoupling_map_fst {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (P : Measure (FullRow ε J))
    (hP : CompatibleCausalLaw H g Prel P)
    (hMass : CompatibleCellMasses H g Prel)
    (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) :
    (compatibleArmCellCoupling H g P a r hq).map Prod.fst =
      armCellOutcomeLaw Prel hMass.2.1 a r
        (by rw [hMass.2.2.2 a r]; exact hq) := by
  have hpair : Measurable (fun ω : FullRow ε J =>
      (((if a then outcome1 ω else outcome0 ω : OutcomeSpace) : ℝ),
        (armProb a (score ω))⁻¹)) := by
    cases a <;> simp [armProb, outcome0, outcome1, score] <;> fun_prop
  unfold compatibleArmCellCoupling armCellOutcomeLaw
  rw [Measure.map_smul, Measure.map_map (by fun_prop) hpair]
  letI : IsProbabilityMeasure Prel := hMass.2.1
  have hTmeasure : Prel {z | z.1 = r ∧ z.2.1 = a} =
      ENNReal.ofReal (armCellMass H g a r) := by
    rw [← hMass.2.2.2 a r]
    exact (ENNReal.ofReal_toReal (measure_ne_top Prel _)).symm
  rw [hTmeasure]
  congr 1
  ext B hB
  have hY : Measurable (fun ω : FullRow ε J =>
      ((if a then outcome1 ω else outcome0 ω : OutcomeSpace) : ℝ)) := by
    cases a <;> simp [outcome0, outcome1] <;> fun_prop
  have hobs : Measurable (fun z : Observation J => (z.2.2 : ℝ)) := by fun_prop
  have hrecord : Measurable (releasedRecord (ε := ε) (J := J)) := by
    unfold releasedRecord label arm observed
    fun_prop
  have hT : MeasurableSet {z : Observation J | z.1 = r ∧ z.2.1 = a} :=
    (measurableSet_eq_fun measurable_fst measurable_const).inter
      (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const)
  change ((P.restrict {ω | arm ω = a ∧ g (score ω) = r}).map
    (fun ω : FullRow ε J =>
      ((if a then outcome1 ω else outcome0 ω : OutcomeSpace) : ℝ))) B = _
  rw [Measure.map_apply hY hB, Measure.restrict_apply (hB.preimage hY)]
  rw [Measure.map_apply hobs hB, Measure.restrict_apply (hB.preimage hobs)]
  rw [← hP.releasedLaw]
  unfold releasedLaw
  rw [Measure.map_apply hrecord ((hB.preimage hobs).inter hT)]
  apply measure_congr
  filter_upwards [hP.consistency, hP.deterministicRelease] with ω hcons hlabel
  change ((((if a then outcome1 ω else outcome0 ω : OutcomeSpace) : ℝ) ∈ B ∧
      arm ω = a ∧ g (score ω) = r) =
    ((observed ω : ℝ) ∈ B ∧ label ω = r ∧ arm ω = a))
  apply propext
  by_cases ha : arm ω = a
  · rw [ha] at hcons
    simp [ha, hcons, hlabel, and_comm]
  · simp [ha]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,P,hP,hMass,a,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma compatible_assignedArmCell_measureReal {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (P : Measure (FullRow ε J))
    (hP : CompatibleCausalLaw H g Prel P)
    (hMass : CompatibleCellMasses H g Prel)
    (a : ArmSpace) (r : LabelSpace J) :
    P.real {ω | arm ω = a ∧ g (score ω) = r} = armCellMass H g a r := by
  have hrecord : Measurable (releasedRecord (ε := ε) (J := J)) := by
    unfold releasedRecord label arm observed
    fun_prop
  have hcell : MeasurableSet {z : Observation J | z.1 = r ∧ z.2.1 = a} :=
    (measurableSet_eq_fun measurable_fst measurable_const).inter
      (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const)
  rw [← hMass.2.2.2 a r, ← hP.releasedLaw]
  unfold releasedLaw
  rw [MeasureTheory.map_measureReal_apply hrecord hcell]
  apply measureReal_congr
  filter_upwards [hP.deterministicRelease] with ω hlabel
  change (arm ω = a ∧ g (score ω) = r) = (label ω = r ∧ arm ω = a)
  apply propext
  simp [hlabel, and_comm]


/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,P,hP,hMass,hOverlap,a,r,hq), this result [establishes the stated mathematical conclusion](goal). -/
lemma compatibleArmCellCoupling_isCoupling {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (P : Measure (FullRow ε J))
    (hP : CompatibleCausalLaw H g Prel P)
    (hMass : CompatibleCellMasses H g Prel) (hOverlap : Overlap ε)
    (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) :
    Causalean.Stat.IsCoupling (compatibleArmCellCoupling H g P a r hq)
      (armCellOutcomeLaw Prel hMass.2.1 a r
        (by rw [hMass.2.2.2 a r]; exact hq))
      (armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq) := by
  letI : IsProbabilityMeasure P := hP.probability
  let S : Set (FullRow ε J) := {ω | arm ω = a ∧ g (score ω) = r}
  have hSreal : P.real S = armCellMass H g a r := by
    simpa [S] using compatible_assignedArmCell_measureReal H g Prel P hP hMass a r
  have hSmeasure : P S = ENNReal.ofReal (armCellMass H g a r) := by
    rw [← hSreal]
    exact (ENNReal.ofReal_toReal (measure_ne_top P S)).symm
  have hSzero : P S ≠ 0 := by
    rw [hSmeasure]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hq)
  let μ : Measure (FullRow ε J) := P.restrict S
  letI : IsFiniteMeasure μ := inferInstance
  letI : NeZero μ := by
    constructor
    intro hμ
    have : P S = 0 := by
      rw [← Measure.restrict_apply_univ S, show P.restrict S = μ from rfl, hμ]
      simp
    exact hSzero this
  have hprob : IsProbabilityMeasure
      ((ENNReal.ofReal (armCellMass H g a r))⁻¹ • μ) := by
    rw [← hSmeasure, ← Measure.restrict_apply_univ S]
    infer_instance
  have hpair : Measurable (fun ω : FullRow ε J =>
      (((if a then outcome1 ω else outcome0 ω : OutcomeSpace) : ℝ),
        (armProb a (score ω))⁻¹)) := by
    cases a <;> simp [armProb, outcome0, outcome1, score] <;> fun_prop
  refine ⟨?_, ?_, ?_⟩
  · unfold compatibleArmCellCoupling
    rw [← Measure.map_smul]
    change IsProbabilityMeasure
      (((ENNReal.ofReal (armCellMass H g a r))⁻¹ • μ).map _)
    exact @Measure.isProbabilityMeasure_map _ _ _ _ _ hprob _ hpair.aemeasurable
  · exact compatibleArmCellCoupling_map_fst H g Prel P hP hMass a r hq
  · exact compatibleArmCellCoupling_map_snd H g Prel P hP hMass hOverlap a r hq


end
end CausalSmith.PartialID.UnlinkedPropensityAte

module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.FixedLawEndpointConstruction

/-! Assembly of endpoint-attaining cell laws into bounded arm laws. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,a,r,hq,upper), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointCellScoreOutcomeLaw_snd {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) (upper : Bool) :
    (endpointCellScoreOutcomeLaw H g Prel hMass hOverlap a r hq upper).snd =
      armCellOutcomeLaw Prel hMass.2.1 a r
        (by rw [hMass.2.2.2 a r]; exact hq) := by
  let Y := armCellOutcomeLaw Prel hMass.2.1 a r
    (by rw [hMass.2.2.2 a r]; exact hq)
  let W := armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq
  let π : Measure (ℝ × ℝ) :=
    if upper then Causalean.Stat.comonotoneCoupling Y W
    else Causalean.Stat.countermonotoneCoupling Y W
  have hπ : Causalean.Stat.IsCoupling π Y W := by
    simpa [π, Y, W] using
      endpointCoupling_isCoupling H g Prel hMass hOverlap a r hq upper
  unfold Measure.snd
  calc
    (endpointCellScoreOutcomeLaw H g Prel hMass hOverlap a r hq upper).map
        Prod.snd =
        ((endpointCellScoreOutcomeLaw H g Prel hMass hOverlap a r hq upper).map
          (fun p => (p.2, (armProb a p.1)⁻¹))).map Prod.fst := by
      rw [Measure.map_map measurable_fst (by
        cases a <;> simp [armProb] <;> fun_prop)]
      rfl
    _ = π.map Prod.fst := by
      rw [endpointCellScoreOutcomeLaw_map_outcome_weight
        H g Prel hMass hOverlap a r hq upper]
    _ = Y := hπ.map_fst

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,a,r,hq,upper), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointCellScoreOutcomeLaw_outcome_support {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) (upper : Bool) :
    endpointCellScoreOutcomeLaw H g Prel hMass hOverlap a r hq upper
      {p | p.2 ∉ Icc (0 : ℝ) 1} = 0 := by
  let M := endpointCellScoreOutcomeLaw H g Prel hMass hOverlap a r hq upper
  have hs : MeasurableSet ({y : ℝ | y ∉ Icc (0 : ℝ) 1}) :=
    measurableSet_Icc.compl
  have hsnd : M.snd = armCellOutcomeLaw Prel hMass.2.1 a r
      (by rw [hMass.2.2.2 a r]; exact hq) :=
    endpointCellScoreOutcomeLaw_snd H g Prel hMass hOverlap a r hq upper
  have hset : {p : ScoreSpace ε × ℝ | p.2 ∉ Icc (0 : ℝ) 1} =
      Prod.snd ⁻¹' {y : ℝ | y ∉ Icc (0 : ℝ) 1} := rfl
  rw [hset, ← Measure.map_apply measurable_snd hs, show M.map Prod.snd = M.snd from rfl,
    hsnd]
  unfold armCellOutcomeLaw
  rw [Measure.smul_apply, Measure.map_apply (by fun_prop) hs]
  have hpre : (fun z : Observation J => (z.2.2 : ℝ)) ⁻¹'
      {y : ℝ | y ∉ Icc (0 : ℝ) 1} = ∅ := by
    ext z
    exact iff_false_intro (fun hz => hz z.2.2.property)
  rw [hpre]
  simp

/-- For [the specified mathematical inputs](hyp:y), [this definition](goal) introduces the corresponding object. -/
def clampOutcome (y : ℝ) : OutcomeSpace :=
  ⟨min 1 (max 0 y), by constructor <;> simp⟩
/-- This result [establishes the stated mathematical conclusion](goal). -/
lemma clampOutcome_measurable : Measurable clampOutcome := by
  unfold clampOutcome
  fun_prop
/-- Given [the stated mathematical inputs and assumptions](hyp:y,hy), this result [establishes the stated mathematical conclusion](goal). -/
lemma clampOutcome_coe_of_mem {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    ((clampOutcome y : OutcomeSpace) : ℝ) = y := by
  simp [clampOutcome, hy.1, hy.2]

/-- For [the specified mathematical inputs](hyp:ε,J,H,g,Prel,hMass,hOverlap,a,r,hq,upper), [this definition](goal) introduces the corresponding object. -/
def boundedEndpointCellLaw {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) (upper : Bool) :
    Measure (ScoreSpace ε × OutcomeSpace) :=
  (endpointCellScoreOutcomeLaw H g Prel hMass hOverlap a r hq upper).map
    (fun p => (p.1, clampOutcome p.2))
/-- For [the specified mathematical inputs](hyp:ε,J,H,g,Prel,hMass,hOverlap,a,r,hq,upper), [this definition](goal) introduces the corresponding object. -/
instance boundedEndpointCellLaw_isProbabilityMeasure {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) (upper : Bool) :
    IsProbabilityMeasure
      (boundedEndpointCellLaw H g Prel hMass hOverlap a r hq upper) := by
  unfold boundedEndpointCellLaw
  letI : IsProbabilityMeasure H := hMass.1
  letI : IsProbabilityMeasure Prel := hMass.2.1
  letI : Nonempty (ScoreSpace ε) := ⟨⟨1 / 2, by
    constructor <;> linarith [hOverlap.1, hOverlap.2]⟩⟩
  letI : IsProbabilityMeasure
      (endpointCellScoreOutcomeLaw H g Prel hMass hOverlap a r hq upper) :=
    endpointCellScoreOutcomeLaw_isProbabilityMeasure
      H g Prel hMass hOverlap a r hq upper
  exact Measure.isProbabilityMeasure_map (by
    exact (measurable_fst.prodMk (clampOutcome_measurable.comp measurable_snd)).aemeasurable)

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,a,r,hq,upper), this result [establishes the stated mathematical conclusion](goal). -/
lemma boundedEndpointCellLaw_fst {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) (upper : Bool) :
    (boundedEndpointCellLaw H g Prel hMass hOverlap a r hq upper).fst =
      armCellScoreLaw H hMass.1 g hMass.2.2.1 a r hq := by
  unfold boundedEndpointCellLaw Measure.fst
  rw [Measure.map_map measurable_fst (by
    exact measurable_fst.prodMk (clampOutcome_measurable.comp measurable_snd))]
  change (endpointCellScoreOutcomeLaw H g Prel hMass hOverlap a r hq upper).fst = _
  exact endpointCellScoreOutcomeLaw_fst H g Prel hMass hOverlap a r hq upper

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,a,r,hq,upper), this result [establishes the stated mathematical conclusion](goal). -/
lemma boundedEndpointCellLaw_map_real_outcome {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) (upper : Bool) :
    (boundedEndpointCellLaw H g Prel hMass hOverlap a r hq upper).map
        (fun p => (p.2 : ℝ)) =
      armCellOutcomeLaw Prel hMass.2.1 a r
        (by rw [hMass.2.2.2 a r]; exact hq) := by
  let M := endpointCellScoreOutcomeLaw H g Prel hMass hOverlap a r hq upper
  have hsupport : ∀ᵐ p ∂M, p.2 ∈ Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    exact endpointCellScoreOutcomeLaw_outcome_support
      H g Prel hMass hOverlap a r hq upper
  unfold boundedEndpointCellLaw
  change (M.map (fun p => (p.1, clampOutcome p.2))).map
    (fun p => (p.2 : ℝ)) = _
  have hb : Measurable
      (fun p : ScoreSpace ε × ℝ => (p.1, clampOutcome p.2)) :=
    measurable_fst.prodMk (clampOutcome_measurable.comp measurable_snd)
  have hc : Measurable (fun p : ScoreSpace ε × OutcomeSpace => (p.2 : ℝ)) := by
    fun_prop
  rw [Measure.map_map hc hb]
  calc
    M.map ((fun p : ScoreSpace ε × OutcomeSpace => (p.2 : ℝ)) ∘
        (fun p : ScoreSpace ε × ℝ => (p.1, clampOutcome p.2))) =
        M.map Prod.snd := by
      apply Measure.map_congr
      filter_upwards [hsupport] with p hp
      exact clampOutcome_coe_of_mem hp
    _ = _ := endpointCellScoreOutcomeLaw_snd
      H g Prel hMass hOverlap a r hq upper

/-- For [the specified mathematical inputs](hyp:ε,J,H,g,Prel,hMass,hOverlap,a,upper), [this definition](goal) introduces the corresponding object. -/
def endpointAssignedArmLaw {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) (upper : Bool) :
    Measure (ScoreSpace ε × OutcomeSpace) :=
  Measure.sum fun r : LabelSpace J =>
    if hq : 0 < armCellMass H g a r then
      ENNReal.ofReal (armCellMass H g a r) •
        boundedEndpointCellLaw H g Prel hMass hOverlap a r hq upper
    else 0

private lemma endpointAssignedCell_fst {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) (upper : Bool)
    (r : LabelSpace J) :
    (if hq : 0 < armCellMass H g a r then
      ENNReal.ofReal (armCellMass H g a r) •
        boundedEndpointCellLaw H g Prel hMass hOverlap a r hq upper
     else 0).map Prod.fst =
      (H.withDensity (fun e => ENNReal.ofReal (armProb a e))).restrict
        (cell g r) := by
  letI : IsProbabilityMeasure H := hMass.1
  have hInt : Integrable (armProb a : ScoreSpace ε → ℝ) H := by
    apply Integrable.of_bound (by
      cases a
      · change AEStronglyMeasurable (fun e : ScoreSpace ε => 1 - (e : ℝ)) H
        fun_prop
      · change AEStronglyMeasurable (fun e : ScoreSpace ε => (e : ℝ)) H
        fun_prop) 1
    filter_upwards [] with e
    rcases e.property with ⟨he0, he1⟩
    have hzero : 0 ≤ (e : ℝ) := le_trans hOverlap.1.le he0
    have hone : (e : ℝ) ≤ 1 := by linarith [he1, hOverlap.1]
    cases a
    · change |1 - (e : ℝ)| ≤ 1
      rw [abs_of_nonneg (by linarith)]
      linarith
    · change |(e : ℝ)| ≤ 1
      rw [abs_of_nonneg hzero]
      exact hone
  letI : IsFiniteMeasure
      (H.withDensity (fun e => ENNReal.ofReal (armProb a e))) :=
    isFiniteMeasure_withDensity_ofReal hInt.hasFiniteIntegral
  split
  · rename_i hq
    rw [Measure.map_smul]
    change ENNReal.ofReal (armCellMass H g a r) •
      (boundedEndpointCellLaw H g Prel hMass hOverlap a r hq upper).fst = _
    rw [boundedEndpointCellLaw_fst H g Prel hMass hOverlap a r hq upper]
    unfold armCellScoreLaw
    rw [smul_smul]
    rw [ENNReal.mul_inv_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hq))
      ENNReal.ofReal_ne_top, one_smul]
  · rename_i hq
    rw [Measure.map_zero]
    change 0 = (H.withDensity (fun e => ENNReal.ofReal (armProb a e))).restrict
      (cell g r)
    have hnonneg : 0 ≤ armCellMass H g a r := by
      rw [← propensityTilt_real_cell H g hMass.2.2.1 hOverlap a r]
      exact measureReal_nonneg
    have hqzero : armCellMass H g a r = 0 :=
      le_antisymm (le_of_not_gt hq) hnonneg
    have hreal :
        (H.withDensity (fun e => ENNReal.ofReal (armProb a e))).real
          (cell g r) = 0 := by
      rw [propensityTilt_real_cell H g hMass.2.2.1 hOverlap a r, hqzero]
    have hmeasure :
        (H.withDensity (fun e => ENNReal.ofReal (armProb a e))) (cell g r) = 0 :=
      (measureReal_eq_zero_iff).mp hreal
    exact (Measure.restrict_zero_set hmeasure).symm

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,a,upper,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointAssignedCell_realOutcome {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) (upper : Bool)
    (r : LabelSpace J) :
    (if hq : 0 < armCellMass H g a r then
      ENNReal.ofReal (armCellMass H g a r) •
        boundedEndpointCellLaw H g Prel hMass hOverlap a r hq upper
     else 0).map (fun p => (p.2 : ℝ)) =
      (Prel.restrict {z | z.1 = r ∧ z.2.1 = a}).map
        (fun z => (z.2.2 : ℝ)) := by
  let C : Set (Observation J) := {z | z.1 = r ∧ z.2.1 = a}
  letI : IsProbabilityMeasure Prel := hMass.2.1
  split
  · rename_i hq
    rw [Measure.map_smul,
      boundedEndpointCellLaw_map_real_outcome
        H g Prel hMass hOverlap a r hq upper]
    unfold armCellOutcomeLaw
    rw [smul_smul]
    have hC : Prel C = ENNReal.ofReal (armCellMass H g a r) := by
      calc
        Prel C = ENNReal.ofReal (Prel.real C) :=
          (ENNReal.ofReal_toReal (measure_ne_top Prel C)).symm
        _ = ENNReal.ofReal (armCellMass H g a r) := by
          rw [hMass.2.2.2 a r]
    change (ENNReal.ofReal (armCellMass H g a r) * (Prel C)⁻¹) •
        ((Prel.restrict C).map (fun z => (z.2.2 : ℝ))) = _
    rw [hC, ENNReal.mul_inv_cancel
      (ne_of_gt (ENNReal.ofReal_pos.mpr hq)) ENNReal.ofReal_ne_top, one_smul]
  · rename_i hq
    rw [Measure.map_zero]
    have hnonneg : 0 ≤ armCellMass H g a r := by
      rw [← hMass.2.2.2 a r]
      exact measureReal_nonneg
    have hqzero : armCellMass H g a r = 0 :=
      le_antisymm (le_of_not_gt hq) hnonneg
    have hCreal : Prel.real C = 0 := by
      rw [hMass.2.2.2 a r, hqzero]
    have hCzero : Prel C = 0 := (measureReal_eq_zero_iff).mp hCreal
    rw [Measure.restrict_zero_set hCzero, Measure.map_zero]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,a,upper), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointAssignedArmLaw_fst {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) (upper : Bool) :
    (endpointAssignedArmLaw H g Prel hMass hOverlap a upper).fst =
      H.withDensity (fun e => ENNReal.ofReal (armProb a e)) := by
  unfold endpointAssignedArmLaw Measure.fst
  rw [Measure.map_sum (by fun_prop)]
  simp_rw [endpointAssignedCell_fst H g Prel hMass hOverlap a upper]
  let μ := H.withDensity (fun e => ENNReal.ofReal (armProb a e))
  have hcell : ∀ r : LabelSpace J, MeasurableSet (cell g r) := by
    intro r
    exact measurableSet_eq_fun hMass.2.2.1 measurable_const
  have hdisj : Pairwise (fun r s : LabelSpace J =>
      Disjoint (cell g r) (cell g s)) := by
    intro r s hrs
    apply Set.disjoint_left.mpr
    intro e her hes
    exact hrs (her.symm.trans hes)
  have hunion : (⋃ r : LabelSpace J, cell g r) = Set.univ := by
    ext e
    simp [cell]
  rw [← Measure.restrict_iUnion hdisj hcell, hunion, Measure.restrict_univ]

private lemma map_withDensity_of_fst {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure (α × β)) (f : α → ENNReal) (hf : Measurable f) :
    (μ.withDensity (fun p => f p.1)).map Prod.fst =
      (μ.map Prod.fst).withDensity f := by
  ext B hB
  rw [Measure.map_apply measurable_fst hB,
    withDensity_apply _ (hB.preimage measurable_fst), withDensity_apply _ hB,
    setLIntegral_map hB hf measurable_fst]

/-- For [the specified mathematical inputs](hyp:ε,J,H,g,Prel,hMass,hOverlap,a,upper), [this definition](goal) introduces the corresponding object. -/
def endpointArmPotentialLaw {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) (upper : Bool) :
    Measure (ScoreSpace ε × OutcomeSpace) :=
  (endpointAssignedArmLaw H g Prel hMass hOverlap a upper).withDensity
    (fun p => (ENNReal.ofReal (armProb a p.1))⁻¹)

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,a,upper), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointArmPotentialLaw_fst {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) (upper : Bool) :
    (endpointArmPotentialLaw H g Prel hMass hOverlap a upper).fst = H := by
  let f : ScoreSpace ε → ENNReal :=
    fun e => ENNReal.ofReal (armProb a e)
  have hf : Measurable f := by
    cases a <;> simp [f, armProb] <;> fun_prop
  have hf0 : ∀ e : ScoreSpace ε, f e ≠ 0 := by
    intro e
    apply ne_of_gt
    rw [ENNReal.ofReal_pos]
    rcases e.property with ⟨he0, he1⟩
    cases a <;> simp [f, armProb] <;> linarith [hOverlap.1, hOverlap.2]
  have hft : ∀ e : ScoreSpace ε, f e ≠ ∞ := fun _ => ENNReal.ofReal_ne_top
  unfold endpointArmPotentialLaw Measure.fst
  change ((endpointAssignedArmLaw H g Prel hMass hOverlap a upper).withDensity
    (fun p => (f p.1)⁻¹)).map Prod.fst = H
  rw [map_withDensity_of_fst _ (fun e => (f e)⁻¹) hf.fun_inv]
  change ((endpointAssignedArmLaw H g Prel hMass hOverlap a upper).fst).withDensity
    (fun e => (f e)⁻¹) = H
  rw [endpointAssignedArmLaw_fst H g Prel hMass hOverlap a upper]
  change (H.withDensity f).withDensity (fun e => (f e)⁻¹) = H
  exact withDensity_inv_same hf
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hft)
/-- For [the specified mathematical inputs](hyp:ε,J,H,g,Prel,hMass,hOverlap,a,upper), [this definition](goal) introduces the corresponding object. -/
instance endpointArmPotentialLaw_isProbabilityMeasure {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) (upper : Bool) :
    IsProbabilityMeasure
      (endpointArmPotentialLaw H g Prel hMass hOverlap a upper) := by
  rw [isProbabilityMeasure_iff]
  have hfst := endpointArmPotentialLaw_fst H g Prel hMass hOverlap a upper
  calc
    endpointArmPotentialLaw H g Prel hMass hOverlap a upper Set.univ =
        (endpointArmPotentialLaw H g Prel hMass hOverlap a upper).fst Set.univ := by
      unfold Measure.fst
      rw [Measure.map_apply measurable_fst MeasurableSet.univ]
      simp
    _ = H Set.univ := congrArg (fun μ : Measure (ScoreSpace ε) => μ Set.univ) hfst
    _ = 1 := isProbabilityMeasure_iff.mp hMass.1

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,a,upper), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointArmPotentialLaw_retilt {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) (upper : Bool) :
    (endpointArmPotentialLaw H g Prel hMass hOverlap a upper).withDensity
        (fun p => ENNReal.ofReal (armProb a p.1)) =
      endpointAssignedArmLaw H g Prel hMass hOverlap a upper := by
  let f : ScoreSpace ε × OutcomeSpace → ENNReal :=
    fun p => ENNReal.ofReal (armProb a p.1)
  have hf : Measurable f := by
    cases a <;> simp [f, armProb] <;> fun_prop
  have hf0 : ∀ p : ScoreSpace ε × OutcomeSpace, f p ≠ 0 := by
    intro p
    apply ne_of_gt
    rw [ENNReal.ofReal_pos]
    rcases p.1.property with ⟨he0, he1⟩
    cases a <;> simp [f, armProb] <;> linarith [hOverlap.1, hOverlap.2]
  unfold endpointArmPotentialLaw
  change ((endpointAssignedArmLaw H g Prel hMass hOverlap a upper).withDensity
      (fun p => (f p)⁻¹)).withDensity f = _
  rw [← withDensity_mul _ hf.fun_inv hf]
  have hfun : (fun p => (f p)⁻¹) * f = 1 := by
    funext p
    exact ENNReal.inv_mul_cancel (hf0 p) ENNReal.ofReal_ne_top
  rw [hfun, withDensity_one]

/-- For [the specified mathematical inputs](hyp:ε,J,H,g,Prel,hMass,hOverlap,upper0,upper1), [this definition](goal) introduces the corresponding object. -/
def endpointLatentLaw {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (upper0 upper1 : Bool) :
    Measure (ScoreSpace ε × (OutcomeSpace × OutcomeSpace)) :=
  glueAlongFst
    (endpointArmPotentialLaw H g Prel hMass hOverlap false upper0)
    (endpointArmPotentialLaw H g Prel hMass hOverlap true upper1)
/-- For [the specified mathematical inputs](hyp:ε,J,H,g,Prel,hMass,hOverlap,upper0,upper1), [this definition](goal) introduces the corresponding object. -/
instance endpointLatentLaw_isProbabilityMeasure {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (upper0 upper1 : Bool) :
    IsProbabilityMeasure
      (endpointLatentLaw H g Prel hMass hOverlap upper0 upper1) := by
  unfold endpointLatentLaw
  letI : IsProbabilityMeasure
      (endpointArmPotentialLaw H g Prel hMass hOverlap false upper0) :=
    endpointArmPotentialLaw_isProbabilityMeasure
      H g Prel hMass hOverlap false upper0
  letI : IsProbabilityMeasure
      (endpointArmPotentialLaw H g Prel hMass hOverlap true upper1) :=
    endpointArmPotentialLaw_isProbabilityMeasure
      H g Prel hMass hOverlap true upper1
  exact glueAlongFst_isProbabilityMeasure _ _
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,upper0,upper1), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointLatentLaw_map_control {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (upper0 upper1 : Bool) :
    (endpointLatentLaw H g Prel hMass hOverlap upper0 upper1).map
        (fun p => (p.1, p.2.1)) =
      endpointArmPotentialLaw H g Prel hMass hOverlap false upper0 := by
  unfold endpointLatentLaw
  exact glueAlongFst_map_left _ _
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,upper0,upper1), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointLatentLaw_map_treated {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (upper0 upper1 : Bool) :
    (endpointLatentLaw H g Prel hMass hOverlap upper0 upper1).map
        (fun p => (p.1, p.2.2)) =
      endpointArmPotentialLaw H g Prel hMass hOverlap true upper1 := by
  unfold endpointLatentLaw
  apply glueAlongFst_map_right
  rw [endpointArmPotentialLaw_fst, endpointArmPotentialLaw_fst]
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,upper0,upper1), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointLatentLaw_fst {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (upper0 upper1 : Bool) :
    (endpointLatentLaw H g Prel hMass hOverlap upper0 upper1).fst = H := by
  unfold Measure.fst
  calc
    (endpointLatentLaw H g Prel hMass hOverlap upper0 upper1).map Prod.fst =
        ((endpointLatentLaw H g Prel hMass hOverlap upper0 upper1).map
          (fun p => (p.1, p.2.1))).map Prod.fst := by
      rw [Measure.map_map measurable_fst (by fun_prop)]
      rfl
    _ = (endpointArmPotentialLaw H g Prel hMass hOverlap false upper0).map
        Prod.fst := by
      rw [endpointLatentLaw_map_control]
    _ = H := by
      change (endpointArmPotentialLaw H g Prel hMass hOverlap false upper0).fst = H
      exact endpointArmPotentialLaw_fst H g Prel hMass hOverlap false upper0

end
end CausalSmith.PartialID.UnlinkedPropensityAte

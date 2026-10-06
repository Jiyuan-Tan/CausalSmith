module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.FixedLawCoverage
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.FixedLawAttainment
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.CompatibilityReconstruction

/-! Reconstruction leaves for fixed-law endpoint attainment. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- For [the specified mathematical inputs](hyp:α,β,γ,G,w,hw,π), [this definition](goal) introduces the corresponding object. -/
def liftTransformCoupling {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [StandardBorelSpace α] [Nonempty α]
    [StandardBorelSpace β] [Nonempty β]
    [MeasurableSpace.CountablyGenerated γ]
    (G : Measure α) (w : α → γ) (hw : Measurable w)
    (π : Measure (β × γ)) [IsFiniteMeasure G] [IsFiniteMeasure π] :
    Measure (α × β) :=
  (glueAlongFst (π.map Prod.swap)
      (G.map (fun x => (w x, x)))).map
    (fun p => (p.2.2, p.2.1))
/-- For [the specified mathematical inputs](hyp:α,β,γ,G,w,hw,π), [this definition](goal) introduces the corresponding object. -/
instance liftTransformCoupling_isProbabilityMeasure {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [StandardBorelSpace α] [Nonempty α]
    [StandardBorelSpace β] [Nonempty β]
    [MeasurableSpace.CountablyGenerated γ]
    (G : Measure α) (w : α → γ) (hw : Measurable w)
    (π : Measure (β × γ)) [IsProbabilityMeasure G]
    [IsProbabilityMeasure π] :
    IsProbabilityMeasure (liftTransformCoupling G w hw π) := by
  unfold liftTransformCoupling
  letI : IsProbabilityMeasure (π.map Prod.swap) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure (G.map (fun x => (w x, x))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure
      (glueAlongFst (π.map Prod.swap) (G.map (fun x => (w x, x)))) :=
    glueAlongFst_isProbabilityMeasure _ _
  exact Measure.isProbabilityMeasure_map (by fun_prop)

private lemma reversedCoupling_fst {β γ : Type*}
    [MeasurableSpace β] [MeasurableSpace γ]
    (π : Measure (β × γ)) :
    (π.map Prod.swap).fst = π.map Prod.snd := by
  unfold Measure.fst
  rw [Measure.map_map measurable_fst (by fun_prop)]
  rfl

private lemma transformGraph_fst {α γ : Type*}
    [MeasurableSpace α] [MeasurableSpace γ]
    (G : Measure α) (w : α → γ) (hw : Measurable w) :
    (G.map (fun x => (w x, x))).fst = G.map w := by
  have hgraph : Measurable (fun x : α => (w x, x)) := by fun_prop
  unfold Measure.fst
  rw [Measure.map_map measurable_fst hgraph]
  rfl

/-- Given [the stated mathematical inputs and assumptions](hyp:α,β,γ,G,w,hw,π,htransform), this result [establishes the stated mathematical conclusion](goal). -/
lemma liftTransformCoupling_fst {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [StandardBorelSpace α] [Nonempty α]
    [StandardBorelSpace β] [Nonempty β]
    [MeasurableSpace.CountablyGenerated γ]
    (G : Measure α) (w : α → γ) (hw : Measurable w)
    (π : Measure (β × γ)) [IsProbabilityMeasure G]
    [IsProbabilityMeasure π]
    (htransform : π.map Prod.snd = G.map w) :
    (liftTransformCoupling G w hw π).fst = G := by
  let ρ0 : Measure (γ × β) := π.map Prod.swap
  let ρ1 : Measure (γ × α) := G.map (fun x => (w x, x))
  have hfst : ρ0.fst = ρ1.fst := by
    dsimp [ρ0, ρ1]
    rw [reversedCoupling_fst, transformGraph_fst G w hw, htransform]
  unfold liftTransformCoupling Measure.fst
  calc
    (Measure.map (fun p => (p.2.2, p.2.1))
        (glueAlongFst ρ0 ρ1)).map Prod.fst =
        ((glueAlongFst ρ0 ρ1).map
          (fun p => (p.1, p.2.2))).map Prod.snd := by
          rw [Measure.map_map measurable_fst (by fun_prop),
            Measure.map_map measurable_snd (by fun_prop)]
          rfl
    _ = ρ1.map Prod.snd := by rw [glueAlongFst_map_right ρ0 ρ1 hfst]
    _ = G := by
      dsimp [ρ1]
      rw [Measure.map_map measurable_snd (by fun_prop)]
      change Measure.map id G = G
      exact Measure.map_id

/-- Given [the stated mathematical inputs and assumptions](hyp:α,β,γ,G,w,hw,π,htransform), this result [establishes the stated mathematical conclusion](goal). -/
lemma liftTransformCoupling_map_outcome_transform {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [StandardBorelSpace α] [Nonempty α]
    [StandardBorelSpace β] [Nonempty β]
    [MeasurableSpace.CountablyGenerated γ] [MeasurableEq γ]
    (G : Measure α) (w : α → γ) (hw : Measurable w)
    (π : Measure (β × γ)) [IsProbabilityMeasure G]
    [IsProbabilityMeasure π]
    (htransform : π.map Prod.snd = G.map w) :
    (liftTransformCoupling G w hw π).map (fun p => (p.2, w p.1)) = π := by
  let ρ0 : Measure (γ × β) := π.map Prod.swap
  let ρ1 : Measure (γ × α) := G.map (fun x => (w x, x))
  let L : Measure (γ × (β × α)) := glueAlongFst ρ0 ρ1
  have hfst : ρ0.fst = ρ1.fst := by
    dsimp [ρ0, ρ1]
    rw [reversedCoupling_fst, transformGraph_fst G w hw, htransform]
  have hright : L.map (fun p => (p.1, p.2.2)) = ρ1 := by
    exact glueAlongFst_map_right ρ0 ρ1 hfst
  let S : Set (γ × α) := {q | q.1 = w q.2}
  have hS : MeasurableSet S :=
    measurableSet_eq_fun measurable_fst (hw.comp measurable_snd)
  have hSc : MeasurableSet {q : γ × α | q ∉ S} := hS.compl
  have hgraphMap : Measurable (fun x : α => (w x, x)) := by fun_prop
  have hrightMap : Measurable
      (fun p : γ × (β × α) => (p.1, p.2.2)) := by fun_prop
  have hgraphρ1 : ∀ᵐ q ∂ρ1, q ∈ S := by
    rw [ae_iff]
    dsimp [ρ1]
    rw [Measure.map_apply hgraphMap hSc]
    have hpre : (fun x : α => (w x, x)) ⁻¹' {q | q ∉ S} = ∅ := by
      ext x
      simp [S]
    rw [hpre, measure_empty]
  have hgraphLS : ∀ᵐ p ∂L, (p.1, p.2.2) ∈ S := by
    rw [← hright] at hgraphρ1
    rw [ae_iff] at hgraphρ1 ⊢
    rw [Measure.map_apply hrightMap hSc] at hgraphρ1
    exact hgraphρ1
  have hgraphL : ∀ᵐ p ∂L, p.1 = w p.2.2 := by
    filter_upwards [hgraphLS] with p hp
    exact hp
  have hleft : L.map (fun p => (p.1, p.2.1)) = ρ0 :=
    glueAlongFst_map_left ρ0 ρ1
  unfold liftTransformCoupling
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  calc
    L.map ((fun q : α × β => (q.2, w q.1)) ∘
        (fun p : γ × (β × α) => (p.2.2, p.2.1))) =
        L.map (fun p => (p.2.1, p.1)) := by
      apply Measure.map_congr
      filter_upwards [hgraphL] with p hp
      simp only [Function.comp_apply]
      rw [hp]
    _ = (L.map (fun p => (p.1, p.2.1))).map Prod.swap := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = ρ0.map Prod.swap := by rw [hleft]
    _ = π := by
      dsimp [ρ0]
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      change Measure.map id π = π
      exact Measure.map_id

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hg,hOverlap,a,r,hq), this result [establishes the stated mathematical conclusion](goal). -/
lemma armCellScoreLaw_isProbabilityMeasure {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (g : ScoreSpace ε → LabelSpace J) (hg : Measurable g)
    (hOverlap : Overlap ε) (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) :
    IsProbabilityMeasure (armCellScoreLaw H inferInstance g hg a r hq) := by
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
  rw [isProbabilityMeasure_iff]
  unfold armCellScoreLaw
  rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, smul_eq_mul]
  have hfinite :
      (H.withDensity (fun e => ENNReal.ofReal (armProb a e))) (cell g r) ≠ ∞ :=
    measure_ne_top _ _
  have hmeasure :
      (H.withDensity (fun e => ENNReal.ofReal (armProb a e))) (cell g r) =
        ENNReal.ofReal (armCellMass H g a r) := by
    rw [← propensityTilt_real_cell H g hg hOverlap a r]
    exact (ENNReal.ofReal_toReal hfinite).symm
  rw [hmeasure, ENNReal.inv_mul_cancel]
  · exact ne_of_gt (ENNReal.ofReal_pos.mpr hq)
  · exact ENNReal.ofReal_ne_top

/-- For [the specified mathematical inputs](hyp:ε,J,H,g,Prel,hMass,hOverlap,a,r,hq,upper), [this definition](goal) introduces the corresponding object. -/
def endpointCellScoreOutcomeLaw {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) (upper : Bool) :
    Measure (ScoreSpace ε × ℝ) := by
  letI : IsProbabilityMeasure H := hMass.1
  letI : IsProbabilityMeasure Prel := hMass.2.1
  letI : Nonempty (ScoreSpace ε) := ⟨⟨1 / 2, by
    constructor <;> linarith [hOverlap.1, hOverlap.2]⟩⟩
  let Y := armCellOutcomeLaw Prel hMass.2.1 a r
    (by rw [hMass.2.2.2 a r]; exact hq)
  let G := armCellScoreLaw H hMass.1 g hMass.2.2.1 a r hq
  let W := armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq
  letI : IsProbabilityMeasure Y :=
    armCellOutcomeLaw_isProbabilityMeasure Prel a r
      (by rw [hMass.2.2.2 a r]; exact hq)
  letI : IsProbabilityMeasure G :=
    armCellScoreLaw_isProbabilityMeasure H g hMass.2.2.1 hOverlap a r hq
  letI : IsProbabilityMeasure W := by
    dsimp [W, armCellWeightLaw]
    exact Measure.isProbabilityMeasure_map (by
      cases a <;> simp [armProb] <;> fun_prop)
  let π : Measure (ℝ × ℝ) :=
    if upper then Causalean.Stat.comonotoneCoupling Y W
    else Causalean.Stat.countermonotoneCoupling Y W
  letI : IsProbabilityMeasure π := by
    dsimp [π]
    split_ifs
    · exact (Causalean.Stat.isCoupling_comonotoneCoupling Y W).isProbabilityMeasure
    · exact (Causalean.Stat.isCoupling_countermonotoneCoupling Y W).isProbabilityMeasure
  exact liftTransformCoupling G (fun e => (armProb a e)⁻¹) (by
    cases a <;> simp [armProb] <;> fun_prop) π
/-- For [the specified mathematical inputs](hyp:ε,J,H,g,Prel,hMass,hOverlap,a,r,hq,upper), [this definition](goal) introduces the corresponding object. -/
instance endpointCellScoreOutcomeLaw_isProbabilityMeasure {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) (upper : Bool) :
    IsProbabilityMeasure
      (endpointCellScoreOutcomeLaw H g Prel hMass hOverlap a r hq upper) := by
  letI : IsProbabilityMeasure H := hMass.1
  letI : IsProbabilityMeasure Prel := hMass.2.1
  letI : Nonempty (ScoreSpace ε) := ⟨⟨1 / 2, by
    constructor <;> linarith [hOverlap.1, hOverlap.2]⟩⟩
  let Y := armCellOutcomeLaw Prel hMass.2.1 a r
    (by rw [hMass.2.2.2 a r]; exact hq)
  let G := armCellScoreLaw H hMass.1 g hMass.2.2.1 a r hq
  let W := armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq
  let π : Measure (ℝ × ℝ) :=
    if upper then Causalean.Stat.comonotoneCoupling Y W
    else Causalean.Stat.countermonotoneCoupling Y W
  letI : IsProbabilityMeasure Y :=
    armCellOutcomeLaw_isProbabilityMeasure Prel a r
      (by rw [hMass.2.2.2 a r]; exact hq)
  letI : IsProbabilityMeasure G :=
    armCellScoreLaw_isProbabilityMeasure H g hMass.2.2.1 hOverlap a r hq
  letI : IsProbabilityMeasure W := by
    dsimp [W, armCellWeightLaw]
    exact Measure.isProbabilityMeasure_map (by
      cases a <;> simp [armProb] <;> fun_prop)
  letI : IsProbabilityMeasure π := by
    dsimp [π]
    split_ifs
    · exact (Causalean.Stat.isCoupling_comonotoneCoupling Y W).isProbabilityMeasure
    · exact (Causalean.Stat.isCoupling_countermonotoneCoupling Y W).isProbabilityMeasure
  have hw : Measurable (fun e : ScoreSpace ε => (armProb a e)⁻¹) := by
    cases a <;> simp [armProb] <;> fun_prop
  change IsProbabilityMeasure (liftTransformCoupling G
    (fun e => (armProb a e)⁻¹) hw π)
  infer_instance
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,a,r,hq,upper), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointCoupling_isCoupling {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) (upper : Bool) :
    let Y := armCellOutcomeLaw Prel hMass.2.1 a r
      (by rw [hMass.2.2.2 a r]; exact hq)
    let W := armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq
    Causalean.Stat.IsCoupling
      (if upper then Causalean.Stat.comonotoneCoupling Y W
        else Causalean.Stat.countermonotoneCoupling Y W) Y W := by
  dsimp
  letI : IsProbabilityMeasure H := hMass.1
  letI : IsProbabilityMeasure Prel := hMass.2.1
  letI : IsProbabilityMeasure
      (armCellOutcomeLaw Prel hMass.2.1 a r
        (by rw [hMass.2.2.2 a r]; exact hq)) :=
    armCellOutcomeLaw_isProbabilityMeasure Prel a r
      (by rw [hMass.2.2.2 a r]; exact hq)
  letI : IsProbabilityMeasure
      (armCellScoreLaw H hMass.1 g hMass.2.2.1 a r hq) :=
    armCellScoreLaw_isProbabilityMeasure H g hMass.2.2.1 hOverlap a r hq
  letI : IsProbabilityMeasure
      (armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq) := by
    unfold armCellWeightLaw
    exact Measure.isProbabilityMeasure_map (by
      cases a <;> simp [armProb] <;> fun_prop)
  cases upper
  · exact Causalean.Stat.isCoupling_countermonotoneCoupling _ _
  · exact Causalean.Stat.isCoupling_comonotoneCoupling _ _

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,a,r,hq,upper), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointCellScoreOutcomeLaw_fst {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) (upper : Bool) :
    (endpointCellScoreOutcomeLaw H g Prel hMass hOverlap a r hq upper).fst =
      armCellScoreLaw H hMass.1 g hMass.2.2.1 a r hq := by
  letI : IsProbabilityMeasure H := hMass.1
  letI : IsProbabilityMeasure Prel := hMass.2.1
  letI : Nonempty (ScoreSpace ε) := ⟨⟨1 / 2, by
    constructor <;> linarith [hOverlap.1, hOverlap.2]⟩⟩
  let Y := armCellOutcomeLaw Prel hMass.2.1 a r
    (by rw [hMass.2.2.2 a r]; exact hq)
  let G := armCellScoreLaw H hMass.1 g hMass.2.2.1 a r hq
  let W := armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq
  let π : Measure (ℝ × ℝ) :=
    if upper then Causalean.Stat.comonotoneCoupling Y W
    else Causalean.Stat.countermonotoneCoupling Y W
  letI : IsProbabilityMeasure Y :=
    armCellOutcomeLaw_isProbabilityMeasure Prel a r
      (by rw [hMass.2.2.2 a r]; exact hq)
  letI : IsProbabilityMeasure G :=
    armCellScoreLaw_isProbabilityMeasure H g hMass.2.2.1 hOverlap a r hq
  letI : IsProbabilityMeasure W := by
    dsimp [W, armCellWeightLaw]
    exact Measure.isProbabilityMeasure_map (by
      cases a <;> simp [armProb] <;> fun_prop)
  have hπ : Causalean.Stat.IsCoupling π Y W := by
    simpa [π, Y, W] using
      endpointCoupling_isCoupling H g Prel hMass hOverlap a r hq upper
  letI : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  have hw : Measurable (fun e : ScoreSpace ε => (armProb a e)⁻¹) := by
    cases a <;> simp [armProb] <;> fun_prop
  have htransform : π.map Prod.snd = G.map
      (fun e : ScoreSpace ε => (armProb a e)⁻¹) := by
    rw [hπ.map_snd]
    rfl
  change (liftTransformCoupling G
    (fun e : ScoreSpace ε => (armProb a e)⁻¹) hw π).fst = G
  exact liftTransformCoupling_fst G _ hw π htransform

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,a,r,hq,upper), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointCellScoreOutcomeLaw_map_outcome_weight {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) (upper : Bool) :
    (endpointCellScoreOutcomeLaw H g Prel hMass hOverlap a r hq upper).map
        (fun p => (p.2, (armProb a p.1)⁻¹)) =
      (if upper then
        Causalean.Stat.comonotoneCoupling
          (armCellOutcomeLaw Prel hMass.2.1 a r
            (by rw [hMass.2.2.2 a r]; exact hq))
          (armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq)
       else
        Causalean.Stat.countermonotoneCoupling
          (armCellOutcomeLaw Prel hMass.2.1 a r
            (by rw [hMass.2.2.2 a r]; exact hq))
          (armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq)) := by
  letI : IsProbabilityMeasure H := hMass.1
  letI : IsProbabilityMeasure Prel := hMass.2.1
  letI : Nonempty (ScoreSpace ε) := ⟨⟨1 / 2, by
    constructor <;> linarith [hOverlap.1, hOverlap.2]⟩⟩
  let Y := armCellOutcomeLaw Prel hMass.2.1 a r
    (by rw [hMass.2.2.2 a r]; exact hq)
  let G := armCellScoreLaw H hMass.1 g hMass.2.2.1 a r hq
  let W := armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq
  let π : Measure (ℝ × ℝ) :=
    if upper then Causalean.Stat.comonotoneCoupling Y W
    else Causalean.Stat.countermonotoneCoupling Y W
  letI : IsProbabilityMeasure Y :=
    armCellOutcomeLaw_isProbabilityMeasure Prel a r
      (by rw [hMass.2.2.2 a r]; exact hq)
  letI : IsProbabilityMeasure G :=
    armCellScoreLaw_isProbabilityMeasure H g hMass.2.2.1 hOverlap a r hq
  letI : IsProbabilityMeasure W := by
    dsimp [W, armCellWeightLaw]
    exact Measure.isProbabilityMeasure_map (by
      cases a <;> simp [armProb] <;> fun_prop)
  have hπ : Causalean.Stat.IsCoupling π Y W := by
    simpa [π, Y, W] using
      endpointCoupling_isCoupling H g Prel hMass hOverlap a r hq upper
  letI : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  have hw : Measurable (fun e : ScoreSpace ε => (armProb a e)⁻¹) := by
    cases a <;> simp [armProb] <;> fun_prop
  have htransform : π.map Prod.snd = G.map
      (fun e : ScoreSpace ε => (armProb a e)⁻¹) := by
    rw [hπ.map_snd]
    rfl
  change (liftTransformCoupling G
    (fun e : ScoreSpace ε => (armProb a e)⁻¹) hw π).map
      (fun p => (p.2, (armProb a p.1)⁻¹)) = π
  exact liftTransformCoupling_map_outcome_transform G _ hw π htransform

end
end CausalSmith.PartialID.UnlinkedPropensityAte

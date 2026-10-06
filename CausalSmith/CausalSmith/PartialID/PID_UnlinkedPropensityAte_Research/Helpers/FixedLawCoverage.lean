module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.FixedLawCellCoupling
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionCellTransport

/-! Membership of a compatible law's ATE in the population interval. -/

public section

open MeasureTheory Set
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

private lemma inverseArmProb_mem_Icc {ε : ℝ} (hOverlap : Overlap ε)
    (a : ArmSpace) (e : ScoreSpace ε) :
    (armProb a e)⁻¹ ∈ Icc 0 ε⁻¹ := by
  have hb := projectionArmProb_bounds hOverlap a e
  have hp : 0 < armProb a e := lt_of_lt_of_le hOverlap.1 hb.1
  exact ⟨(inv_pos.mpr hp).le, (inv_le_inv₀ hp hOverlap.1).2 hb.1⟩

private lemma assignedProduct_integrable {ε : ℝ} {J : ℕ}
    (P : Measure (FullRow ε J)) [IsProbabilityMeasure P]
    (hOverlap : Overlap ε) (a : ArmSpace) :
    Integrable (fun ω : FullRow ε J =>
      ((if a then outcome1 ω else outcome0 ω : OutcomeSpace) : ℝ) *
        (armProb a (score ω))⁻¹) P := by
  have hmeas : Measurable (fun ω : FullRow ε J =>
      ((if a then outcome1 ω else outcome0 ω : OutcomeSpace) : ℝ) *
        (armProb a (score ω))⁻¹) := by
    cases a <;> simp [armProb, outcome0, outcome1, score] <;> fun_prop
  apply Integrable.of_bound hmeas.aestronglyMeasurable ε⁻¹
  filter_upwards [] with ω
  have hy : ((if a then outcome1 ω else outcome0 ω : OutcomeSpace) : ℝ) ∈ Icc 0 1 :=
    (if a then outcome1 ω else outcome0 ω).property
  have hw := inverseArmProb_mem_Icc hOverlap a (score ω)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hy.1 hw.1)]
  calc
    ((if a then outcome1 ω else outcome0 ω : OutcomeSpace) : ℝ) *
        (armProb a (score ω))⁻¹ ≤ 1 * (armProb a (score ω))⁻¹ :=
      mul_le_mul_of_nonneg_right hy.2 hw.1
    _ = (armProb a (score ω))⁻¹ := one_mul _
    _ ≤ ε⁻¹ := hw.2

private lemma assignedProduct_integral_eq_sum_cells {ε : ℝ} {J : ℕ}
    (P : Measure (FullRow ε J)) [IsProbabilityMeasure P]
    (g : ScoreSpace ε → LabelSpace J) (hg : Measurable g)
    (hOverlap : Overlap ε) (a : ArmSpace) :
    (∫ ω in {ω | arm ω = a},
      ((if a then outcome1 ω else outcome0 ω : OutcomeSpace) : ℝ) *
        (armProb a (score ω))⁻¹ ∂P) =
      ∑ r : LabelSpace J, ∫ ω in {ω | arm ω = a ∧ g (score ω) = r},
        ((if a then outcome1 ω else outcome0 ω : OutcomeSpace) : ℝ) *
          (armProb a (score ω))⁻¹ ∂P := by
  let S : LabelSpace J → Set (FullRow ε J) :=
    fun r => {ω | arm ω = a ∧ g (score ω) = r}
  have hS : ∀ r, MeasurableSet (S r) := by
    intro r
    exact (measurableSet_eq_fun (by unfold arm; fun_prop) measurable_const).inter
      (measurableSet_eq_fun (hg.comp (by unfold score; fun_prop)) measurable_const)
  have hd : Pairwise (fun r s => Disjoint (S r) (S s)) := by
    intro r s hrs
    apply Set.disjoint_left.mpr
    intro ω hr hs
    exact hrs (hr.2.symm.trans hs.2)
  have hc : (⋃ r, S r) = {ω | arm ω = a} := by
    ext ω
    simp [S]
  have hfi := assignedProduct_integrable P hOverlap a
  have hsum := integral_iUnion_fintype hS hd (fun r => hfi.integrableOn)
    (f := fun ω : FullRow ε J =>
      ((if a then outcome1 ω else outcome0 ω : OutcomeSpace) : ℝ) *
        (armProb a (score ω))⁻¹) (μ := P)
  simpa [hc, S] using hsum

private lemma assignedProduct_cell_eq_mass_mul_coupling {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (P : Measure (FullRow ε J)) (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) :
    (∫ ω in {ω | arm ω = a ∧ g (score ω) = r},
      ((if a then outcome1 ω else outcome0 ω : OutcomeSpace) : ℝ) *
        (armProb a (score ω))⁻¹ ∂P) =
      armCellMass H g a r *
        ∫ p, p.1 * p.2 ∂(compatibleArmCellCoupling H g P a r hq) := by
  have hpair : Measurable (fun ω : FullRow ε J =>
      (((if a then outcome1 ω else outcome0 ω : OutcomeSpace) : ℝ),
        (armProb a (score ω))⁻¹)) := by
    cases a <;> simp [armProb, outcome0, outcome1, score] <;> fun_prop
  have hprod : AEStronglyMeasurable (fun p : ℝ × ℝ => p.1 * p.2)
      ((P.restrict {ω | arm ω = a ∧ g (score ω) = r}).map
        (fun ω =>
          (((if a then outcome1 ω else outcome0 ω : OutcomeSpace) : ℝ),
            (armProb a (score ω))⁻¹))) := by fun_prop
  unfold compatibleArmCellCoupling
  rw [integral_smul_measure, integral_map hpair.aemeasurable hprod]
  simp only [smul_eq_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hq.le]
  rw [← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul]

private lemma assignedProduct_cell_eq_zero {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (P : Measure (FullRow ε J))
    (hP : CompatibleCausalLaw H g Prel P)
    (hMass : CompatibleCellMasses H g Prel)
    (a : ArmSpace) (r : LabelSpace J)
    (hq : ¬ 0 < armCellMass H g a r) :
    (∫ ω in {ω | arm ω = a ∧ g (score ω) = r},
      ((if a then outcome1 ω else outcome0 ω : OutcomeSpace) : ℝ) *
        (armProb a (score ω))⁻¹ ∂P) = 0 := by
  letI : IsProbabilityMeasure P := hP.probability
  let S : Set (FullRow ε J) := {ω | arm ω = a ∧ g (score ω) = r}
  have hqzero : armCellMass H g a r = 0 := by
    have hreal := compatible_assignedArmCell_measureReal H g Prel P hP hMass a r
    exact le_antisymm (le_of_not_gt hq) (hreal ▸ measureReal_nonneg)
  have hS : P S = 0 := by
    have hreal := compatible_assignedArmCell_measureReal H g Prel P hP hMass a r
    have hfinite : P S ≠ ⊤ := measure_ne_top P S
    have hrealzero : P.real S = 0 := by simpa [S, hqzero] using hreal
    calc
      P S = ENNReal.ofReal (P.real S) := (ENNReal.ofReal_toReal hfinite).symm
      _ = 0 := by rw [hrealzero]; simp
  have hzero : P.restrict S = 0 := Measure.restrict_zero_set hS
  simpa only [S, hzero, integral_zero_measure]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,P,hP,hMass,hOverlap,a), this result [establishes the stated mathematical conclusion](goal). -/
lemma compatible_armMean_eq_sum_cellCouplings {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (P : Measure (FullRow ε J))
    (hP : CompatibleCausalLaw H g Prel P)
    (hMass : CompatibleCellMasses H g Prel) (hOverlap : Overlap ε)
    (a : ArmSpace) :
    (∫ ω, ((if a then outcome1 ω else outcome0 ω : OutcomeSpace) : ℝ) ∂P) =
      ∑ r : LabelSpace J,
        if hq : 0 < armCellMass H g a r then
          armCellMass H g a r *
            ∫ p, p.1 * p.2 ∂(compatibleArmCellCoupling H g P a r hq)
        else 0 := by
  letI : IsProbabilityMeasure P := hP.probability
  rw [potentialOutcomeMean_eq_inversePropensity P hOverlap hP.randomizedAssignment a]
  rw [assignedProduct_integral_eq_sum_cells P g hMass.2.2.1 hOverlap a]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hq : 0 < armCellMass H g a r
  · simp only [hq, dif_pos]
    exact assignedProduct_cell_eq_mass_mul_coupling H g P a r hq
  · simp only [hq, dif_neg]
    exact assignedProduct_cell_eq_zero H g Prel P hP hMass a r hq

private lemma memLp_id_of_support_Icc (μ : Measure ℝ) [IsFiniteMeasure μ]
    (b : ℝ) (h : μ (Icc 0 b)ᶜ = 0) : MemLp (fun x : ℝ => x) 2 μ := by
  apply memLp_of_bounded
  · rw [ae_iff]
    exact h
  · fun_prop

private lemma compatibleArmCell_moments {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (P : Measure (FullRow ε J))
    (hP : CompatibleCausalLaw H g Prel P)
    (hMass : CompatibleCellMasses H g Prel) (hOverlap : Overlap ε)
    (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) :
    MemLp (fun x : ℝ => x) 2
      (armCellOutcomeLaw Prel hMass.2.1 a r
        (by rw [hMass.2.2.2 a r]; exact hq)) ∧
    MemLp (fun x : ℝ => x) 2
      (armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq) := by
  let Y := armCellOutcomeLaw Prel hMass.2.1 a r
    (by rw [hMass.2.2.2 a r]; exact hq)
  let W := armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq
  have hπ := compatibleArmCellCoupling_isCoupling H g Prel P hP hMass hOverlap a r hq
  letI : IsProbabilityMeasure (compatibleArmCellCoupling H g P a r hq) :=
    hπ.isProbabilityMeasure
  letI : IsProbabilityMeasure Y := by
    rw [show Y = (compatibleArmCellCoupling H g P a r hq).map Prod.fst from
      hπ.map_fst.symm]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure W := by
    rw [show W = (compatibleArmCellCoupling H g P a r hq).map Prod.snd from
      hπ.map_snd.symm]
    exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hYsup : Y (Icc 0 1)ᶜ = 0 := by
    dsimp [Y, armCellOutcomeLaw]
    rw [Measure.map_apply (by fun_prop) measurableSet_Icc.compl]
    have hpre : (fun z : Observation J => (z.2.2 : ℝ)) ⁻¹' (Icc 0 1)ᶜ = ∅ := by
      ext z
      exact iff_false_intro (fun hz => hz z.2.2.property)
    rw [hpre]
    simp
  have hWsup : W (Icc 0 ε⁻¹)ᶜ = 0 := by
    dsimp [W, armCellWeightLaw]
    rw [Measure.map_apply (measurable_inverseArmProb a) measurableSet_Icc.compl]
    have hpre : (fun e : ScoreSpace ε => (armProb a e)⁻¹) ⁻¹'
        (Icc 0 ε⁻¹)ᶜ = ∅ := by
      ext e
      exact iff_false_intro (fun he => he (inverseArmProb_mem_Icc hOverlap a e))
    rw [hpre]
    simp
  exact ⟨memLp_id_of_support_Icc Y 1 hYsup,
    memLp_id_of_support_Icc W ε⁻¹ hWsup⟩

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,P,hP,hMass,hOverlap,a), this result [establishes the stated mathematical conclusion](goal). -/
lemma compatible_armMean_mem_endpoints {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (P : Measure (FullRow ε J))
    (hP : CompatibleCausalLaw H g Prel P)
    (hMass : CompatibleCellMasses H g Prel) (hOverlap : Overlap ε)
    (a : ArmSpace) :
    (∫ ω, ((if a then outcome1 ω else outcome0 ω : OutcomeSpace) : ℝ) ∂P) ∈
      Icc (muLower H g Prel hMass a) (muUpper H g Prel hMass a) := by
  let π : ∀ r : LabelSpace J, 0 < armCellMass H g a r → Measure (ℝ × ℝ) :=
    fun r hq => compatibleArmCellCoupling H g P a r hq
  apply armMean_mem_endpoints_of_cellCouplings H g Prel hMass a π
  · intro r hq
    exact compatibleArmCellCoupling_isCoupling H g Prel P hP hMass hOverlap a r hq
  · intro r hq
    exact (compatibleArmCell_moments H g Prel P hP hMass hOverlap a r hq).1
  · intro r hq
    exact (compatibleArmCell_moments H g Prel P hP hMass hOverlap a r hq).2
  · exact compatible_armMean_eq_sum_cellCouplings H g Prel P hP hMass hOverlap a

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,P,hP,hOverlap), this result [establishes the stated mathematical conclusion](goal). -/
lemma compatible_ate_mem_sharpATESet {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (P : Measure (FullRow ε J))
    (hP : CompatibleCausalLaw H g Prel P)
    (hOverlap : Overlap ε) :
    ate P ∈ sharpATESet H g Prel
      (compatibleCellMasses_of_compatibleCausalLaw H g Prel P hP) := by
  let hMass := compatibleCellMasses_of_compatibleCausalLaw H g Prel P hP
  letI : IsProbabilityMeasure P := hP.probability
  apply ate_mem_sharpATESet_of_armMean_bounds H g Prel hMass P
  · intro a
    exact (compatible_armMean_mem_endpoints H g Prel P hP hMass hOverlap a).1
  · intro a
    exact (compatible_armMean_mem_endpoints H g Prel P hP hMass hOverlap a).2

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hOverlap,hcomp,P,hP), this result [establishes the stated mathematical conclusion](goal). -/
lemma compatibleLaw_ate_mem_sharpATESet {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J))
    (hOverlap : Overlap ε)
    (hcomp : (CompatibleLaws H g Prel).Nonempty)
    (P : Measure (FullRow ε J))
    (hP : P ∈ CompatibleLaws H g Prel) :
    ate P ∈ sharpATESet H g Prel
      (compatibleCellMasses_of_nonempty H g Prel hcomp) := by
  simpa using compatible_ate_mem_sharpATESet H g Prel P hP.2 hOverlap

end
end CausalSmith.PartialID.UnlinkedPropensityAte

module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.TCompatibility
public import Causalean.Stat.Coupling.Monotone.ProductLoss.Optimality

/-!
One-sided membership lemmas for the fixed-released-law sharp ATE interval.

This file isolates the algebraic passage from armwise potential-outcome mean
bounds to membership of the ATE in the candidate sharp interval.  It also
records the quantile formulas needed when the arm-cell law has been exhibited
as a coupling of the released outcome law and the inverse-score law.
-/

@[expose] public section

open MeasureTheory Set
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,P,a), this result [establishes the stated mathematical conclusion](goal). -/
lemma potentialOutcome_integrable {ε : ℝ} {J : ℕ}
    (P : Measure (FullRow ε J)) [IsProbabilityMeasure P] (a : ArmSpace) :
    Integrable
      (fun ω => ((if a then outcome1 ω else outcome0 ω : OutcomeSpace) : ℝ)) P := by
  cases a with
  | false =>
      change Integrable (fun ω => ((outcome0 ω : OutcomeSpace) : ℝ)) P
      apply Integrable.of_bound
        (by unfold outcome0; fun_prop) 1
      filter_upwards [] with ω
      exact abs_le.mpr ⟨by linarith [((outcome0 ω).property).1],
        ((outcome0 ω).property).2⟩
  | true =>
      change Integrable (fun ω => ((outcome1 ω : OutcomeSpace) : ℝ)) P
      apply Integrable.of_bound
        (by unfold outcome1; fun_prop) 1
      filter_upwards [] with ω
      exact abs_le.mpr ⟨by linarith [((outcome1 ω).property).1],
        ((outcome1 ω).property).2⟩

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,P), this result [establishes the stated mathematical conclusion](goal). -/
lemma ate_eq_potentialOutcomeMeans_sub {ε : ℝ} {J : ℕ}
    (P : Measure (FullRow ε J)) [IsProbabilityMeasure P] :
    ate P =
      (∫ ω, ((outcome1 ω : OutcomeSpace) : ℝ) ∂P) -
        ∫ ω, ((outcome0 ω : OutcomeSpace) : ℝ) ∂P := by
  unfold ate
  have h₁ : Integrable (fun ω => ((outcome1 ω : OutcomeSpace) : ℝ)) P := by
    simpa using potentialOutcome_integrable P true
  have h₀ : Integrable (fun ω => ((outcome0 ω : OutcomeSpace) : ℝ)) P := by
    simpa using potentialOutcome_integrable P false
  exact integral_sub h₁ h₀

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,P,hLower,hUpper), this result [establishes the stated mathematical conclusion](goal). -/
lemma ate_mem_sharpATESet_of_armMean_bounds {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (P : Measure (FullRow ε J)) [IsProbabilityMeasure P]
    (hLower : ∀ a : ArmSpace,
      muLower H g Prel hMass a ≤
        ∫ ω, ((if a then outcome1 ω else outcome0 ω : OutcomeSpace) : ℝ) ∂P)
    (hUpper : ∀ a : ArmSpace,
      (∫ ω, ((if a then outcome1 ω else outcome0 ω : OutcomeSpace) : ℝ) ∂P) ≤
        muUpper H g Prel hMass a) :
    ate P ∈ sharpATESet H g Prel hMass := by
  rw [ate_eq_potentialOutcomeMeans_sub P]
  unfold sharpATESet
  constructor
  · have h₁ := hLower true
    have h₀ := hUpper false
    simp at h₁ h₀
    linarith
  · have h₁ := hUpper true
    have h₀ := hLower false
    simp at h₁ h₀
    linarith

/-- For [the specified mathematical inputs](hyp:ε,J,ω), [this definition](goal) introduces the corresponding object. -/
def latentTriple {ε : ℝ} {J : ℕ} (ω : FullRow ε J) :
    ScoreSpace ε × OutcomeSpace × OutcomeSpace :=
  (score ω, outcome0 ω, outcome1 ω)

/-- For [the specified mathematical inputs](hyp:ε,J,P,a), [this definition](goal) introduces the corresponding object. -/
def assignedLatentLaw {ε : ℝ} {J : ℕ} (P : Measure (FullRow ε J))
    (a : ArmSpace) : Measure (ScoreSpace ε × OutcomeSpace × OutcomeSpace) :=
  (P.restrict {ω | arm ω = a}).map latentTriple

/-- For [the specified mathematical inputs](hyp:ε,J,P,a), [this definition](goal) introduces the corresponding object. -/
def propensityTiltedLatentLaw {ε : ℝ} {J : ℕ}
    (P : Measure (FullRow ε J)) (a : ArmSpace) :
    Measure (ScoreSpace ε × OutcomeSpace × OutcomeSpace) :=
  (P.map latentTriple).withDensity
    (fun x => ENNReal.ofReal (armProb a x.1))

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,P,hRandom,B,hB), this result [establishes the stated mathematical conclusion](goal). -/
lemma randomizedAssignment_false_measureReal
    {ε : ℝ} {J : ℕ} (P : Measure (FullRow ε J)) [IsProbabilityMeasure P]
    (hRandom : RandomizedAssignment P)
    (B : Set (ScoreSpace ε × OutcomeSpace × OutcomeSpace))
    (hB : MeasurableSet B) :
    P.real {ω | arm ω = false ∧ latentTriple ω ∈ B} =
      ∫ x in B, (1 - (x.1 : ℝ)) ∂(P.map latentTriple) := by
  have hX : Measurable (latentTriple (ε := ε) (J := J)) := by
    unfold latentTriple score outcome0 outcome1
    fun_prop
  let C : Set (FullRow ε J) := latentTriple ⁻¹' B
  let T : Set (FullRow ε J) := {ω | arm ω = true}
  have hT : MeasurableSet T := by
    dsimp [T]
    exact measurableSet_eq_fun (by unfold arm; fun_prop) measurable_const
  have hsplit := measureReal_inter_add_sdiff (μ := P) (s := C) (t := T) hT
  have htreated : P.real (C ∩ T) =
      ∫ x in B, (x.1 : ℝ) ∂(P.map latentTriple) := by
    rw [MeasureTheory.setIntegral_map hB (by fun_prop) hX.aemeasurable]
    convert hRandom B hB using 1
    · apply measureReal_congr
      filter_upwards [] with ω
      change (latentTriple ω ∈ B ∧ arm ω = true) =
        (arm ω = true ∧ latentTriple ω ∈ B)
      exact propext and_comm
    · apply setIntegral_congr_set
      filter_upwards [] with ω
      rfl
  have hC : P.real C = ∫ _x in B, (1 : ℝ) ∂(P.map latentTriple) := by
    rw [MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul, mul_one]
    change (P C).toReal = ((P.map latentTriple) B).toReal
    rw [Measure.map_apply hX hB]
  have hIntOne : IntegrableOn (fun _x : ScoreSpace ε × OutcomeSpace × OutcomeSpace =>
      (1 : ℝ)) B (P.map latentTriple) := integrableOn_const
  have hIntScore : IntegrableOn
      (fun x : ScoreSpace ε × OutcomeSpace × OutcomeSpace => (x.1 : ℝ)) B
      (P.map latentTriple) := by
    apply Integrable.of_bound
      ((by fun_prop : AEStronglyMeasurable
        (fun x : ScoreSpace ε × OutcomeSpace × OutcomeSpace => (x.1 : ℝ))
        (P.map latentTriple)).restrict) (|ε| + |1 - ε| + 1)
    filter_upwards [] with x
    rcases x.1.property with ⟨hx₁, hx₂⟩
    have h₁ := neg_le_abs ε
    have h₂ := le_abs_self (1 - ε)
    have h₃ := neg_le_abs (1 - ε)
    have h₄ := le_abs_self ε
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [MeasureTheory.integral_sub hIntOne hIntScore]
  rw [← hC, ← htreated]
  have hfalse : C \ T = {ω | arm ω = false ∧ latentTriple ω ∈ B} := by
    ext ω
    cases hA : arm ω <;> simp [C, T, hA, and_comm]
  rw [hfalse] at hsplit
  linarith

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,P,hOverlap,hRandom), this result [establishes the stated mathematical conclusion](goal). -/
lemma assignedLatentLaw_true_eq_propensityTiltedLatentLaw
    {ε : ℝ} {J : ℕ} (P : Measure (FullRow ε J)) [IsProbabilityMeasure P]
    (hOverlap : Overlap ε) (hRandom : RandomizedAssignment P) :
    assignedLatentLaw P true = propensityTiltedLatentLaw P true := by
  have hX : Measurable (latentTriple (ε := ε) (J := J)) := by
    unfold latentTriple score outcome0 outcome1
    fun_prop
  ext B hB
  have hInt : IntegrableOn
      (fun x : ScoreSpace ε × OutcomeSpace × OutcomeSpace => (x.1 : ℝ)) B
      (P.map latentTriple) := by
    apply Integrable.of_bound
      ((by fun_prop : AEStronglyMeasurable
        (fun x : ScoreSpace ε × OutcomeSpace × OutcomeSpace => (x.1 : ℝ))
      (P.map latentTriple)).restrict) 1
    filter_upwards [] with x
    rcases x.1.property with ⟨hx₁, hx₂⟩
    exact abs_le.mpr ⟨by linarith [hOverlap.1], by linarith [hOverlap.1]⟩
  have hnonneg : 0 ≤ᵐ[(P.map latentTriple).restrict B]
      fun x : ScoreSpace ε × OutcomeSpace × OutcomeSpace => (x.1 : ℝ) :=
    ae_of_all _ fun x => le_trans hOverlap.1.le x.1.property.1
  have hleft : assignedLatentLaw P true B ≠ ⊤ := by
    rw [assignedLatentLaw, Measure.map_apply hX hB,
      Measure.restrict_apply (hB.preimage hX)]
    exact measure_ne_top P _
  have hright : propensityTiltedLatentLaw P true B ≠ ⊤ := by
    rw [propensityTiltedLatentLaw, withDensity_apply _ hB]
    simp only [armProb, ↓reduceIte]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
      hnonneg).symm.trans_ne (by simp)
  rw [← ENNReal.toReal_eq_toReal_iff' hleft hright]
  rw [assignedLatentLaw, Measure.map_apply hX hB,
    Measure.restrict_apply (hB.preimage hX)]
  change P.real (latentTriple ⁻¹' B ∩ {ω | arm ω = true}) = _
  rw [propensityTiltedLatentLaw, withDensity_apply _ hB]
  simp only [armProb, ↓reduceIte]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
    hnonneg, ENNReal.toReal_ofReal]
  · rw [MeasureTheory.setIntegral_map hB (by fun_prop) hX.aemeasurable]
    convert hRandom B hB using 1
    · apply measureReal_congr
      filter_upwards [] with ω
      change (latentTriple ω ∈ B ∧ arm ω = true) =
        (arm ω = true ∧ latentTriple ω ∈ B)
      exact propext and_comm
    · rfl
  · exact integral_nonneg_of_ae hnonneg

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,P,hOverlap,hRandom), this result [establishes the stated mathematical conclusion](goal). -/
lemma assignedLatentLaw_false_eq_propensityTiltedLatentLaw
    {ε : ℝ} {J : ℕ} (P : Measure (FullRow ε J)) [IsProbabilityMeasure P]
    (hOverlap : Overlap ε) (hRandom : RandomizedAssignment P) :
    assignedLatentLaw P false = propensityTiltedLatentLaw P false := by
  have hX : Measurable (latentTriple (ε := ε) (J := J)) := by
    unfold latentTriple score outcome0 outcome1
    fun_prop
  ext B hB
  have hInt : IntegrableOn
      (fun x : ScoreSpace ε × OutcomeSpace × OutcomeSpace => 1 - (x.1 : ℝ)) B
      (P.map latentTriple) := by
    apply Integrable.of_bound
      ((by fun_prop : AEStronglyMeasurable
        (fun x : ScoreSpace ε × OutcomeSpace × OutcomeSpace => 1 - (x.1 : ℝ))
        (P.map latentTriple)).restrict) 1
    filter_upwards [] with x
    rcases x.1.property with ⟨hx₁, hx₂⟩
    exact abs_le.mpr ⟨by linarith [hOverlap.1], by linarith [hOverlap.1]⟩
  have hnonneg : 0 ≤ᵐ[(P.map latentTriple).restrict B]
      fun x : ScoreSpace ε × OutcomeSpace × OutcomeSpace => 1 - (x.1 : ℝ) :=
    ae_of_all _ fun x => show 0 ≤ 1 - (x.1 : ℝ) by
      linarith [x.1.property.2, hOverlap.1]
  have hleft : assignedLatentLaw P false B ≠ ⊤ := by
    rw [assignedLatentLaw, Measure.map_apply hX hB,
      Measure.restrict_apply (hB.preimage hX)]
    exact measure_ne_top P _
  have hright : propensityTiltedLatentLaw P false B ≠ ⊤ := by
    rw [propensityTiltedLatentLaw, withDensity_apply _ hB]
    simp only [armProb, Bool.false_eq_true, ↓reduceIte]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
      hnonneg).symm.trans_ne (by simp)
  rw [← ENNReal.toReal_eq_toReal_iff' hleft hright]
  rw [assignedLatentLaw, Measure.map_apply hX hB,
    Measure.restrict_apply (hB.preimage hX)]
  change P.real (latentTriple ⁻¹' B ∩ {ω | arm ω = false}) = _
  rw [propensityTiltedLatentLaw, withDensity_apply _ hB]
  simp only [armProb, Bool.false_eq_true, ↓reduceIte]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnonneg,
    ENNReal.toReal_ofReal]
  · rw [← randomizedAssignment_false_measureReal P hRandom B hB]
    apply measureReal_congr
    filter_upwards [] with ω
    change (latentTriple ω ∈ B ∧ arm ω = false) =
      (arm ω = false ∧ latentTriple ω ∈ B)
    exact propext and_comm
  · exact integral_nonneg_of_ae hnonneg

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,P,hOverlap,hRandom,a), this result [establishes the stated mathematical conclusion](goal). -/
lemma assignedLatentLaw_eq_propensityTiltedLatentLaw
    {ε : ℝ} {J : ℕ} (P : Measure (FullRow ε J)) [IsProbabilityMeasure P]
    (hOverlap : Overlap ε) (hRandom : RandomizedAssignment P) (a : ArmSpace) :
    assignedLatentLaw P a = propensityTiltedLatentLaw P a := by
  cases a
  · exact assignedLatentLaw_false_eq_propensityTiltedLatentLaw P hOverlap hRandom
  · exact assignedLatentLaw_true_eq_propensityTiltedLatentLaw P hOverlap hRandom

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,P,hOverlap,hRandom,a), this result [establishes the stated mathematical conclusion](goal). -/
lemma integral_inversePropensity_assignedLatentLaw
    {ε : ℝ} {J : ℕ} (P : Measure (FullRow ε J)) [IsProbabilityMeasure P]
    (hOverlap : Overlap ε) (hRandom : RandomizedAssignment P) (a : ArmSpace) :
    (∫ x, ((if a then x.2.2 else x.2.1 : OutcomeSpace) : ℝ) *
        (armProb a x.1)⁻¹ ∂(assignedLatentLaw P a)) =
      ∫ x, ((if a then x.2.2 else x.2.1 : OutcomeSpace) : ℝ)
        ∂(P.map latentTriple) := by
  rw [assignedLatentLaw_eq_propensityTiltedLatentLaw P hOverlap hRandom a]
  unfold propensityTiltedLatentLaw
  rw [integral_withDensity_eq_integral_toReal_smul
    (by cases a <;> simp only [armProb, Bool.false_eq_true, ↓reduceIte] <;> fun_prop)
    (ae_of_all _ fun _ => by finiteness)]
  apply integral_congr_ae
  filter_upwards [] with x
  have hp : 0 < armProb a x.1 := by
    rcases x.1.property with ⟨hx₁, hx₂⟩
    cases a <;> simp [armProb] <;> linarith [hOverlap.1]
  rw [ENNReal.toReal_ofReal hp.le]
  simp only [smul_eq_mul]
  field_simp

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,P,hOverlap,hRandom,a), this result [establishes the stated mathematical conclusion](goal). -/
lemma potentialOutcomeMean_eq_inversePropensity {ε : ℝ} {J : ℕ}
    (P : Measure (FullRow ε J)) [IsProbabilityMeasure P]
    (hOverlap : Overlap ε) (hRandom : RandomizedAssignment P) (a : ArmSpace) :
    (∫ ω, ((if a then outcome1 ω else outcome0 ω : OutcomeSpace) : ℝ) ∂P) =
      ∫ ω in {ω | arm ω = a},
        ((if a then outcome1 ω else outcome0 ω : OutcomeSpace) : ℝ) *
          (armProb a (score ω))⁻¹ ∂P := by
  have hX : Measurable (latentTriple (ε := ε) (J := J)) := by
    unfold latentTriple score outcome0 outcome1
    fun_prop
  have h := integral_inversePropensity_assignedLatentLaw P hOverlap hRandom a
  rw [assignedLatentLaw, MeasureTheory.integral_map] at h
  · rw [MeasureTheory.integral_map] at h
    · simpa [latentTriple] using h.symm
    · exact hX.aemeasurable
    · cases a with
      | false =>
          change AEStronglyMeasurable
            (fun x : ScoreSpace ε × OutcomeSpace × OutcomeSpace =>
              ((x.2.1 : OutcomeSpace) : ℝ)) _
          fun_prop
      | true =>
          change AEStronglyMeasurable
            (fun x : ScoreSpace ε × OutcomeSpace × OutcomeSpace =>
              ((x.2.2 : OutcomeSpace) : ℝ)) _
          fun_prop
  · exact hX.aemeasurable
  · cases a <;> simp only [armProb, Bool.false_eq_true, ↓reduceIte] <;> fun_prop

/-- For [the specified mathematical inputs](hyp:ε,J,H,g,P,a,r,_hq), [this definition](goal) introduces the corresponding object. -/
def compatibleArmCellCoupling {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (P : Measure (FullRow ε J)) (a : ArmSpace) (r : LabelSpace J)
    (_hq : 0 < armCellMass H g a r) : Measure (ℝ × ℝ) :=
  (ENNReal.ofReal (armCellMass H g a r))⁻¹ •
    ((P.restrict {ω | arm ω = a ∧ g (score ω) = r}).map
      (fun ω =>
        (((if a then outcome1 ω else outcome0 ω : OutcomeSpace) : ℝ),
          (armProb a (score ω))⁻¹)))

/-- Given [the stated mathematical inputs and assumptions](hyp:μ,ν), this result [establishes the stated mathematical conclusion](goal). -/
lemma product_expectation_countermonotoneCoupling_interval
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (∫ p, p.1 * p.2 ∂(Causalean.Stat.countermonotoneCoupling μ ν)) =
      ∫ u in (0 : ℝ)..1,
        Causalean.Stat.quantile μ u * Causalean.Stat.quantile ν (1 - u) := by
  have hrest : volume.restrict (Ioc (0 : ℝ) 1) = Causalean.Stat.unifOI := by
    rw [Causalean.Stat.unifOI, restrict_Ioo_eq_restrict_Ioc]
  unfold Causalean.Stat.countermonotoneCoupling
  let r : ℝ → ℝ := fun u => 1 - u
  have hr : Measurable r := measurable_const.sub measurable_id
  have hνmap : AEMeasurable (Causalean.Stat.quantile ν)
      (Causalean.Stat.unifOI.map r) := by
    simpa [r, Causalean.Stat.map_one_sub_unifOI] using
      (Causalean.Stat.aemeasurable_quantile_unifOI ν)
  have hνr : AEMeasurable (fun u : ℝ => Causalean.Stat.quantile ν (1 - u))
      Causalean.Stat.unifOI := by
    simpa [r, Function.comp_def] using hνmap.comp_measurable hr
  rw [MeasureTheory.integral_map]
  · rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), hrest]
  · exact (Causalean.Stat.aemeasurable_quantile_unifOI μ).prodMk hνr
  · fun_prop

/-- Given [the stated mathematical inputs and assumptions](hyp:μ,ν,hμ,hν), this result [establishes the stated mathematical conclusion](goal). -/
lemma product_expectation_comonotoneCoupling_interval
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp (fun x : ℝ => x) 2 μ) (hν : MemLp (fun y : ℝ => y) 2 ν) :
    (∫ p, p.1 * p.2 ∂(Causalean.Stat.comonotoneCoupling μ ν)) =
      ∫ u in (0 : ℝ)..1,
        Causalean.Stat.quantile μ u * Causalean.Stat.quantile ν u := by
  have hrest : volume.restrict (Ioc (0 : ℝ) 1) = Causalean.Stat.unifOI := by
    rw [Causalean.Stat.unifOI, restrict_Ioo_eq_restrict_Ioc]
  rw [Causalean.Stat.product_expectation_comonotoneCoupling μ ν hμ hν,
    ← integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), hrest]

/-- Given [the stated mathematical inputs and assumptions](hyp:π,μ,ν,hπ,hμ,hν), this result [establishes the stated mathematical conclusion](goal). -/
lemma product_expectation_mem_quantileInterval
    {π : Measure (ℝ × ℝ)} {μ ν : Measure ℝ}
    (hπ : Causalean.Stat.IsCoupling π μ ν)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp (fun x : ℝ => x) 2 μ) (hν : MemLp (fun y : ℝ => y) 2 ν) :
    (∫ p, p.1 * p.2 ∂π) ∈
      Icc
        (∫ u in (0 : ℝ)..1,
          Causalean.Stat.quantile μ u * Causalean.Stat.quantile ν (1 - u))
        (∫ u in (0 : ℝ)..1,
          Causalean.Stat.quantile μ u * Causalean.Stat.quantile ν u) := by
  constructor
  · rw [← product_expectation_countermonotoneCoupling_interval μ ν]
    exact Causalean.Stat.countermonotone_le_product_expectation hπ hμ hν
  · rw [← product_expectation_comonotoneCoupling_interval μ ν hμ hν]
    exact Causalean.Stat.product_expectation_le_comonotone hπ hμ hν

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,a,π,hπ,hY2,hW2,m,hm), this result [establishes the stated mathematical conclusion](goal). -/
lemma armMean_mem_endpoints_of_cellCouplings {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (a : ArmSpace)
    (π : ∀ r : LabelSpace J, 0 < armCellMass H g a r → Measure (ℝ × ℝ))
    (hπ : ∀ (r : LabelSpace J) (hq : 0 < armCellMass H g a r),
      Causalean.Stat.IsCoupling (π r hq)
        (armCellOutcomeLaw Prel hMass.2.1 a r
          (by rw [hMass.2.2.2 a r]; exact hq))
        (armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq))
    (hY2 : ∀ (r : LabelSpace J) (hq : 0 < armCellMass H g a r),
      MemLp (fun x : ℝ => x) 2
        (armCellOutcomeLaw Prel hMass.2.1 a r
          (by rw [hMass.2.2.2 a r]; exact hq)))
    (hW2 : ∀ (r : LabelSpace J) (hq : 0 < armCellMass H g a r),
      MemLp (fun x : ℝ => x) 2
        (armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq))
    (m : ℝ)
    (hm : m = ∑ r : LabelSpace J,
      if hq : 0 < armCellMass H g a r then
        armCellMass H g a r * ∫ p, p.1 * p.2 ∂(π r hq)
      else 0) :
    m ∈ Icc (muLower H g Prel hMass a) (muUpper H g Prel hMass a) := by
  rw [hm]
  constructor
  · unfold muLower
    apply Finset.sum_le_sum
    intro r _
    by_cases hq : 0 < armCellMass H g a r
    · simp only [hq, dif_pos]
      letI : IsProbabilityMeasure (π r hq) := (hπ r hq).isProbabilityMeasure
      letI : IsProbabilityMeasure
          (armCellOutcomeLaw Prel hMass.2.1 a r
            (by rw [hMass.2.2.2 a r]; exact hq)) := by
        rw [← (hπ r hq).map_fst]
        exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
      letI : IsProbabilityMeasure
          (armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq) := by
        rw [← (hπ r hq).map_snd]
        exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
      apply mul_le_mul_of_nonneg_left _ hq.le
      exact (product_expectation_mem_quantileInterval (hπ r hq)
        (hY2 r hq) (hW2 r hq)).1
    · simp [hq]
  · unfold muUpper
    apply Finset.sum_le_sum
    intro r _
    by_cases hq : 0 < armCellMass H g a r
    · simp only [hq, dif_pos]
      letI : IsProbabilityMeasure (π r hq) := (hπ r hq).isProbabilityMeasure
      letI : IsProbabilityMeasure
          (armCellOutcomeLaw Prel hMass.2.1 a r
            (by rw [hMass.2.2.2 a r]; exact hq)) := by
        rw [← (hπ r hq).map_fst]
        exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
      letI : IsProbabilityMeasure
          (armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq) := by
        rw [← (hπ r hq).map_snd]
        exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
      apply mul_le_mul_of_nonneg_left _ hq.le
      exact (product_expectation_mem_quantileInterval (hπ r hq)
        (hY2 r hq) (hW2 r hq)).2
    · simp [hq]

end
end CausalSmith.PartialID.UnlinkedPropensityAte

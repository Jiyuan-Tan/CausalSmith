module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.Reduction
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.Identification_Part1

/-! # Conditional IV identities and transported CACE -/

public section

open MeasureTheory Set
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength
-- @node: armMeanVersion_conditionalMean
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hP,A,z), [the stated result about arm mean version conditional mean holds](goal). -/
lemma armMeanVersion_conditionalMean (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hP : ModelClass c_f C_f L P n) (A z : Bool) :
    ConditionalMean P true (potentialArmValue A z) (armMeanVersion P A z) := by
  let μ := populationLaw P true
  let m0 : MeasurableSpace FullData := inferInstance
  have hcov : @Measurable FullData ℝ m0 _ covariate := by
    simpa [m0] using (show Measurable (covariate : FullData → ℝ) by
      unfold covariate; fun_prop)
  let q := armMeanVersion P A z
  let f := potentialArmValue A z
  let w : FullData → ℝ := fun o => assignmentMass P z (covariate o)
  haveI : IsProbabilityMeasure P.fullLaw := hP.sourceBounds.2.2.1
  haveI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    by_cases hp : P.fullLaw {o | population o = true} = 0
    · simp [μ, populationLaw, ProbabilityTheory.cond, hp]
    · simp only [μ, populationLaw, ProbabilityTheory.cond, Measure.coe_smul,
        Pi.smul_apply, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter,
        smul_eq_mul]
      rw [ENNReal.inv_mul_cancel hp (measure_ne_top P.fullLaw _)]
      exact ENNReal.one_lt_top
  have hq : Measurable q := armMeanVersion_measurable L P hP.armHolder A z
  have hf : @Measurable FullData ℝ m0 _ f := by
    have hr0 : @Measurable FullData Bool m0 _ receipt0 := by
      simpa [m0] using (show Measurable (receipt0 : FullData → Bool) by unfold receipt0; fun_prop)
    have hr1 : @Measurable FullData Bool m0 _ receipt1 := by
      simpa [m0] using (show Measurable (receipt1 : FullData → Bool) by unfold receipt1; fun_prop)
    have hy0 : @Measurable FullData ℝ m0 _ outcome0 := by
      simpa [m0] using (show Measurable (outcome0 : FullData → ℝ) by unfold outcome0; fun_prop)
    have hy1 : @Measurable FullData ℝ m0 _ outcome1 := by
      simpa [m0] using (show Measurable (outcome1 : FullData → ℝ) by unfold outcome1; fun_prop)
    have hbool : Measurable (boolReal : Bool → ℝ) := measurable_of_finite _
    cases A <;> cases z
    · change Measurable (fun o => boolReal (receipt0 o)); exact hbool.comp hr0
    · change Measurable (fun o => boolReal (receipt1 o)); exact hbool.comp hr1
    · change Measurable (fun o => if receipt0 o then outcome1 o else outcome0 o)
      exact hy1.ite (hr0 (measurableSet_singleton true)) hy0
    · change Measurable (fun o => if receipt1 o then outcome1 o else outcome0 o)
      exact hy1.ite (hr1 (measurableSet_singleton true)) hy0
  have hsupp : ∀ᵐ o ∂μ, covariate o ∈ covariateSpace := by
    apply (ProbabilityTheory.cond_absolutelyContinuous : μ.AbsolutelyContinuous P.fullLaw).ae_le
    exact hP.sourceBounds.2.2.2.1.mono fun _ ho => ho.1
  have hw : AEMeasurable w μ := by
    have hsupported : @Measurable FullData ℝ m0 _ (fun o =>
        covariateSpace.indicator (assignmentMass P z) (covariate o)) :=
      (measurable_assignmentMassOnCovariate P z hP.randomized.2.1).comp hcov
    refine hsupported.aemeasurable.congr ?_
    filter_upwards [hsupp] with o ho
    simp [w, ho]
  have hwpos : ∀ᵐ o ∂μ, 0 < w o := by
    filter_upwards [hsupp] with o ho
    rcases hP.overlap (covariate o) ho with ⟨he0, he1⟩
    cases z <;> simp [w, assignmentMass] <;> linarith
  have hbounds : ∀ᵐ o ∂μ,
      covariate o ∈ covariateSpace ∧ outcome0 o ∈ Icc (0 : ℝ) 1 ∧
        outcome1 o ∈ Icc (0 : ℝ) 1 :=
    (ProbabilityTheory.cond_absolutelyContinuous : μ.AbsolutelyContinuous P.fullLaw).ae_le
      hP.sourceBounds.2.2.2.1
  have hfbd : ∀ᵐ o ∂μ, ‖f o‖ ≤ 1 := by
    filter_upwards [hbounds] with o ho
    rcases ho with ⟨_, h0, h1⟩
    cases A <;> cases z <;>
      simp [f, potentialArmValue, potentialReceipt, potentialOutcome, boolReal] <;>
      split <;> simp_all [Real.norm_eq_abs, abs_le] <;>
      nlinarith [h0.1, h0.2, h1.1, h1.2]
  have hfint : Integrable f μ := by
    exact Integrable.of_bound hf.aestronglyMeasurable 1 hfbd
  have hwbd : ∀ᵐ o ∂μ, ‖w o‖ ≤ 1 := by
    filter_upwards [hsupp] with o ho
    rcases hP.overlap (covariate o) ho with ⟨he0, he1⟩
    have hw0 : 0 ≤ w o := by
      cases z <;> simp [w, assignmentMass] <;> linarith
    have hw1 : w o ≤ 1 := by
      cases z <;> simp [w, assignmentMass] <;> linarith
    simpa [Real.norm_eq_abs, abs_of_nonneg hw0] using hw1
  have hwfint : Integrable (w * f) μ := by
    apply Integrable.of_bound (hw.mul hf.aemeasurable).aestronglyMeasurable 1
    filter_upwards [hwbd, hfbd] with o hwo hfo
    simp only [Pi.mul_apply, norm_mul]
    nlinarith [norm_nonneg (w o), norm_nonneg (f o)]
  have hgint : Integrable (w * fun o => q (covariate o)) μ := by
    apply Integrable.of_bound
      ((hw.mul (hq.comp hcov).aemeasurable).aestronglyMeasurable) 1
    filter_upwards [hwbd, hsupp] with o hwo ho
    have hqbd : ‖q (covariate o)‖ ≤ 1 := by
      have hm := hP.armHolder.2.1 A z |>.2.2 (covariate o) ho
      simp [q, armMeanVersion, Set.indicator_of_mem ho, Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [hm.1], hm.2⟩
    simp only [Pi.mul_apply, norm_mul]
    change ‖w o‖ * ‖q (covariate o)‖ ≤ 1
    nlinarith [norm_nonneg (w o), norm_nonneg (q (covariate o))]
  have hwX : Measurable (covariateSpace.indicator (assignmentMass P z)) :=
    measurable_assignmentMassOnCovariate P z hP.randomized.2.1
  have hXLaw : sourceXLaw P = μ.map covariate := by
    have hobs : Measurable (observeSource : Assigned → SourceObs) := by
      unfold observeSource covariate
      fun_prop
    calc
      sourceXLaw P = P.assignedLaw.map (fun o : Assigned => covariate o.1) := by
        rw [sourceXLaw, sourceObsLaw, Measure.map_map (by fun_prop) hobs]
        rfl
      _ = (P.assignedLaw.map Prod.fst).map covariate := by
        rw [Measure.map_map hcov (by fun_prop)]
        rfl
      _ = μ.map covariate := by
        change (P.assignedLaw.map Prod.fst).map covariate =
          (populationLaw P true).map covariate
        rw [hP.randomized.2.2.1]
  let mX : MeasurableSpace FullData := MeasurableSpace.comap covariate Real.measurableSpace
  have hmX : mX ≤ m0 := hcov.comap_le
  haveI : IsFiniteMeasure (μ.trim hmX) := isFiniteMeasure_trim hmX
  haveI : SigmaFinite (μ.trim hmX) := inferInstance
  letI : MeasurableSpace FullData := m0
  have hw_mX : AEStronglyMeasurable[mX] w μ := by
    have hsupported : Measurable[mX] (fun o : FullData =>
        covariateSpace.indicator (assignmentMass P z) (covariate o)) :=
      (measurable_assignmentMassOnCovariate P z hP.randomized.2.1).comp
        (comap_measurable covariate)
    refine hsupported.aestronglyMeasurable.congr ?_
    filter_upwards [hsupp] with o ho
    simp [w, ho]
  have hweighted : (w * fun o => q (covariate o)) =ᵐ[μ] μ[w * f | mX] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hmX hwfint
      (fun _ _ _ => hgint.integrableOn)
    · intro C hC _
      obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hC
      let B0 := B ∩ covariateSpace
      have hB0 : MeasurableSet B0 := hB.inter measurableSet_Icc
      have hsub : B0 ⊆ covariateSpace := inter_subset_right
      have hpreB : MeasurableSet {o : FullData | covariate o ∈ B} := hB.preimage hcov
      have hpreB0 : MeasurableSet {o : FullData | covariate o ∈ B0} := hB0.preimage hcov
      have hsetae : {o : FullData | covariate o ∈ B} =ᵐ[μ]
          {o : FullData | covariate o ∈ B0} := by
        filter_upwards [hsupp] with o ho
        apply propext
        constructor
        · intro hBo
          exact ⟨hBo, ho⟩
        · intro hBo
          exact hBo.1
      have hrestrict (r : FullData → ℝ) :
          (∫ o in {o : FullData | covariate o ∈ B}, r o ∂μ) =
            ∫ o in {o : FullData | covariate o ∈ B0}, r o ∂μ := by
        rw [← integral_indicator hpreB, ← integral_indicator hpreB0]
        exact integral_congr_ae (indicator_ae_eq_of_ae_eq_set hsetae)
      calc
        (∫ o in {o : FullData | covariate o ∈ B},
            (w * fun o => q (covariate o)) o ∂μ) =
            ∫ o in {o : FullData | covariate o ∈ B0},
              (w * fun o => q (covariate o)) o ∂μ := hrestrict _
        _ = ∫ o in {o : FullData | covariate o ∈ B0},
              covariateSpace.indicator (assignmentMass P z) (covariate o) *
                q (covariate o) ∂μ := by
          apply setIntegral_congr_fun hpreB0
          intro o ho
          simp [w, hsub ho]
        _ = ∫ x in B0,
              covariateSpace.indicator (assignmentMass P z) x * q x
              ∂sourceXLaw P := by
          rw [hXLaw]
          exact (setIntegral_map hB0 (hwX.mul hq).aestronglyMeasurable
            hcov.aemeasurable).symm
        _ = ∫ x in B0, assignmentMass P z x * q x ∂sourceXLaw P := by
          apply setIntegral_congr_fun hB0
          intro x hx
          simp [hsub hx]
        _ = ∫ x in B0, P.fS x * (assignmentMass P z x * q x) :=
          source_setIntegral_eq_density_integral c_f C_f L P n hP B0 hB0 hsub _
        _ = ∫ x in B0, P.fS x * assignmentMass P z x * P.m A z x := by
          apply setIntegral_congr_fun hB0
          intro x hx
          simp [q, armMeanVersion, Set.indicator_of_mem (hsub hx), mul_assoc]
        _ = ∫ o in {o : FullData | covariate o ∈ B0},
            assignmentMass P z (covariate o) * potentialArmValue A z o ∂μ :=
          source_arm_potential_integral c_f C_f L P n hP A z B0 hB0 hsub
        _ = ∫ o in {o : FullData | covariate o ∈ B},
            (w * f) o ∂μ := by
          rw [hrestrict]
          rfl
    · exact (hw_mX.mul
        ((hq.comp (comap_measurable covariate)).aestronglyMeasurable))
  have hpull : μ[w * f | mX] =ᵐ[μ] w * μ[f | mX] :=
    condExp_mul_of_aestronglyMeasurable_left hw_mX hwfint hfint
  have hqce_comp : (fun o => q (covariate o)) =ᵐ[μ] μ[f | mX] := by
    filter_upwards [hweighted, hpull, hwpos] with o h1 h2 hpos
    dsimp only [Pi.mul_apply] at h1 h2
    rw [h2] at h1
    exact (mul_left_cancel₀ (ne_of_gt hpos) h1)
  refine ⟨hq, ?_⟩
  intro B hB
  have hpre : MeasurableSet[mX] {o : FullData | covariate o ∈ B} := by
    exact MeasurableSpace.measurableSet_comap.mpr ⟨B, hB, rfl⟩
  calc
    (∫ o in {o : FullData | covariate o ∈ B}, f o ∂μ) =
        ∫ o in {o : FullData | covariate o ∈ B}, (μ[f | mX]) o ∂μ :=
      (setIntegral_condExp hmX hfint hpre).symm
    _ = ∫ o in {o : FullData | covariate o ∈ B}, q (covariate o) ∂μ :=
      setIntegral_congr_ae (hmX _ hpre) (hqce_comp.symm.mono fun _ ho _ => ho)
    _ = ∫ x in B, q x ∂μ.map covariate := by
      exact (setIntegral_map hB hq.aestronglyMeasurable hcov.aemeasurable).symm
    _ = _ := by rfl

-- @node: sourceXLaw_eq_source_population_map
/-- Given [the supplied inputs](hyp:P,hP), [the stated result about source xlaw eq source population map holds](goal). -/
lemma sourceXLaw_eq_source_population_map (P : TransportLaw)
    (hP : InstrumentRandomization P) :
    sourceXLaw P = (populationLaw P true).map covariate := by
  have hcov : Measurable (covariate : FullData → ℝ) := by
    unfold covariate
    fun_prop
  have hobs : Measurable (observeSource : Assigned → SourceObs) := by
    unfold observeSource covariate
    fun_prop
  calc
    sourceXLaw P = P.assignedLaw.map (fun o : Assigned => covariate o.1) := by
      rw [sourceXLaw, sourceObsLaw, Measure.map_map (by fun_prop) hobs]
      rfl
    _ = (P.assignedLaw.map Prod.fst).map covariate := by
      rw [Measure.map_map hcov (by fun_prop)]
      rfl
    _ = (populationLaw P true).map covariate := by rw [hP.2.2.1]

-- @node: conditionalMean_unique_source
/-- Given [the supplied inputs](hyp:P,hP,f,q,r,hq,hr), [the stated result about conditional mean unique source holds](goal). -/
lemma conditionalMean_unique_source (P : TransportLaw)
    (hP : InstrumentRandomization P) (f : FullData → ℝ) (q r : ℝ → ℝ)
    (hq : ConditionalMean P true f q) (hr : ConditionalMean P true f r) :
    q =ᵐ[sourceXLaw P] r := by
  haveI : IsProbabilityMeasure P.assignedLaw := hP.1
  haveI : IsFiniteMeasure (sourceXLaw P) := by
    dsimp [sourceXLaw, sourceObsLaw]
    infer_instance
  apply measurable_ae_eq_of_forall_setIntegral_eq (sourceXLaw P) q r hq.1 hr.1
  intro B hB
  rw [sourceXLaw_eq_source_population_map P hP]
  exact (hq.2 B hB).symm.trans (hr.2 B hB)

-- @node: conditionalMean_sub
/-- Given [the supplied inputs](hyp:P,s,h₁,h₀,hf₁,hf₀,hq₁,hq₀), [the difference of two conditional means is the conditional mean of the difference](goal). -/
lemma conditionalMean_sub (P : TransportLaw) (s : Bool)
    (f₁ f₀ : FullData → ℝ) (q₁ q₀ : ℝ → ℝ)
    (h₁ : ConditionalMean P s f₁ q₁) (h₀ : ConditionalMean P s f₀ q₀)
    (hf₁ : Integrable f₁ (populationLaw P s))
    (hf₀ : Integrable f₀ (populationLaw P s))
    (hq₁ : Integrable q₁ ((populationLaw P s).map covariate))
    (hq₀ : Integrable q₀ ((populationLaw P s).map covariate)) :
    ConditionalMean P s (f₁ - f₀) (q₁ - q₀) := by
  refine ⟨h₁.1.sub h₀.1, ?_⟩
  intro B hB
  rw [integral_sub' hf₁.integrableOn hf₀.integrableOn,
    integral_sub' hq₁.integrableOn hq₀.integrableOn, h₁.2 B hB, h₀.2 B hB]

-- @node: armContrastVersion_conditionalMean
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hP,A), [the stated result about arm contrast version conditional mean holds](goal). -/
lemma armContrastVersion_conditionalMean (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hP : ModelClass c_f C_f L P n) (A : Bool) :
    ConditionalMean P true
      (potentialArmValue A true - potentialArmValue A false)
      (armMeanVersion P A true - armMeanVersion P A false) := by
  let μ := populationLaw P true
  haveI : IsProbabilityMeasure P.fullLaw := hP.sourceBounds.2.2.1
  haveI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    by_cases hp : P.fullLaw {o | population o = true} = 0
    · simp [μ, populationLaw, ProbabilityTheory.cond, hp]
    · simp only [μ, populationLaw, ProbabilityTheory.cond, Measure.coe_smul,
        Pi.smul_apply, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter,
        smul_eq_mul]
      rw [ENNReal.inv_mul_cancel hp (measure_ne_top P.fullLaw _)]
      exact ENNReal.one_lt_top
  haveI : IsFiniteMeasure (μ.map covariate) := by infer_instance
  have hmeasF (z : Bool) : Measurable (potentialArmValue A z) := by
    have hr0 : Measurable (receipt0 : FullData → Bool) := by unfold receipt0; fun_prop
    have hr1 : Measurable (receipt1 : FullData → Bool) := by unfold receipt1; fun_prop
    have hy0 : Measurable (outcome0 : FullData → ℝ) := by unfold outcome0; fun_prop
    have hy1 : Measurable (outcome1 : FullData → ℝ) := by unfold outcome1; fun_prop
    have hbool : Measurable (boolReal : Bool → ℝ) := measurable_of_finite _
    cases A <;> cases z
    · change Measurable (fun o => boolReal (receipt0 o)); exact hbool.comp hr0
    · change Measurable (fun o => boolReal (receipt1 o)); exact hbool.comp hr1
    · change Measurable (fun o => if receipt0 o then outcome1 o else outcome0 o)
      exact hy1.ite (hr0 (measurableSet_singleton true)) hy0
    · change Measurable (fun o => if receipt1 o then outcome1 o else outcome0 o)
      exact hy1.ite (hr1 (measurableSet_singleton true)) hy0
  have hbounds : ∀ᵐ o ∂μ,
      outcome0 o ∈ Icc (0 : ℝ) 1 ∧ outcome1 o ∈ Icc (0 : ℝ) 1 := by
    apply (ProbabilityTheory.cond_absolutelyContinuous : μ.AbsolutelyContinuous P.fullLaw).ae_le
    exact hP.sourceBounds.2.2.2.1.mono fun _ ho => ⟨ho.2.1, ho.2.2⟩
  have hintF (z : Bool) : Integrable (potentialArmValue A z) μ := by
    apply Integrable.of_bound (hmeasF z).aestronglyMeasurable 1
    filter_upwards [hbounds] with o ho
    rcases ho with ⟨h0, h1⟩
    cases A <;> cases z <;>
      simp [potentialArmValue, potentialReceipt, potentialOutcome, boolReal,
        Real.norm_eq_abs, abs_le] <;>
      split <;> simp_all [Real.norm_eq_abs, abs_le] <;>
      nlinarith [h0.1, h0.2, h1.1, h1.2]
  have hintQ (z : Bool) : Integrable (armMeanVersion P A z) (μ.map covariate) := by
    apply Integrable.of_bound
      (armMeanVersion_measurable L P hP.armHolder A z).aestronglyMeasurable 1
    filter_upwards [] with x
    by_cases hx : x ∈ covariateSpace
    · have hm := hP.armHolder.2.1 A z |>.2.2 x hx
      simp [armMeanVersion, Set.indicator_of_mem hx, Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [hm.1], hm.2⟩
    · simp [armMeanVersion, hx]
  exact conditionalMean_sub P true _ _ _ _
    (armMeanVersion_conditionalMean c_f C_f L P n hP A true)
    (armMeanVersion_conditionalMean c_f C_f L P n hP A false)
    (hintF true) (hintF false) (hintQ true) (hintQ false)

-- @node: lem:transported-cace-identification
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hf,hF,hL,hP), [the stated result about transported cace identification holds](goal). -/
lemma transported_cace_identification (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hf : 0 < c_f ∧ c_f < 1) (hF : 1 < C_f) (hL : 1 < L)
    (hP : ModelClass c_f C_f L P n) :
    (∀ z : Bool,
      (∃ qDz : ℝ → ℝ,
        ConditionalMean P true
          (fun o => boolReal (potentialReceipt o z)) qDz ∧
        P.m false z =ᵐ[sourceXLaw P] qDz) ∧
      (∃ qYz : ℝ → ℝ,
        ConditionalMean P true
          (fun o => potentialOutcome o (potentialReceipt o z)) qYz ∧
        P.m true z =ᵐ[sourceXLaw P] qYz)) ∧
    (∃ qD qY : ℝ → ℝ,
      ConditionalMean P true
        (fun o => boolReal (receipt1 o) - boolReal (receipt0 o)) qD ∧
      ConditionalMean P true
        (fun o => potentialOutcome o (receipt1 o) -
          potentialOutcome o (receipt0 o)) qY ∧
      ConditionalMean P false complier qD ∧
      ConditionalMean P true complier qD ∧
      ConditionalMean P false
        (fun o => (outcome1 o - outcome0 o) * complier o) qY ∧
      ConditionalMean P true
        (fun o => (outcome1 o - outcome0 o) * complier o) qY ∧
      armContrast P false =ᵐ[targetXLaw P] qD ∧
      armContrast P true =ᵐ[targetXLaw P] qY) ∧
    (∀ᵐ o ∂P.fullLaw,
      boolReal (receipt1 o) - boolReal (receipt0 o) = complier o) ∧
    firstStage P = targetComplierShare P ∧
    transportedForm P true =
      ∫ o, (outcome1 o - outcome0 o) * complier o
        ∂populationLaw P false ∧
    targetCACE P = transportedForm P true / firstStage P ∧
    targetCACE P ∈ parameterSpace := by
  have hident : ∃ qD qY : ℝ → ℝ,
      ConditionalMean P true
        (fun o => boolReal (receipt1 o) - boolReal (receipt0 o)) qD ∧
      ConditionalMean P true
        (fun o => potentialOutcome o (receipt1 o) -
          potentialOutcome o (receipt0 o)) qY ∧
      ConditionalMean P false complier qD ∧
      ConditionalMean P true complier qD ∧
      ConditionalMean P false
        (fun o => (outcome1 o - outcome0 o) * complier o) qY ∧
      ConditionalMean P true
        (fun o => (outcome1 o - outcome0 o) * complier o) qY ∧
      armContrast P false =ᵐ[targetXLaw P] qD ∧
      armContrast P true =ᵐ[targetXLaw P] qY := by
    obtain ⟨qD, hqDtarget, hqDsource⟩ := hP.shareTransport
    obtain ⟨qY, hqYtarget, hqYsource⟩ := hP.outcomeTransport
    have hreceipt := conditionalMean_congr_full_ae P true
      (fun o => boolReal (receipt1 o) - boolReal (receipt0 o))
      complier qD (monotone_receipt_difference_eq_complier P hP.monotone)
      hqDsource
    have houtcome := conditionalMean_congr_full_ae P true
      (fun o => potentialOutcome o (receipt1 o) - potentialOutcome o (receipt0 o))
      (fun o => (outcome1 o - outcome0 o) * complier o) qY
      (potentialOutcome_difference_eq_complier P hP.monotone) hqYsource
    have harm : armContrast P false =ᵐ[targetXLaw P] qD ∧
        armContrast P true =ᵐ[targetXLaw P] qY := by
      have hraw (A : Bool) : armContrast P A =ᵐ[sourceXLaw P]
          (armMeanVersion P A true - armMeanVersion P A false) := by
        filter_upwards [armMeanVersion_ae_eq c_f C_f L P n hP A true,
          armMeanVersion_ae_eq c_f C_f L P n hP A false] with x h1 h0
        change P.m A true x - P.m A false x =
          armMeanVersion P A true x - armMeanVersion P A false x
        rw [h1, h0]
      have hreceipt' : ConditionalMean P true
          (potentialArmValue false true - potentialArmValue false false) qD := by
        change ConditionalMean P true
          (fun o => boolReal (receipt1 o) - boolReal (receipt0 o)) qD
        exact hreceipt
      have houtcome' : ConditionalMean P true
          (potentialArmValue true true - potentialArmValue true false) qY := by
        change ConditionalMean P true
          (fun o => potentialOutcome o (receipt1 o) -
            potentialOutcome o (receipt0 o)) qY
        exact houtcome
      have hvD := conditionalMean_unique_source P hP.randomized _ _ _
        (armContrastVersion_conditionalMean c_f C_f L P n hP false) hreceipt'
      have hvY := conditionalMean_unique_source P hP.randomized _ _ _
        (armContrastVersion_conditionalMean c_f C_f L P n hP true) houtcome'
      have hsD := (hraw false).trans hvD
      have hsY := (hraw true).trans hvY
      exact ⟨(target_absolutelyContinuous_source c_f C_f L P n hP).ae_le hsD,
        (target_absolutelyContinuous_source c_f C_f L P n hP).ae_le hsY⟩
    exact ⟨qD, qY, hreceipt, houtcome, hqDtarget, hqDsource,
      hqYtarget, hqYsource, harm.1, harm.2⟩
  obtain ⟨qD, qY, hqDsrc, hqYsrc, hqD, hqDsrc2, hqY, hqYsrc2,
    haeD, haeY⟩ := hident
  have hfirst : firstStage P = targetComplierShare P := by
    calc
      firstStage P = ∫ x in covariateSpace, P.fT x * armContrast P false x := rfl
      _ = ∫ x, armContrast P false x ∂targetXLaw P :=
        (target_integral_eq_density_integral c_f C_f L P n hP _).symm
      _ = ∫ x, qD x ∂targetXLaw P := integral_congr_ae haeD
      _ = ∫ o, complier o ∂populationLaw P false := by
        have h := hqD.2 Set.univ MeasurableSet.univ
        simpa [targetXLaw] using h.symm
      _ = targetComplierShare P := integral_complier_eq_targetComplierShare P
  have hout : transportedForm P true =
      ∫ o, (outcome1 o - outcome0 o) * complier o
        ∂populationLaw P false := by
    calc
      transportedForm P true =
          ∫ x in covariateSpace, P.fT x * armContrast P true x := rfl
      _ = ∫ x, armContrast P true x ∂targetXLaw P :=
        (target_integral_eq_density_integral c_f C_f L P n hP _).symm
      _ = ∫ x, qY x ∂targetXLaw P := integral_congr_ae haeY
      _ = ∫ o, (outcome1 o - outcome0 o) * complier o
          ∂populationLaw P false := by
        have h := hqY.2 Set.univ MeasurableSet.univ
        simpa [targetXLaw] using h.symm
  refine ⟨?_, ?_, monotone_receipt_difference_eq_complier P hP.monotone,
    hfirst, hout, ?_, ?_⟩
  · intro z
    constructor
    · refine ⟨armMeanVersion P false z, ?_, ?_⟩
      · change ConditionalMean P true (potentialArmValue false z) _
        exact armMeanVersion_conditionalMean c_f C_f L P n hP false z
      · exact (armMeanVersion_ae_eq c_f C_f L P n hP false z).symm
    · refine ⟨armMeanVersion P true z, ?_, ?_⟩
      · change ConditionalMean P true (potentialArmValue true z) _
        exact armMeanVersion_conditionalMean c_f C_f L P n hP true z
      · exact (armMeanVersion_ae_eq c_f C_f L P n hP true z).symm
  · exact ⟨qD, qY, hqDsrc, hqYsrc, hqD, hqDsrc2,
      hqY, hqYsrc2, haeD, haeY⟩
  · rw [targetCACE, hout, hfirst]
  · exact targetCACE_mem_parameterSpace c_f C_f L P n hP hfirst

end CausalSmith.Stat.TransportCaceRoughnuisanceLength

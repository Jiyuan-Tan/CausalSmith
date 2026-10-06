module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.Reduction
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Conditional IV identities and transported CACE -/

@[expose] public section

open MeasureTheory Set
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength
-- @node: potentialOutcome_difference
/-- Given [the supplied inputs](hyp:o), [the stated result about potential outcome difference holds](goal). -/
lemma potentialOutcome_difference (o : FullData) :
    potentialOutcome o (receipt1 o) - potentialOutcome o (receipt0 o) =
      (outcome1 o - outcome0 o) *
        (boolReal (receipt1 o) - boolReal (receipt0 o)) := by
  cases receipt0 o <;> cases receipt1 o <;>
    simp [potentialOutcome, boolReal]

-- @node: monotone_receipt_difference_eq_complier
/-- Given [the supplied inputs](hyp:P,hmono), [the stated result about monotone receipt difference eq complier holds](goal). -/
lemma monotone_receipt_difference_eq_complier (P : TransportLaw)
    (hmono : Monotonicity P) :
    ∀ᵐ o ∂P.fullLaw,
      boolReal (receipt1 o) - boolReal (receipt0 o) = complier o := by
  filter_upwards [hmono] with o ho
  cases h0 : receipt0 o <;> cases h1 : receipt1 o <;>
    simp [boolReal, complier, h0, h1] at ho ⊢; norm_num at ho

-- @node: potentialOutcome_difference_eq_complier
/-- Given [the supplied inputs](hyp:P,hmono), [the stated result about potential outcome difference eq complier holds](goal). -/
lemma potentialOutcome_difference_eq_complier (P : TransportLaw)
    (hmono : Monotonicity P) :
    ∀ᵐ o ∂P.fullLaw,
      potentialOutcome o (receipt1 o) - potentialOutcome o (receipt0 o) =
        (outcome1 o - outcome0 o) * complier o := by
  filter_upwards [monotone_receipt_difference_eq_complier P hmono] with o ho
  rw [potentialOutcome_difference, ho]

-- @node: conditionalMean_congr_full_ae
/-- Given [the supplied inputs](hyp:P,s,f,g,q,hfg,hg), [the stated result about conditional mean congr full ae holds](goal). -/
lemma conditionalMean_congr_full_ae (P : TransportLaw) (s : Bool)
    (f g : FullData → ℝ) (q : ℝ → ℝ)
    (hfg : f =ᵐ[P.fullLaw] g) (hg : ConditionalMean P s g q) :
    ConditionalMean P s f q := by
  refine ⟨hg.1, ?_⟩
  intro B hB
  have hcov : Measurable (covariate : FullData → ℝ) := by
    unfold covariate
    fun_prop
  have hset : MeasurableSet {o : FullData | covariate o ∈ B} :=
    hB.preimage hcov
  have hcond : f =ᵐ[populationLaw P s] g :=
    (ProbabilityTheory.cond_absolutelyContinuous :
      (populationLaw P s).AbsolutelyContinuous P.fullLaw).ae_le hfg
  calc
    (∫ o in {o | covariate o ∈ B}, f o ∂populationLaw P s) =
        ∫ o in {o | covariate o ∈ B}, g o ∂populationLaw P s :=
      setIntegral_congr_ae₀ hset.nullMeasurableSet (hcond.mono fun _ ho _ => ho)
    _ = ∫ x in B, q x ∂(populationLaw P s).map covariate := hg.2 B hB

-- @node: integral_complier_eq_targetComplierShare
/-- Given [the supplied inputs](hyp:P), [the stated result about integral complier eq target complier share holds](goal). -/
lemma integral_complier_eq_targetComplierShare (P : TransportLaw) :
    (∫ o, complier o ∂populationLaw P false) = targetComplierShare P := by
  let s : Set FullData := {o | complier o = 1}
  have hs : MeasurableSet s := by
    have hm0 : Measurable (receipt0 : FullData → Bool) := by
      unfold receipt0
      fun_prop
    have hm1 : Measurable (receipt1 : FullData → Bool) := by
      unfold receipt1
      fun_prop
    dsimp [s, complier]
    measurability
  have hpoint : (fun o : FullData => complier o) = s.indicator (1 : FullData → ℝ) := by
    funext o
    simp only [s, Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
    split_ifs <;> simp_all [complier]
  rw [hpoint, integral_indicator_one hs]
  rfl

-- @node: measurable_complier
/-- [the stated result about measurable complier holds](goal). -/
lemma measurable_complier : Measurable (complier : FullData → ℝ) := by
  have hm0 : Measurable (receipt0 : FullData → Bool) := by unfold receipt0; fun_prop
  have hm1 : Measurable (receipt1 : FullData → Bool) := by unfold receipt1; fun_prop
  have hs : MeasurableSet {o : FullData | receipt1 o = true ∧ receipt0 o = false} :=
    (hm1 (measurableSet_singleton true)).inter (hm0 (measurableSet_singleton false))
  have hite : Measurable (fun o : FullData =>
      if o ∈ {o : FullData | receipt1 o = true ∧ receipt0 o = false} then (1 : ℝ) else 0) :=
    measurable_const.ite hs measurable_const
  convert hite using 1
  funext o
  simp [complier]

-- @node: targetCACE_mem_parameterSpace
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hP,hfirst), [the stated result about target cace mem parameter space holds](goal). -/
lemma targetCACE_mem_parameterSpace (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hP : ModelClass c_f C_f L P n)
    (hfirst : firstStage P = targetComplierShare P) :
    targetCACE P ∈ parameterSpace := by
  let μ := populationLaw P false
  haveI : IsProbabilityMeasure P.fullLaw := hP.sourceBounds.2.2.1
  haveI : IsFiniteMeasure μ := by
    dsimp [μ, populationLaw]
    infer_instance
  have hsupport : ∀ᵐ o ∂μ,
      outcome0 o ∈ Set.Icc (0 : ℝ) 1 ∧ outcome1 o ∈ Set.Icc (0 : ℝ) 1 := by
    apply (ProbabilityTheory.cond_absolutelyContinuous :
      μ.AbsolutelyContinuous P.fullLaw).ae_le
    filter_upwards [hP.sourceBounds.2.2.2.1] with o ho
    exact ⟨ho.2.1, ho.2.2⟩
  have hcomp : Integrable complier μ := by
    apply Integrable.of_bound measurable_complier.aestronglyMeasurable 1
    filter_upwards [] with o
    simp only [complier]
    split_ifs <;> norm_num
  have hnum : Integrable (fun o => (outcome1 o - outcome0 o) * complier o) μ := by
    have hm : Measurable (fun o : FullData => (outcome1 o - outcome0 o) * complier o) := by
      have hm0 : Measurable (outcome0 : FullData → ℝ) := by unfold outcome0; fun_prop
      have hm1 : Measurable (outcome1 : FullData → ℝ) := by unfold outcome1; fun_prop
      exact (hm1.sub hm0).mul measurable_complier
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    filter_upwards [hsupport] with o ho
    rcases ho with ⟨h0, h1⟩
    simp only [complier]
    split_ifs
    · simpa using abs_le.mpr (show -(1 : ℝ) ≤ outcome1 o - outcome0 o ∧
          outcome1 o - outcome0 o ≤ 1 by constructor <;> linarith [h0.1, h0.2, h1.1, h1.2])
    · norm_num
  have hbound : (∀ᵐ o ∂μ, -complier o ≤ (outcome1 o - outcome0 o) * complier o) ∧
      (∀ᵐ o ∂μ, (outcome1 o - outcome0 o) * complier o ≤ complier o) := by
    have hb : ∀ᵐ o ∂μ, -complier o ≤ (outcome1 o - outcome0 o) * complier o ∧
        (outcome1 o - outcome0 o) * complier o ≤ complier o := by
      filter_upwards [hsupport] with o ho
      rcases ho with ⟨h0, h1⟩
      simp only [complier]
      split_ifs <;> simp_all <;> constructor <;> nlinarith [h0.1, h0.2, h1.1, h1.2]
    exact ⟨hb.mono (fun _ h => h.1), hb.mono (fun _ h => h.2)⟩
  have hlo := integral_mono_ae hcomp.neg hnum hbound.1
  have hhi := integral_mono_ae hnum hcomp hbound.2
  have hpos : 0 < targetComplierShare P := by
    rw [← hfirst]
    exact hP.strength
  rw [parameterSpace, Set.mem_Icc, targetCACE]
  rw [← integral_complier_eq_targetComplierShare P] at hpos ⊢
  constructor
  · apply (le_div_iff₀ hpos).2
    change (∫ x, -complier x ∂μ) ≤ _ at hlo
    rw [integral_neg] at hlo
    simpa using hlo
  · apply (div_le_iff₀ hpos).2
    simpa using hhi

-- @node: target_integral_eq_density_integral
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hP,f), [the stated result about target integral eq density integral holds](goal). -/
lemma target_integral_eq_density_integral (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hP : ModelClass c_f C_f L P n)
    (f : ℝ → ℝ) :
    (∫ x, f x ∂targetXLaw P) =
      ∫ x in covariateSpace, P.fT x * f x := by
  have hcont : ContinuousOn P.fT covariateSpace := by
    have hcd := hP.targetHolder.2.1.continuousOn
    have hmap : ContinuousOn (fun x : ℝ => ![x]) covariateSpace := by fun_prop
    have hmaps : MapsTo (fun x : ℝ => ![x]) covariateSpace
        {v : Fin 1 → ℝ | v 0 ∈ covariateSpace} := by
      intro x hx
      simpa using hx
    simpa [Function.comp_def, Matrix.cons_val_zero] using hcd.comp hmap hmaps
  have hae : AEMeasurable (fun x : ℝ => ENNReal.ofReal (P.fT x))
      (volume.restrict covariateSpace) :=
    (hcont.aemeasurable measurableSet_Icc).ennreal_ofReal
  have hfinite : ∀ᵐ x ∂volume.restrict covariateSpace,
      ENNReal.ofReal (P.fT x) < ⊤ := by filter_upwards [] with x; simp
  have hden := integral_withDensity_eq_integral_toReal_smul₀
    (f := fun x : ℝ => ENNReal.ofReal (P.fT x)) hae hfinite f
  rw [hP.targetBounds.1]
  rw [hden]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  simp [ENNReal.toReal_ofReal
      (le_trans hP.sourceBounds.1.1.le (hP.targetBounds.2.1 x hx).1)]

-- @node: source_setIntegral_eq_density_integral
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hP,B,hB,hsub,f), [the stated result about source set integral eq density integral holds](goal). -/
lemma source_setIntegral_eq_density_integral (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hP : ModelClass c_f C_f L P n)
    (B : Set ℝ) (hB : MeasurableSet B) (hsub : B ⊆ covariateSpace)
    (f : ℝ → ℝ) :
    (∫ x in B, f x ∂sourceXLaw P) =
      ∫ x in B, P.fS x * f x := by
  have hcont : ContinuousOn P.fS covariateSpace := by
    have hcd := hP.sourceHolder.2.1.continuousOn
    have hmap : ContinuousOn (fun x : ℝ => ![x]) covariateSpace := by fun_prop
    have hmaps : MapsTo (fun x : ℝ => ![x]) covariateSpace
        {v : Fin 1 → ℝ | v 0 ∈ covariateSpace} := by
      intro x hx
      simpa using hx
    simpa [Function.comp_def, Matrix.cons_val_zero] using hcd.comp hmap hmaps
  have hae : AEMeasurable (fun x : ℝ => ENNReal.ofReal (P.fS x))
      ((volume.restrict covariateSpace).restrict B) :=
    (hcont.aemeasurable measurableSet_Icc).ennreal_ofReal.restrict
  have hfinite : ∀ᵐ x ∂(volume.restrict covariateSpace).restrict B,
      ENNReal.ofReal (P.fS x) < ⊤ := by filter_upwards [] with x; simp
  have hden := setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    (f := fun x : ℝ => ENNReal.ofReal (P.fS x))
    (s := B) hae hfinite f hB
  rw [hP.sourceBounds.2.2.2.2.1]
  calc
    _ = ∫ x in B, (ENNReal.ofReal (P.fS x)).toReal • f x ∂volume := by
      simpa only [Measure.restrict_restrict_of_subset hsub] using hden
    _ = _ := by
      apply setIntegral_congr_fun hB
      intro x hx
      simp [ENNReal.toReal_ofReal
        (le_trans hP.sourceBounds.1.1.le
          (hP.sourceBounds.2.2.2.2.2 x (hsub hx)).1)]

-- @node: assignment_slice_eq_withDensity
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hP,z), [the stated result about assignment slice eq with density holds](goal). -/
lemma assignment_slice_eq_withDensity (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hP : ModelClass c_f C_f L P n) (z : Bool) :
    (P.assignedLaw.restrict {o : Assigned | o.2.1 = z}).map Prod.fst =
      (populationLaw P true).withDensity
        (fun o => ENNReal.ofReal (assignmentMass P z (covariate o))) := by
  haveI : IsProbabilityMeasure P.assignedLaw := hP.randomized.1
  haveI : IsProbabilityMeasure P.fullLaw := hP.sourceBounds.2.2.1
  haveI : IsFiniteMeasure (populationLaw P true) := by
    refine ⟨?_⟩
    by_cases hp : P.fullLaw {o | population o = true} = 0
    · simp [populationLaw, ProbabilityTheory.cond, hp]
    · simp only [populationLaw, ProbabilityTheory.cond, Measure.coe_smul,
        Pi.smul_apply, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter,
        smul_eq_mul]
      rw [ENNReal.inv_mul_cancel hp (measure_ne_top P.fullLaw _)]
      exact ENNReal.one_lt_top
  have hfst : Measurable (Prod.fst : Assigned → FullData) := by fun_prop
  have hZ : MeasurableSet {o : Assigned | o.2.1 = z} := by measurability
  have hsupport : ∀ᵐ o ∂populationLaw P true, covariate o ∈ covariateSpace := by
    apply (ProbabilityTheory.cond_absolutelyContinuous :
      (populationLaw P true).AbsolutelyContinuous P.fullLaw).ae_le
    exact hP.sourceBounds.2.2.2.1.mono fun _ ho => ho.1
  have hmass : AEMeasurable (fun o : FullData => assignmentMass P z (covariate o))
      (populationLaw P true) := by
    have hcov : Measurable (covariate : FullData → ℝ) := by unfold covariate; fun_prop
    have hsupported : Measurable (fun o : FullData =>
        covariateSpace.indicator (assignmentMass P z) (covariate o)) :=
      (measurable_assignmentMassOnCovariate P z hP.randomized.2.1).comp hcov
    refine hsupported.aemeasurable.congr ?_
    filter_upwards [hsupport] with o ho
    simp [ho]
  have hmass_nonneg : ∀ᵐ o ∂populationLaw P true,
      0 ≤ assignmentMass P z (covariate o) := by
    filter_upwards [hsupport] with o ho
    rcases hP.overlap (covariate o) ho with ⟨he0, he1⟩
    cases z <;> simp [assignmentMass] <;> linarith
  have hmass_le_one : ∀ᵐ o ∂populationLaw P true,
      ENNReal.ofReal (assignmentMass P z (covariate o)) ≤ 1 := by
    filter_upwards [hsupport] with o ho
    rcases hP.overlap (covariate o) ho with ⟨he0, he1⟩
    cases z <;> simp [assignmentMass, ENNReal.ofReal_le_one] <;> linarith
  ext B hB
  have hrhs_ne : ((populationLaw P true).withDensity
      (fun o => ENNReal.ofReal (assignmentMass P z (covariate o))) B) ≠ ⊤ := by
    rw [withDensity_apply _ hB]
    exact ne_of_lt (lt_of_le_of_lt (setLIntegral_le_lintegral _ _)
      (lt_of_le_of_lt (lintegral_mono_ae hmass_le_one) (by simp)))
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) hrhs_ne).mp
  rw [Measure.map_apply hfst hB, Measure.restrict_apply (hB.preimage hfst)]
  have hden := setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    (μ := populationLaw P true)
    (f := fun o : FullData => ENNReal.ofReal (assignmentMass P z (covariate o)))
    (s := B) hmass.ennreal_ofReal.restrict (by simp) (fun _ => (1 : ℝ)) hB
  calc
    (P.assignedLaw (Prod.fst ⁻¹' B ∩ {o : Assigned | o.2.1 = z})).toReal =
        ∫ o in B, assignmentMass P z (covariate o) ∂populationLaw P true := by
      have hevent : Prod.fst ⁻¹' B ∩ {o : Assigned | o.2.1 = z} =
          {o : Assigned | o.1 ∈ B ∧ o.2.1 = z} := by
        ext o
        simp
      rw [hevent]
      exact hP.randomized.2.2.2 B hB z
    _ = ∫ o in B,
        (ENNReal.ofReal (assignmentMass P z (covariate o))).toReal • (1 : ℝ)
          ∂populationLaw P true := by
      refine setIntegral_congr_ae hB ?_
      filter_upwards [hmass_nonneg] with o ho
      simp [ENNReal.toReal_ofReal ho]
    _ = ∫ o in B, (1 : ℝ) ∂
        (populationLaw P true).withDensity
          (fun o => ENNReal.ofReal (assignmentMass P z (covariate o))) := hden.symm
    _ = (((populationLaw P true).withDensity
        (fun o => ENNReal.ofReal (assignmentMass P z (covariate o)))) B).toReal := by
      simp [Measure.real]

-- @node: assignment_slice_integral_eq
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hP,z,f,hf), [the stated result about assignment slice integral eq holds](goal). -/
lemma assignment_slice_integral_eq (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hP : ModelClass c_f C_f L P n) (z : Bool)
    (f : FullData → ℝ) (hf : AEStronglyMeasurable f (populationLaw P true)) :
    (∫ a, f a.1 ∂P.assignedLaw.restrict {a : Assigned | a.2.1 = z}) =
      ∫ o, assignmentMass P z (covariate o) * f o ∂populationLaw P true := by
  have hfst : Measurable (Prod.fst : Assigned → FullData) := by fun_prop
  have hsupport : ∀ᵐ o ∂populationLaw P true, covariate o ∈ covariateSpace := by
    apply (ProbabilityTheory.cond_absolutelyContinuous :
      (populationLaw P true).AbsolutelyContinuous P.fullLaw).ae_le
    exact hP.sourceBounds.2.2.2.1.mono fun _ ho => ho.1
  have hmass : AEMeasurable (fun o : FullData => assignmentMass P z (covariate o))
      (populationLaw P true) := by
    have hcov : Measurable (covariate : FullData → ℝ) := by unfold covariate; fun_prop
    have hsupported : Measurable (fun o : FullData =>
        covariateSpace.indicator (assignmentMass P z) (covariate o)) :=
      (measurable_assignmentMassOnCovariate P z hP.randomized.2.1).comp hcov
    refine hsupported.aemeasurable.congr ?_
    filter_upwards [hsupport] with o ho
    simp [ho]
  have hmass_nonneg : ∀ᵐ o ∂populationLaw P true,
      0 ≤ assignmentMass P z (covariate o) := by
    filter_upwards [hsupport] with o ho
    rcases hP.overlap (covariate o) ho with ⟨he0, he1⟩
    cases z <;> simp [assignmentMass] <;> linarith
  have hden := integral_withDensity_eq_integral_toReal_smul₀
    (μ := populationLaw P true)
    (f := fun o : FullData => ENNReal.ofReal (assignmentMass P z (covariate o)))
    hmass.ennreal_ofReal (by simp) f
  have hfmap : AEStronglyMeasurable f
      ((P.assignedLaw.restrict {a : Assigned | a.2.1 = z}).map Prod.fst) := by
    rw [assignment_slice_eq_withDensity c_f C_f L P n hP z]
    exact AEStronglyMeasurable.mono_ac (withDensity_absolutelyContinuous _ _) hf
  calc
    (∫ a, f a.1 ∂P.assignedLaw.restrict {a : Assigned | a.2.1 = z}) =
        ∫ o, f o ∂(P.assignedLaw.restrict {a : Assigned | a.2.1 = z}).map Prod.fst :=
      (integral_map hfst.aemeasurable hfmap).symm
    _ = ∫ o, f o ∂(populationLaw P true).withDensity
        (fun o => ENNReal.ofReal (assignmentMass P z (covariate o))) := by
      rw [assignment_slice_eq_withDensity c_f C_f L P n hP z]
    _ = ∫ o, (ENNReal.ofReal (assignmentMass P z (covariate o))).toReal • f o
        ∂populationLaw P true := hden
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hmass_nonneg] with o ho
      simp [ENNReal.toReal_ofReal ho]
/-- [The potential arm value object](goal) is defined from [the supplied inputs](hyp:A,z,o). -/

def potentialArmValue (A z : Bool) (o : FullData) : ℝ :=
  if A then potentialOutcome o (potentialReceipt o z)
  else boolReal (potentialReceipt o z)

-- @node: observed_armValue_eq_potentialArmValue
/-- Given [the supplied inputs](hyp:P,A,z,hreceipt,houtcome), [the stated result about observed arm value eq potential arm value holds](goal). -/
lemma observed_armValue_eq_potentialArmValue (P : TransportLaw) (A z : Bool)
    (hreceipt : ReceiptConsistency P) (houtcome : OutcomeConsistency P) :
    (fun a : Assigned => armValue A (observeSource a)) =ᵐ[
      P.assignedLaw.restrict {a : Assigned | a.2.1 = z}]
      fun a => potentialArmValue A z a.1 := by
  have hZ : MeasurableSet {a : Assigned | a.2.1 = z} := by measurability
  filter_upwards [ae_restrict_of_ae hreceipt, ae_restrict_of_ae houtcome.1,
    ae_restrict_mem hZ] with a hD hY hz
  cases A <;> simp [armValue, observeSource, potentialArmValue, hD, hY, hz]

-- @node: source_arm_potential_integral
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hP,A,z,B,hB,hsub), [the stated result about source arm potential integral holds](goal). -/
lemma source_arm_potential_integral (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hP : ModelClass c_f C_f L P n)
    (A z : Bool) (B : Set ℝ) (hB : MeasurableSet B) (hsub : B ⊆ covariateSpace) :
    (∫ x in B, P.fS x * assignmentMass P z x * P.m A z x) =
      ∫ o in {o : FullData | covariate o ∈ B},
        assignmentMass P z (covariate o) * potentialArmValue A z o
          ∂populationLaw P true := by
  let Sobs : Set SourceObs := {o | o.1 ∈ B}
  let Sfull : Set Assigned := {a | covariate a.1 ∈ B}
  let Z : Set Assigned := {a | a.2.1 = z}
  let f : FullData → ℝ := potentialArmValue A z
  have hSobs : MeasurableSet Sobs := by dsimp [Sobs]; measurability
  have hSfull : MeasurableSet Sfull := by
    dsimp [Sfull]
    have hcov : Measurable (covariate : FullData → ℝ) := by unfold covariate; fun_prop
    exact hB.preimage (hcov.comp (by fun_prop))
  have hZ : MeasurableSet Z := by dsimp [Z]; measurability
  have hobs : Measurable (observeSource : Assigned → SourceObs) := by
    unfold observeSource covariate
    fun_prop
  have hmark : AEStronglyMeasurable
      (fun o : SourceObs => (if o.2.1 = z then (1 : ℝ) else 0) * armValue A o)
      (sourceObsLaw P) := by
    apply Measurable.aestronglyMeasurable
    have hZobs : MeasurableSet {o : SourceObs | o.2.1 = z} := by measurability
    have hmz : Measurable (fun o : SourceObs => if o.2.1 = z then (1 : ℝ) else 0) :=
      measurable_const.ite hZobs measurable_const
    have hmarm : Measurable (armValue A) := by
      cases A
      · change Measurable (fun o : SourceObs => boolReal o.2.2.1)
        exact (measurable_of_finite boolReal).comp (by fun_prop)
      · change Measurable (fun o : SourceObs => o.2.2.2)
        fun_prop
    exact hmz.mul hmarm
  have hf : Measurable f := by
    have hr0 : Measurable (receipt0 : FullData → Bool) := by unfold receipt0; fun_prop
    have hr1 : Measurable (receipt1 : FullData → Bool) := by unfold receipt1; fun_prop
    have hy0 : Measurable (outcome0 : FullData → ℝ) := by unfold outcome0; fun_prop
    have hy1 : Measurable (outcome1 : FullData → ℝ) := by unfold outcome1; fun_prop
    have hbool : Measurable (boolReal : Bool → ℝ) := measurable_of_finite _
    cases A <;> cases z
    · change Measurable (fun o => boolReal (receipt0 o))
      exact hbool.comp hr0
    · change Measurable (fun o => boolReal (receipt1 o))
      exact hbool.comp hr1
    · change Measurable (fun o => if receipt0 o then outcome1 o else outcome0 o)
      exact hy1.ite (hr0 (measurableSet_singleton true)) hy0
    · change Measurable (fun o => if receipt1 o then outcome1 o else outcome0 o)
      exact hy1.ite (hr1 (measurableSet_singleton true)) hy0
  have hcons := observed_armValue_eq_potentialArmValue P A z hP.receipt hP.outcome
  have hcons_ind : Z.indicator (fun a : Assigned => armValue A (observeSource a)) =ᵐ[
      P.assignedLaw] Z.indicator (fun a => f a.1) := by
    exact (ae_eq_restrict_iff_indicator_ae_eq hZ).mp (by simpa [Z, f] using hcons)
  have hassigned :
      (∫ a in Sfull,
        (if a.2.1 = z then (1 : ℝ) else 0) * armValue A (observeSource a)
          ∂P.assignedLaw) =
        ∫ a, Sfull.indicator (fun a => f a.1) a ∂P.assignedLaw.restrict Z := by
    rw [← integral_indicator hSfull, ← integral_indicator hZ]
    apply integral_congr_ae
    filter_upwards [hcons_ind] with a ha
    calc
      Sfull.indicator
          (fun a : Assigned => (if a.2.1 = z then (1 : ℝ) else 0) *
            armValue A (observeSource a)) a =
          Sfull.indicator (Z.indicator (fun a => armValue A (observeSource a))) a := by
        by_cases hSa : a ∈ Sfull
        · by_cases hZa : a ∈ Z
          · have hz : a.2.1 = z := by simpa [Z] using hZa
            simp [Set.indicator, hSa, hZa, hz]
          · have hz : a.2.1 ≠ z := by simpa [Z] using hZa
            simp [Set.indicator, hSa, hZa, hz]
        · simp [Set.indicator, hSa]
      _ = Sfull.indicator (Z.indicator (fun a => f a.1)) a := by
        by_cases hSa : a ∈ Sfull
        · simpa [Set.indicator, hSa] using ha
        · simp [Set.indicator, hSa]
      _ = Z.indicator (Sfull.indicator (fun a => f a.1)) a := by
        by_cases hSa : a ∈ Sfull <;> by_cases hZa : a ∈ Z <;>
          simp [Set.indicator, hSa, hZa]
  calc
    (∫ x in B, P.fS x * assignmentMass P z x * P.m A z x) =
        ∫ o in Sobs,
          (if o.2.1 = z then (1 : ℝ) else 0) * armValue A o ∂sourceObsLaw P :=
      source_marked_arm_density c_f C_f L P n hP A z B hB hsub
    _ = ∫ a in Sfull,
        (if a.2.1 = z then (1 : ℝ) else 0) * armValue A (observeSource a)
          ∂P.assignedLaw := by
      rw [sourceObsLaw]
      simpa [Sobs, Sfull, observeSource] using
        setIntegral_map hSobs hmark hobs.aemeasurable
    _ = ∫ a, Sfull.indicator (fun a => f a.1) a
          ∂P.assignedLaw.restrict Z := hassigned
    _ = ∫ a, ({o : FullData | covariate o ∈ B}.indicator f) a.1
          ∂P.assignedLaw.restrict Z := by
      apply integral_congr_ae
      filter_upwards [] with a
      by_cases ha : covariate a.1 ∈ B <;> simp [Sfull, Set.indicator, ha]
    _ = ∫ o, assignmentMass P z (covariate o) *
          ({o : FullData | covariate o ∈ B}.indicator f) o
          ∂populationLaw P true := by
      simpa [Z] using assignment_slice_integral_eq c_f C_f L P n hP z
        ({o : FullData | covariate o ∈ B}.indicator f)
        ((hf.indicator (hB.preimage (by unfold covariate; fun_prop))).aestronglyMeasurable)
    _ = ∫ o, {o : FullData | covariate o ∈ B}.indicator
          (fun o => assignmentMass P z (covariate o) * potentialArmValue A z o) o
          ∂populationLaw P true := by
      apply integral_congr_ae
      filter_upwards [] with o
      by_cases ho : covariate o ∈ B <;> simp [Set.indicator, ho, f]
    _ = _ := integral_indicator (hB.preimage (by unfold covariate; fun_prop))

-- @node: measurable_ae_eq_of_forall_setIntegral_eq
/-- Given [the supplied inputs](hyp:α,f,g,hf,hg,hfg), [the stated result about measurable ae eq of forall set integral eq holds](goal). -/
lemma measurable_ae_eq_of_forall_setIntegral_eq {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f g : α → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ B : Set α, MeasurableSet B →
      ∫ x in B, f x ∂μ = ∫ x in B, g x ∂μ) :
    f =ᵐ[μ] g := by
  let E : ℕ → Set α := fun k => {x | |f x| ≤ k ∧ |g x| ≤ k}
  have hE : ∀ k, MeasurableSet (E k) := by
    intro k
    exact (measurableSet_Iic.preimage (continuous_abs.measurable.comp hf)).inter
      (measurableSet_Iic.preimage (continuous_abs.measurable.comp hg))
  have hUnion : ⋃ k, E k = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨kf, hkf⟩ := exists_nat_ge |f x|
    obtain ⟨kg, hkg⟩ := exists_nat_ge |g x|
    exact ⟨max kf kg, hkf.trans (by exact_mod_cast le_max_left kf kg),
      hkg.trans (by exact_mod_cast le_max_right kf kg)⟩
  have hlocal : ∀ k, f =ᵐ[μ.restrict (E k)] g := by
    intro k
    have hfint : Integrable f (μ.restrict (E k)) := by
      apply Integrable.of_bound hf.aestronglyMeasurable.restrict k
      filter_upwards [ae_restrict_mem (hE k)] with x hx
      exact hx.1
    have hgint : Integrable g (μ.restrict (E k)) := by
      apply Integrable.of_bound hg.aestronglyMeasurable.restrict k
      filter_upwards [ae_restrict_mem (hE k)] with x hx
      exact hx.2
    apply hfint.ae_eq_of_forall_setIntegral_eq f g hgint
    intro B hB _
    simpa only [Measure.restrict_restrict hB] using
      hfg (B ∩ E k) (hB.inter (hE k))
  have hu : f =ᵐ[μ.restrict (⋃ k, E k)] g :=
    (ae_eq_restrict_iUnion_iff E f g).2 hlocal
  simpa [hUnion] using hu

-- @node: target_absolutelyContinuous_source
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hP), [the stated result about target absolutely continuous source holds](goal). -/
lemma target_absolutelyContinuous_source (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hP : ModelClass c_f C_f L P n) :
    targetXLaw P ≪ sourceXLaw P := by
  let μ := volume.restrict covariateSpace
  have hcontS : ContinuousOn P.fS covariateSpace := by
    have hcd := hP.sourceHolder.2.1.continuousOn
    have hmap : ContinuousOn (fun x : ℝ => ![x]) covariateSpace := by fun_prop
    have hmaps : MapsTo (fun x : ℝ => ![x]) covariateSpace
        {v : Fin 1 → ℝ | v 0 ∈ covariateSpace} := by
      intro x hx
      simpa using hx
    simpa [Function.comp_def, Matrix.cons_val_zero] using hcd.comp hmap hmaps
  have hmeasS : AEMeasurable (fun x => ENNReal.ofReal (P.fS x)) μ :=
    (hcontS.aemeasurable measurableSet_Icc).ennreal_ofReal
  have hnonzeroS : ∀ᵐ x ∂μ, ENNReal.ofReal (P.fS x) ≠ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact ne_of_gt (ENNReal.ofReal_pos.2 (lt_of_lt_of_le hP.sourceBounds.1.1
      (hP.sourceBounds.2.2.2.2.2 x hx).1))
  rw [hP.targetBounds.1, hP.sourceBounds.2.2.2.2.1]
  exact (withDensity_absolutelyContinuous μ _).trans
    (withDensity_absolutelyContinuous' hmeasS hnonzeroS)
/-- [The arm mean version object](goal) is defined from [the supplied inputs](hyp:P,A,z). -/

noncomputable def armMeanVersion (P : TransportLaw) (A z : Bool) : ℝ → ℝ :=
  covariateSpace.indicator (P.m A z)

-- @node: armMeanVersion_measurable
/-- Given [the supplied inputs](hyp:L,P,hP,A,z), [the stated result about arm mean version measurable holds](goal). -/
lemma armMeanVersion_measurable (L : ℝ) (P : TransportLaw)
    (hP : ArmMeansHolder L P) (A z : Bool) :
    Measurable (armMeanVersion P A z) := by
  exact hP.2.1 A z |>.2.1

-- @node: armMeanVersion_ae_eq
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hP,A,z), [the stated result about arm mean version ae eq holds](goal). -/
lemma armMeanVersion_ae_eq (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hP : ModelClass c_f C_f L P n) (A z : Bool) :
    armMeanVersion P A z =ᵐ[sourceXLaw P] P.m A z := by
  have hsupp : ∀ᵐ x ∂sourceXLaw P, x ∈ covariateSpace := by
    rw [hP.sourceBounds.2.2.2.2.1]
    exact (withDensity_absolutelyContinuous _ _).ae_le
      (ae_restrict_mem measurableSet_Icc)
  filter_upwards [hsupp] with x hx
  simp [armMeanVersion, Set.indicator_of_mem hx]

end CausalSmith.Stat.TransportCaceRoughnuisanceLength

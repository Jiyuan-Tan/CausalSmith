module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Basic
public import Mathlib.Topology.Order.ProjIcc

/-! Finite-stratum normalization and the schedule/dose product law used in the
realized-dose argument. These results use whole-schedule exchangeability. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
variable {S : Type*} [MeasurableSpace S]

/-- Each positive stratum carries a normalized probability law. [Under the stated conditions](hyp:hoverlap). [This is the stated conclusion](goal). -/
-- @node: stratumLaw_probability
lemma stratumLaw_probability (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    (hoverlap : StratumPositive P) (x : Bool) : IsProbabilityMeasure (stratumLaw P x) := by
  have hp : P {w | sX w = x} ≠ 0 := by
    intro h
    have := hoverlap x
    simp [strataProb, Measure.real, h] at this
  constructor
  simp only [stratumLaw, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hp (measure_ne_top _ _)

/-- Stratum restriction divides real event masses by the positive stratum mass. [This is the stated conclusion](goal). -/
-- @node: stratumLaw_real_apply
lemma stratumLaw_real_apply (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    (x : Bool) (B : Set (StructSpace S)) :
    (stratumLaw P x).real B = P.real (B ∩ {w | sX w = x}) / strataProb P x := by
  have hx : MeasurableSet {w : StructSpace S | sX w = x} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  unfold stratumLaw
  rw [measureReal_ennreal_smul_apply, ENNReal.toReal_inv, measureReal_restrict_apply' hx]
  simp only [strataProb, Measure.real, div_eq_mul_inv, mul_comm]

/-- Whole-schedule exchangeability becomes ordinary independence in each stratum. [Under the stated conditions](hyp:hoverlap,hex). [This is the stated conclusion](goal). -/
-- @node: schedule_dose_indep_stratum
lemma schedule_dose_indep_stratum (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    (hoverlap : StratumPositive P) (hex : ScheduleUnconfoundedness P) (x : Bool) :
    IndepFun sSched sA (stratumLaw P x) := by
  have :=  stratumLaw_probability P hoverlap x
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro B D hB hD
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).mp
  rw [ENNReal.toReal_mul]
  change (stratumLaw P x).real (sSched ⁻¹' B ∩ sA ⁻¹' D) =
    (stratumLaw P x).real (sSched ⁻¹' B) * (stratumLaw P x).real (sA ⁻¹' D)
  rw [stratumLaw_real_apply, stratumLaw_real_apply, stratumLaw_real_apply]
  have hp : strataProb P x ≠ 0 := (hoverlap x).ne'
  have h := hex x B D hB hD
  have hset : (sSched ⁻¹' B ∩ sA ⁻¹' D) ∩ {w : StructSpace S | sX w = x} =
      {w | sSched w ∈ B ∧ sA w ∈ D ∧ sX w = x} := by
    ext w; simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]; tauto
  rw [hset]
  change P.real {w | sSched w ∈ B ∧ sA w ∈ D ∧ sX w = x} / strataProb P x =
    (P.real {w | sSched w ∈ B ∧ sX w = x} / strataProb P x) *
      (P.real {w | sA w ∈ D ∧ sX w = x} / strataProb P x)
  field_simp
  exact h

/-- The conditional joint schedule/dose law is the product of its marginals. [Under the stated conditions](hyp:hoverlap,hex). [This is the stated conclusion](goal). -/
-- @node: schedule_dose_product_stratum
lemma schedule_dose_product_stratum (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    (hoverlap : StratumPositive P) (hex : ScheduleUnconfoundedness P) (x : Bool) :
    (stratumLaw P x).map (fun w => (sSched w, sA w)) =
      ((stratumLaw P x).map sSched).prod ((stratumLaw P x).map sA) := by
  have :=  stratumLaw_probability P hoverlap x
  exact (schedule_dose_indep_stratum P hoverlap hex x).map_prod_eq_prod_map_map
    (by fun_prop) (by fun_prop)

/-- Error independence survives positive-stratum restriction, with its marginal unchanged. [Under the stated conditions](hyp:hoverlap,herr). [This is the stated conclusion](goal). -/
-- @node: error_scheduleDose_product_stratum
lemma error_scheduleDose_product_stratum (P : Measure (StructSpace S))
    [IsProbabilityMeasure P] (hoverlap : StratumPositive P)
    (herr : ErrorIndependence P) (x : Bool) :
    (stratumLaw P x).map (fun w => (sZ w, sA w, sSched w)) =
      (P.map sZ).prod ((stratumLaw P x).map (fun w => (sA w, sSched w))) := by
  have := stratumLaw_probability P hoverlap x
  have hZ : Measurable (sZ (S := S)) := by fun_prop
  have hAS : Measurable (fun w : StructSpace S => (sA w, sSched w)) := by fun_prop
  have hx : MeasurableSet {w : StructSpace S | sX w = x} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  apply Measure.ext_prod
  intro B D hB hD
  let C : Set (Bool × ℝ × S) := {p | p.1 = x ∧ p.2 ∈ D}
  have hC : MeasurableSet C :=
    (measurableSet_eq_fun measurable_fst measurable_const).inter
      (measurable_snd hD)
  have hfactor := herr.measure_inter_preimage_eq_mul B C hB hC
  rw [Measure.map_apply (hZ.prodMk hAS) (hB.prod hD), Measure.prod_prod,
    Measure.map_apply hZ hB, Measure.map_apply hAS hD]
  simp only [stratumLaw, Measure.smul_apply, Measure.restrict_apply' hx, smul_eq_mul]
  have hevent : (fun w : StructSpace S => (sZ w, sA w, sSched w)) ⁻¹' (B ×ˢ D) ∩
      {w | sX w = x} = sZ ⁻¹' B ∩ (fun w => (sX w, sA w, sSched w)) ⁻¹' C := by
    ext w; simp only [C, mem_inter_iff, mem_preimage, mem_prod, mem_ofPred_eq]; tauto
  have hright : (fun w : StructSpace S => (sA w, sSched w)) ⁻¹' D ∩
      {w | sX w = x} = (fun w => (sX w, sA w, sSched w)) ⁻¹' C := by
    ext w; simp only [C, mem_inter_iff, mem_preimage, mem_ofPred_eq]; tauto
  rw [hevent, hright, hfactor]
  ac_rfl

/-- The schedule, dose, and Gaussian error have the conditional product law in equation (1). [Under the stated conditions](hyp:hoverlap,hex,herr). [This is the stated conclusion](goal). -/
-- @node: schedule_dose_error_product_stratum
lemma schedule_dose_error_product_stratum (P : Measure (StructSpace S))
    [IsProbabilityMeasure P] (hoverlap : StratumPositive P)
    (hex : ScheduleUnconfoundedness P) (herr : ErrorIndependence P) (x : Bool) :
    (stratumLaw P x).map (fun w => (sZ w, sA w, sSched w)) =
      (P.map sZ).prod (((stratumLaw P x).map sA).prod
        ((stratumLaw P x).map sSched)) := by
  rw [error_scheduleDose_product_stratum P hoverlap herr x]
  have := stratumLaw_probability P hoverlap x
  rw [(schedule_dose_indep_stratum P hoverlap hex x).symm.map_prod_eq_prod_map_map
    (by fun_prop) (by fun_prop)]

/-- An almost-everywhere assertion under the population law holds in each stratum. [Under the stated condition](hyp:hp). [This is the stated conclusion](goal). -/
-- @node: ae_stratumLaw_of_ae
lemma ae_stratumLaw_of_ae (P : Measure (StructSpace S)) (x : Bool)
    {p : StructSpace S → Prop} (hp : ∀ᵐ w ∂P, p w) :
    ∀ᵐ w ∂stratumLaw P x, p w :=
  Measure.ae_smul_measure (ae_restrict_of_ae hp) _

/-- The two positive strata suffice to recover a population almost-everywhere assertion. [Under the stated conditions](hyp:hp). [This is the stated conclusion](goal). -/
-- @node: ae_of_ae_stratumLaw
lemma ae_of_ae_stratumLaw (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    {p : StructSpace S → Prop}
    (hp : ∀ x, ∀ᵐ w ∂stratumLaw P x, p w) : ∀ᵐ w ∂P, p w := by
  have hrestrict (x : Bool) : ∀ᵐ w ∂P.restrict {w | sX w = x}, p w := by
    have hs := hp x
    change ∀ᵐ w ∂(P {w | sX w = x})⁻¹ • P.restrict {w | sX w = x}, p w at hs
    rw [ae_iff] at hs ⊢
    simpa only [Measure.smul_apply, smul_eq_mul, mul_eq_zero,
      ENNReal.inv_eq_zero, measure_ne_top P _, false_or] using hs
  have hc : {w : StructSpace S | sX w = false}ᶜ = {w | sX w = true} := by
    ext w; cases sX w <;> simp
  apply ae_of_ae_restrict_of_ae_restrict_compl {w | sX w = false} (hrestrict false)
  simpa only [hc] using hrestrict true

/-- Whole-schedule exchangeability integrates fixed-dose exceptional sets at the random dose. [Under the stated conditions](hyp:hoverlap,hex,hsupport,hbounded). [This is the stated conclusion](goal). -/
-- @node: realized_potential_mem_Icc
lemma realized_potential_mem_Icc (E : PathSpace S) (P : Measure (StructSpace S))
    [IsProbabilityMeasure P] (hoverlap : StratumPositive P)
    (hex : ScheduleUnconfoundedness P) (hsupport : LatentSupport P)
    (hbounded : BoundedPotentialOutcomes E P) :
    ∀ᵐ w ∂P, potentialOutcome E w (sA w) ∈ Icc 0 1 := by
  let ev : ℝ × S → ℝ := fun p => E.eval p.2 (Set.projIcc 0 1 zero_le_one p.1)
  have hev : Measurable ev := by
    first
    | fun_prop
    | exact E.measurable_eval.comp (measurable_snd.prodMk
        ((continuous_projIcc (h := zero_le_one)).measurable.comp measurable_fst))
  apply ae_of_ae_stratumLaw P
  intro x
  let R := stratumLaw P x
  have : IsProbabilityMeasure R := stratumLaw_probability P hoverlap x
  have hA : Measurable (sA (S := S)) := by fun_prop
  have hS : Measurable (sSched (S := S)) := by fun_prop
  have hprod : R.map (fun w => (sA w, sSched w)) =
      (R.map sA).prod (R.map sSched) :=
    (schedule_dose_indep_stratum P hoverlap hex x).symm.map_prod_eq_prod_map_map
      hA.aemeasurable hS.aemeasurable
  have hfixed (a : ℝ) : ∀ᵐ s ∂R.map sSched,
      E.eval s (Set.projIcc 0 1 zero_le_one a) ∈ Icc 0 1 := by
    have hm : Measurable (fun s : S => E.eval s (Set.projIcc 0 1 zero_le_one a)) :=
      E.measurable_eval.comp (measurable_id.prodMk measurable_const)
    apply (ae_map_iff hS.aemeasurable (hm measurableSet_Icc)).mpr
    exact ae_stratumLaw_of_ae P x (hbounded _ (Set.projIcc 0 1 zero_le_one a).property)
  have hgood : ∀ᵐ p ∂(R.map sA).prod (R.map sSched), ev p ∈ Icc 0 1 := by
    apply (Measure.ae_prod_iff_ae_ae
      (hev measurableSet_Icc)).mpr
    exact ae_of_all _ hfixed
  rw [← hprod] at hgood
  have hrandom : ∀ᵐ w ∂R, ev (sA w, sSched w) ∈ Icc 0 1 :=
    (ae_map_iff (hA.prodMk hS).aemeasurable
      (hev measurableSet_Icc)).mp hgood
  filter_upwards [hrandom, ae_stratumLaw_of_ae P x hsupport] with w hw ha
  simpa only [ev, potentialOutcome, Set.projIcc_of_mem zero_le_one ha] using hw

/-- Consistency transfers the random-evaluation bound to the observed outcome. [Under the stated conditions](hyp:hoverlap,hex,hsupport,hbounded,hcons). [This is the stated conclusion](goal). -/
-- @node: realized_outcome_mem_Icc
lemma realized_outcome_mem_Icc (E : PathSpace S) (P : Measure (StructSpace S))
    [IsProbabilityMeasure P] (hoverlap : StratumPositive P)
    (hex : ScheduleUnconfoundedness P) (hsupport : LatentSupport P)
    (hbounded : BoundedPotentialOutcomes E P) (hcons : DoseConsistency E P) :
    ∀ᵐ w ∂P, sY w ∈ Icc 0 1 := by
  filter_upwards [realized_potential_mem_Icc E P hoverlap hex hsupport hbounded, hcons]
    with w hw hc
  rw [hc]
  exact hw

/-- The derived observed-outcome bound supplies integrability without an extra premise. [Under the stated conditions](hyp:hoverlap,hex,hsupport,hbounded,hcons). [This is the stated conclusion](goal). -/
-- @node: realized_outcome_integrable
lemma realized_outcome_integrable (E : PathSpace S) (P : Measure (StructSpace S))
    [IsProbabilityMeasure P] (hoverlap : StratumPositive P)
    (hex : ScheduleUnconfoundedness P) (hsupport : LatentSupport P)
    (hbounded : BoundedPotentialOutcomes E P) (hcons : DoseConsistency E P) :
    Integrable sY P := by
  apply Integrable.of_bound
    (show Measurable (sY (S := S)) by fun_prop).aestronglyMeasurable 1
  filter_upwards [realized_outcome_mem_Icc E P hoverlap hex hsupport hbounded hcons]
    with w hw
  simpa only [Real.norm_eq_abs, abs_of_nonneg hw.1] using hw.2

end CausalSmith.Stat.NoisydoseWeakdesignTransition

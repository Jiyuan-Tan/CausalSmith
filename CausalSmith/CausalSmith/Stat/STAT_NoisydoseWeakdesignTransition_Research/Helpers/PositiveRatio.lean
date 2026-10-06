module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.Estimator
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.RealizedDoseMean
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.Probability.Independence.Integration

/-! Positive inverse-weight population ratios. Integrable signed weights pass through the
realized conditional mean and exact Gaussian inverse; latent density envelopes then give
the public positive denominator and Holder localization bias bounds. -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
variable {S : Type*} [MeasurableSpace S]


/-- Integrable signed dose-stratum-error weights can multiply the realized outcome.
The domination is by the original weight, using the derived outcome range. [Under the stated conditions](hyp:hP,hF,hiF). [This is the stated conclusion](goal). -/
-- @node: integrable_test_outcome
lemma integrable_test_outcome (E : PathSpace S) (beta kappa sigma : ℝ)
    (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    {K : ClassConstants} (hP : NoisyDoseModelClass E K beta kappa sigma P)
    (F : (ℝ × Bool × ℝ) → ℝ) (hF : Measurable F)
    (hiF : Integrable (fun w => F (sA w, sX w, sZ w)) P) :
    Integrable (fun w => F (sA w, sX w, sZ w) * sY w) P := by
  apply hiF.mul_bdd (c := 1) (show Measurable (sY (S := S)) by fun_prop).aestronglyMeasurable
  filter_upwards [realized_outcome_mem_Icc E P hP.strataPos
    hP.scheduleUnconfoundedness hP.latentSupport hP.boundedPO hP.consistency] with w hw
  simpa only [Real.norm_eq_abs, abs_of_nonneg hw.1] using hw.2

/-- The conditional-mean bridge extends to every integrable signed test weight.
The pull-out theorem includes the dominated truncation argument needed for unbounded weights. [Under the stated conditions](hyp:hP,hF,hbeta,hkappa,hsigma,hiF). [This is the stated conclusion](goal). -/
-- @node: integrable_test_mean
lemma integrable_test_mean (E : PathSpace S) (beta kappa sigma : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2)
    (hsigma : sigma ∈ Icc (0 : ℝ) (1/4))
    (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    {K : ClassConstants} (hP : NoisyDoseModelClass E K beta kappa sigma P)
    (F : (ℝ × Bool × ℝ) → ℝ) (hF : Measurable F)
    (hiF : Integrable (fun w => F (sA w, sX w, sZ w)) P) :
    (∫ w, F (sA w, sX w, sZ w) * sY w ∂P) =
      ∫ w, F (sA w, sX w, sZ w) * condPotMean E P (sX w) (sA w) ∂P := by
  have hiY := realized_outcome_integrable E P hP.strataPos
    hP.scheduleUnconfoundedness hP.latentSupport hP.boundedPO hP.consistency
  have hiFY := integrable_test_outcome E beta kappa sigma P hP F hF hiF
  have hm : AEStronglyMeasurable[doseXZSigma]
      (fun w : StructSpace S => F (sA w, sX w, sZ w)) P :=
    (hF.comp (comap_measurable (fun w : StructSpace S => (sA w, sX w, sZ w)))).aestronglyMeasurable
  have hpull := condExp_mul_of_aestronglyMeasurable_left hm hiFY hiY
  have hmean := (realized_dose_mean E beta kappa sigma hbeta hkappa hsigma P hP).2.1
  calc
    _ = ∫ w, P[(fun w => F (sA w, sX w, sZ w) * sY w) | doseXZSigma] w ∂P :=
      (integral_condExp (show doseXZSigma ≤ (inferInstance : MeasurableSpace (StructSpace S)) from
        (show Measurable (fun w : StructSpace S => (sA w, sX w, sZ w)) by fun_prop).comap_le)).symm
    _ = ∫ w, F (sA w, sX w, sZ w) * P[sY | doseXZSigma] w ∂P :=
      integral_congr_ae hpull
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hmean] with w hw
      rw [hw]


/-- The unmarked stratum inverse weight is integrable by restriction of the admissible weight. [Under the stated conditions](hyp:hlaw). [This is the stated conclusion](goal). -/
-- @node: populationD_integrable
lemma populationD_integrable (sigma : ℝ) (P : Measure (StructSpace S))
    (x : Bool) (q : WeightPair) (hlaw : LawAdmissible sigma P q) :
    Integrable (fun w => if sX w = x then q.ell (observedCentered sigma w) else 0) P := by
  have hi : Integrable (fun w => q.ell (observedCentered sigma w)) P := hlaw
  apply (hi.indicator (show MeasurableSet {w : StructSpace S | sX w = x} from
    measurableSet_eq_fun (by fun_prop) measurable_const)).congr
  filter_upwards [] with w
  simp only [Set.indicator_apply, Set.mem_setOf_eq]

/-- The signed inverse-weight numerator is integrable because the realized outcome is bounded. [Under the stated conditions](hyp:hP,hq,hlaw). [This is the stated conclusion](goal). -/
-- @node: populationM_integrable
lemma populationM_integrable (E : PathSpace S) (beta kappa sigma : ℝ)
    (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    {K : ClassConstants} (hP : NoisyDoseModelClass E K beta kappa sigma P)
    (x : Bool) (q : WeightPair) (hq : Measurable q.ell)
    (hlaw : LawAdmissible sigma P q) :
    Integrable (fun w => if sX w = x then sY w * q.ell (observedCentered sigma w) else 0) P := by
  have h := (populationD_integrable sigma P x q hlaw).mul_bdd (c := 1)
    (show Measurable (sY (S := S)) by fun_prop).aestronglyMeasurable
    (show ∀ᵐ w ∂P, ‖sY w‖ ≤ 1 from by
      filter_upwards [realized_outcome_mem_Icc E P hP.strataPos
        hP.scheduleUnconfoundedness hP.latentSupport hP.boundedPO hP.consistency] with w hw
      simpa only [Real.norm_eq_abs, abs_of_nonneg hw.1] using hw.2)
  convert h using 1
  funext w
  split_ifs <;> simp [mul_comm]

/-- The population marked weight equals its conditional-mean weighted counterpart,
including signed unbounded inverse weights. [Under the stated conditions](hyp:hP,hq,hlaw,hbeta,hkappa,hsigma). [This is the stated conclusion](goal). -/
-- @node: populationM_eq_mean
lemma populationM_eq_mean (E : PathSpace S) (beta kappa sigma : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2)
    (hsigma : sigma ∈ Icc (0 : ℝ) (1/4))
    (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    {K : ClassConstants} (hP : NoisyDoseModelClass E K beta kappa sigma P)
    (x : Bool) (q : WeightPair) (hq : Measurable q.ell)
    (hlaw : LawAdmissible sigma P q) :
    populationM sigma P x q =
      ∫ w, (if sX w = x then
        condPotMean E P x (sA w) * q.ell (observedCentered sigma w) else 0) ∂P := by
  let F : (ℝ × Bool × ℝ) → ℝ := fun p =>
    if p.2.1 = x then q.ell (p.1 + sigma * p.2.2 - a0) else 0
  have hF : Measurable F := by
    apply Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
      (hq.comp (by fun_prop)) measurable_const
  have hiF : Integrable (fun w : StructSpace S => F (sA w, sX w, sZ w)) P :=
    populationD_integrable sigma P x q hlaw
  have h := integrable_test_mean E beta kappa sigma hbeta hkappa hsigma P hP F hF hiF
  calc
    _ = ∫ w, F (sA w, sX w, sZ w) * sY w ∂P := by
      apply integral_congr_ae
      filter_upwards [] with w
      dsimp [populationM, F, observedCentered, contaminatedDose]
      split_ifs <;> simp [mul_comm]
    _ = _ := h
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with w
      dsimp [F, observedCentered, contaminatedDose]
      split_ifs with hw
      · rw [hw, mul_comm]
      · simp

/-- Conditioning on a public stratum preserves independence of the centered dose and error. [Under the stated conditions](hyp:hoverlap,herr). [This is the stated conclusion](goal). -/
-- @node: error_centered_product_stratum
lemma error_centered_product_stratum (P : Measure (StructSpace S))
    [IsProbabilityMeasure P] (hoverlap : StratumPositive P)
    (herr : ErrorIndependence P) (x : Bool) :
    (stratumLaw P x).map (fun w => (sZ w, latentCentered w)) =
      (P.map sZ).prod ((stratumLaw P x).map latentCentered) := by
  have := stratumLaw_probability P hoverlap x
  have hZ : Measurable (sZ (S := S)) := by fun_prop
  have hAS : Measurable (fun w : StructSpace S => (sA w, sSched w)) := by fun_prop
  have hcenter : Measurable (fun p : ℝ × S => p.1 - a0) := by fun_prop
  have hp := congrArg (Measure.map (Prod.map (id : ℝ → ℝ) (fun p : ℝ × S => p.1-a0)))
    (error_scheduleDose_product_stratum P hoverlap herr x)
  rw [← Measure.map_prod_map _ _ measurable_id hcenter] at hp
  rw [Measure.map_map (measurable_id.prodMap hcenter) (hZ.prodMk hAS),
    Measure.map_map hcenter hAS, Measure.map_id] at hp
  exact hp

/-- An integrable population weight remains integrable under every positive-mass stratum. [Under the stated conditions](hyp:hoverlap,f,hf). [This is the stated conclusion](goal). -/
-- @node: integrable_stratumLaw
lemma integrable_stratumLaw (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    (hoverlap : StratumPositive P) (x : Bool) (f : StructSpace S → ℝ)
    (hf : Integrable f P) : Integrable f (stratumLaw P x) := by
  have hp : P {w | sX w = x} ≠ 0 := by
    intro hp
    have h := hoverlap x
    simp only [strataProb, Measure.real, hp, ENNReal.toReal_zero] at h
    linarith
  exact hf.restrict.smul_measure (ENNReal.inv_ne_top.mpr hp)

/-- Exact Gaussian inversion turns an integrable signed observed weight into a latent weight,
with any measurable multiplier for which the product is integrable. [Under the stated conditions](hyp:hoverlap,herr,hgauss,hq,hsupport,H,hH,hinverse,hi). [This is the stated conclusion](goal). -/
-- @node: inverse_weight_stratum_integral
lemma inverse_weight_stratum_integral (sigma : ℝ)
    (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    (hoverlap : StratumPositive P) (herr : ErrorIndependence P)
    (hgauss : GaussianChannel P) (x : Bool) (q : WeightPair)
    (hq : Measurable q.ell) (hsupport : LatentSupport P)
    (hinverse : ∀ t ∈ Icc (-1/2 : ℝ) (1/2),
      ∫ z, q.ell (t+sigma*z) ∂gaussianReal 0 1 = q.q t)
    (H : ℝ → ℝ) (hH : Measurable H)
    (hi : Integrable (fun w => H (latentCentered w) * q.ell (observedCentered sigma w)) P) :
    (∫ w, H (latentCentered w) * q.ell (observedCentered sigma w) ∂stratumLaw P x) =
      ∫ t, H t * q.q t ∂(stratumLaw P x).map latentCentered := by
  have := stratumLaw_probability P hoverlap x
  let γ := (stratumLaw P x).map latentCentered
  let G : ℝ × ℝ → ℝ := fun p => H p.2 * q.ell (p.2 + sigma*p.1)
  have hm : Measurable G := by fun_prop
  have hT : Measurable (latentCentered (S := S)) := by unfold latentCentered; fun_prop
  have hZT : Measurable (fun w : StructSpace S => (sZ w, latentCentered w)) := by fun_prop
  have hprod : (stratumLaw P x).map (fun w => (sZ w, latentCentered w)) =
      (gaussianReal 0 1).prod γ := by
    rw [error_centered_product_stratum P hoverlap herr x, hgauss]
  have hiR := integrable_stratumLaw P hoverlap x _ hi
  have hiG : Integrable G ((gaussianReal 0 1).prod γ) := by
    rw [← hprod]
    apply (integrable_map_measure hm.aestronglyMeasurable hZT.aemeasurable).mpr
    apply hiR.congr
    filter_upwards [] with w
    dsimp [G, observedCentered, contaminatedDose, latentCentered]
    congr 2
    ring
  have hsupportT : ∀ᵐ t ∂γ, t ∈ Icc (-1/2 : ℝ) (1/2) := by
    apply (ae_map_iff hT.aemeasurable (by measurability)).mpr
    filter_upwards [ae_stratumLaw_of_ae P x hsupport] with w hw
    dsimp [latentCentered, a0]
    constructor <;> linarith [hw.1, hw.2]
  calc
    _ = ∫ p, G p ∂(gaussianReal 0 1).prod γ := by
      rw [← hprod, integral_map hZT.aemeasurable hm.aestronglyMeasurable]
      apply integral_congr_ae
      filter_upwards [] with w
      dsimp [G, observedCentered, contaminatedDose, latentCentered]
      congr 2
      ring
    _ = ∫ t, ∫ z, G (z,t) ∂gaussianReal 0 1 ∂γ := integral_prod_symm _ hiG
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hsupportT] with t ht
      dsimp [G]
      rw [integral_const_mul, hinverse t ht]

/-- Integrating against the centered conditional density gives the ordinary latent integral. [Under the stated conditions](hyp:g,f,hg,hlaw,henv). [This is the stated conclusion](goal). -/
-- @node: latent_density_integral
lemma latent_density_integral {K : ClassConstants} (kappa : ℝ) (P : Measure (StructSpace S))
    (g : Bool → ℝ → ℝ) (hg : ∀ x, Measurable (g x))
    (hlaw : ∀ x, (stratumLaw P x).map latentCentered =
      (volume.restrict (Icc (-1/2 : ℝ) (1/2))).withDensity (fun t => ENNReal.ofReal (g x t)))
    (henv : ∀ x, ∀ᵐ t ∂volume.restrict (Icc (-1/2 : ℝ) (1/2)),
      K.clo * |t| ^ kappa ≤ g x t ∧ g x t ≤ K.chi * |t| ^ kappa)
    (x : Bool) (f : ℝ → ℝ) :
    (∫ t, f t ∂(stratumLaw P x).map latentCentered) =
      ∫ t in Icc (-1/2 : ℝ) (1/2), g x t * f t := by
  rw [hlaw x, integral_withDensity_eq_integral_toReal_smul
    (hg x).ennreal_ofReal (ae_of_all _ (fun t => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [henv x] with t ht
  have hnonneg : 0 ≤ g x t :=
    (mul_nonneg K.clo_pos.le (Real.rpow_nonneg (abs_nonneg _) _)).trans ht.1
  simp only [ENNReal.toReal_ofReal hnonneg, smul_eq_mul]

/-- The unmarked population inverse moment is the positive latent weighted integral. [Under the stated conditions](hyp:hP,hq,hweight,g,hg,hlaw,henv). [This is the stated conclusion](goal). -/
-- @node: populationD_eq_latent
lemma populationD_eq_latent (E : PathSpace S) (beta kappa sigma : ℝ)
    (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    {K : ClassConstants} (hP : NoisyDoseModelClass E K beta kappa sigma P) (x : Bool) (q : WeightPair)
    (hq : PairAdmissible kappa sigma q) (hweight : LawAdmissible sigma P q)
    (g : Bool → ℝ → ℝ) (hg : ∀ x, Measurable (g x))
    (hlaw : ∀ x, (stratumLaw P x).map latentCentered =
      (volume.restrict (Icc (-1/2 : ℝ) (1/2))).withDensity (fun t => ENNReal.ofReal (g x t)))
    (henv : ∀ x, ∀ᵐ t ∂volume.restrict (Icc (-1/2 : ℝ) (1/2)),
      K.clo * |t| ^ kappa ≤ g x t ∧ g x t ≤ K.chi * |t| ^ kappa) :
    populationD sigma P x q = strataProb P x *
      ∫ t in Icc (-1/2 : ℝ) (1/2), g x t * q.q t := by
  have hi : Integrable (fun w => (1 : ℝ) * q.ell (observedCentered sigma w)) P := by
    simpa only [one_mul] using (show Integrable (fun w => q.ell (observedCentered sigma w)) P from hweight)
  have h := inverse_weight_stratum_integral sigma P hP.strataPos hP.errorIndependence
    hP.gaussianChannel x q hq.2.1 hP.latentSupport hq.2.2.2.2.2.2
    (fun _ => 1) measurable_const hi
  simp only [one_mul] at h
  rw [stratumLaw_integral, latent_density_integral kappa P g hg hlaw henv] at h
  exact (eq_div_iff (strataProb_pos P hP.strataPos x).ne').mp h.symm |>.symm.trans (mul_comm _ _)

/-- The marked population moment is the latent mean-weighted integral from equation (1). [Under the stated conditions](hyp:hP,hq,hweight,g,hbeta,hkappa,hsigma,hg,hlaw,henv). [This is the stated conclusion](goal). -/
-- @node: populationM_eq_latent
lemma populationM_eq_latent (E : PathSpace S) (beta kappa sigma : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2)
    (hsigma : sigma ∈ Icc (0 : ℝ) (1/4))
    (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    {K : ClassConstants} (hP : NoisyDoseModelClass E K beta kappa sigma P) (x : Bool) (q : WeightPair)
    (hq : PairAdmissible kappa sigma q) (hweight : LawAdmissible sigma P q)
    (g : Bool → ℝ → ℝ) (hg : ∀ x, Measurable (g x))
    (hlaw : ∀ x, (stratumLaw P x).map latentCentered =
      (volume.restrict (Icc (-1/2 : ℝ) (1/2))).withDensity (fun t => ENNReal.ofReal (g x t)))
    (henv : ∀ x, ∀ᵐ t ∂volume.restrict (Icc (-1/2 : ℝ) (1/2)),
      K.clo * |t| ^ kappa ≤ g x t ∧ g x t ≤ K.chi * |t| ^ kappa) :
    populationM sigma P x q = strataProb P x *
      ∫ t in Icc (-1/2 : ℝ) (1/2), g x t *
        (projectedMean E P (a0+t) x * q.q t) := by
  have hb : 0 < beta := hbeta.1
  let H : ℝ → ℝ := fun t => projectedMean E P (a0+t) x
  have hH : Measurable H := (projectedMean_measurable E P beta hb hP.holderMean).comp
    (show Measurable (fun t : ℝ => (a0+t,x)) by fun_prop)
  have hi : Integrable (fun w => H (latentCentered w) * q.ell (observedCentered sigma w)) P := by
    apply (show Integrable (fun w => q.ell (observedCentered sigma w)) P from hweight).bdd_mul
      (c := 1) ((hH.comp (show Measurable (latentCentered (S := S)) by
        unfold latentCentered; fun_prop)).aestronglyMeasurable)
    filter_upwards [] with w
    have hm := projectedMean_mem_Icc E P hP.meanRange (a0+latentCentered w) x
    simpa only [H, Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg hm.1] using hm.2
  have h := inverse_weight_stratum_integral sigma P hP.strataPos hP.errorIndependence
    hP.gaussianChannel x q hq.2.1 hP.latentSupport hq.2.2.2.2.2.2 H hH hi
  rw [stratumLaw_integral, latent_density_integral kappa P g hg hlaw henv] at h
  have hM : populationM sigma P x q =
      ∫ w, (if sX w = x then H (latentCentered w) * q.ell (observedCentered sigma w) else 0) ∂P := by
    rw [populationM_eq_mean E beta kappa sigma hbeta hkappa hsigma P hP x q hq.2.1 hweight]
    apply integral_congr_ae
    filter_upwards [hP.latentSupport] with w hw
    by_cases hx : sX w = x
    · simp only [if_pos hx, H, latentCentered, add_sub_cancel]
      rw [projectedMean, Set.projIcc_of_mem zero_le_one hw]
    · simp only [if_neg hx]
  rw [← hM] at h
  exact (eq_div_iff (strataProb_pos P hP.strataPos x).ne').mp h.symm |>.symm.trans (mul_comm _ _)

/-- The weak-design upper envelope makes every nonnegative admissible latent weight integrable. [Under the stated conditions](hyp:g,hq,hg,hqn,hi,henv). [This is the stated conclusion](goal). -/
-- @node: latent_weight_integrable
lemma latent_weight_integrable {K : ClassConstants} (kappa : ℝ) (q g : ℝ → ℝ)
    (hq : Measurable q) (hg : Measurable g)
    (hqn : ∀ t ∈ Icc (-1/2 : ℝ) (1/2), 0 ≤ q t)
    (hi : Integrable (fun t => |t| ^ kappa * q t) (volume.restrict (Icc (-1/2 : ℝ) (1/2))))
    (henv : ∀ᵐ t ∂volume.restrict (Icc (-1/2 : ℝ) (1/2)),
      K.clo * |t| ^ kappa ≤ g t ∧ g t ≤ K.chi * |t| ^ kappa) :
    Integrable (fun t => g t * q t) (volume.restrict (Icc (-1/2 : ℝ) (1/2))) := by
  apply (hi.const_mul K.chi).mono' (hg.mul hq).aestronglyMeasurable
  filter_upwards [henv, ae_restrict_mem measurableSet_Icc] with t ht hs
  have hn : 0 ≤ g t := (mul_nonneg K.clo_pos.le
    (Real.rpow_nonneg (abs_nonneg _) _)).trans ht.1
  change ‖g t * q t‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hn (hqn t hs))]
  calc
    _ ≤ (K.chi * |t| ^ kappa) * q t := mul_le_mul_of_nonneg_right ht.2 (hqn t hs)
    _ = _ := by ring

/-- The lower weak-design envelope supplies the sharper latent denominator lower bound. [Under the stated conditions](hyp:g,hq,hg,hqn,hi,henv). [This is the stated conclusion](goal). -/
-- @node: latent_weight_lower
lemma latent_weight_lower {K : ClassConstants} (kappa : ℝ) (q g : ℝ → ℝ)
    (hq : Measurable q) (hg : Measurable g)
    (hqn : ∀ t ∈ Icc (-1/2 : ℝ) (1/2), 0 ≤ q t)
    (hi : Integrable (fun t => |t| ^ kappa * q t) (volume.restrict (Icc (-1/2 : ℝ) (1/2))))
    (henv : ∀ᵐ t ∂volume.restrict (Icc (-1/2 : ℝ) (1/2)),
      K.clo * |t| ^ kappa ≤ g t ∧ g t ≤ K.chi * |t| ^ kappa) :
    K.clo * weightMoment kappa q ≤ ∫ t in Icc (-1/2 : ℝ) (1/2), g t * q t := by
  have hl := integral_mono_ae (hi.const_mul K.clo)
    (latent_weight_integrable kappa q g hq hg hqn hi henv) (show
      (fun t => K.clo * (|t| ^ kappa * q t)) ≤ᵐ[volume.restrict (Icc (-1/2 : ℝ) (1/2))]
        (fun t => g t * q t) from by
      filter_upwards [henv, ae_restrict_mem measurableSet_Icc] with t ht hs
      calc
        _ = (K.clo * |t| ^ kappa) * q t := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right ht.1 (hqn t hs))
  change (∫ t in Icc (-1/2 : ℝ) (1/2), K.clo * (|t| ^ kappa * q t)) ≤ _ at hl
  rw [integral_const_mul] at hl
  simpa only [weightMoment] using hl

/-- Compact support controls the higher localization moment by the admissible base moment. [Under the stated conditions](hyp:hb,hk,hi). [This is the stated conclusion](goal). -/
-- @node: higher_weightMoment_integrable
lemma higher_weightMoment_integrable (beta kappa : ℝ) (hb : 0 ≤ beta) (hk : 0 ≤ kappa)
    (q : ℝ → ℝ)
    (hi : Integrable (fun t => |t| ^ kappa * q t) (volume.restrict (Icc (-1/2 : ℝ) (1/2)))) :
    Integrable (fun t => |t| ^ (kappa+beta) * q t) (volume.restrict (Icc (-1/2 : ℝ) (1/2))) := by
  have hm : Measurable (fun t : ℝ => |t| ^ beta) := by fun_prop
  have h := hi.mul_bdd (c := 1) hm.aestronglyMeasurable (show
      ∀ᵐ t ∂volume.restrict (Icc (-1/2 : ℝ) (1/2)), ‖|t| ^ beta‖ ≤ 1 from by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    apply Real.rpow_le_one (abs_nonneg _) _ hb
    exact (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩))
  apply h.congr
  filter_upwards [] with t
  rw [Real.rpow_add_of_nonneg (abs_nonneg _) hk hb]
  ring

/-- Holder continuity and the upper design envelope control the centered latent numerator. [Under the stated conditions](hyp:hb,hk,hholder,hrange,g,hq,hg,hqn,hi,henv). [This is the stated conclusion](goal). -/
-- @node: latent_weight_centered_bias
lemma latent_weight_centered_bias {K : ClassConstants} (E : PathSpace S) (beta kappa : ℝ)
    (hb : 0 < beta) (hk : 0 ≤ kappa) (P : Measure (StructSpace S))
    (hholder : HolderMean E beta P) (hrange : MeanRange E P) (x : Bool)
    (q g : ℝ → ℝ) (hq : Measurable q) (hg : Measurable g)
    (hqn : ∀ t ∈ Icc (-1/2 : ℝ) (1/2), 0 ≤ q t)
    (hi : Integrable (fun t => |t| ^ kappa * q t) (volume.restrict (Icc (-1/2 : ℝ) (1/2))))
    (henv : ∀ᵐ t ∂volume.restrict (Icc (-1/2 : ℝ) (1/2)),
      K.clo * |t| ^ kappa ≤ g t ∧ g t ≤ K.chi * |t| ^ kappa) :
    |(∫ t in Icc (-1/2 : ℝ) (1/2), g t * (projectedMean E P (a0+t) x * q t)) -
      condPotMean E P x a0 * (∫ t in Icc (-1/2 : ℝ) (1/2), g t * q t)| ≤
      K.chi * weightMoment (kappa+beta) q := by
  have hchi : 0 ≤ K.chi := K.clo_pos.le.trans K.clo_le_chi
  let H : ℝ → ℝ := fun t => projectedMean E P (a0+t) x
  let m := condPotMean E P x a0
  have ha0 : a0 ∈ Icc (0 : ℝ) 1 := by norm_num [a0]
  have hmrange := hrange x a0 ha0
  have hHm : Measurable H := (projectedMean_measurable E P beta hb hholder).comp
    (show Measurable (fun t : ℝ => (a0+t,x)) by fun_prop)
  have higq := latent_weight_integrable kappa q g hq hg hqn hi henv
  have hiH : Integrable (fun t => g t * q t * H t)
      (volume.restrict (Icc (-1/2 : ℝ) (1/2))) := by
    apply higq.mul_bdd (c := 1) hHm.aestronglyMeasurable
    filter_upwards [] with t
    have ht := projectedMean_mem_Icc E P hrange (a0+t) x
    simpa only [H, Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
  have hidiff := hiH.sub (higq.mul_const m)
  have hihigher := higher_weightMoment_integrable beta kappa hb.le hk q hi
  have hid : (∫ t in Icc (-1/2 : ℝ) (1/2), g t * (H t * q t)) -
      m * (∫ t in Icc (-1/2 : ℝ) (1/2), g t * q t) =
      ∫ t in Icc (-1/2 : ℝ) (1/2), (g t * q t * H t - g t * q t * m) := by
    rw [integral_sub hiH (higq.mul_const m), integral_mul_const]
    have heq : (fun t => g t * (H t * q t)) = (fun t => g t * q t * H t) := by
      funext t; ring
    rw [heq, mul_comm m]
  rw [hid, ← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  have hbound : ∀ᵐ t ∂volume.restrict (Icc (-1/2 : ℝ) (1/2)),
      ‖g t * q t * H t - g t * q t * m‖ ≤ K.chi * (|t| ^ (kappa+beta) * q t) := by
    filter_upwards [henv, ae_restrict_mem measurableSet_Icc] with t ht hs
    have hgn : 0 ≤ g t := (mul_nonneg K.clo_pos.le
      (Real.rpow_nonneg (abs_nonneg _) _)).trans ht.1
    have ha : a0+t ∈ Icc (0 : ℝ) 1 := by dsimp [a0]; constructor <;> linarith [hs.1, hs.2]
    have hinc : |H t-m| ≤ |t| ^ beta := by
      dsimp [H, m, projectedMean]
      rw [Set.projIcc_of_mem zero_le_one ha]
      simpa only [add_sub_cancel_left] using hholder x (a0+t) ha a0 ha0
    rw [show g t*q t*H t - g t*q t*m = (g t*q t)*(H t-m) by ring,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg hgn (hqn t hs))]
    calc
      _ ≤ (K.chi * |t| ^ kappa * q t) * (|t| ^ beta) :=
        mul_le_mul (mul_le_mul_of_nonneg_right ht.2 (hqn t hs)) hinc
          (abs_nonneg _) (mul_nonneg (mul_nonneg hchi
            (Real.rpow_nonneg (abs_nonneg _) _)) (hqn t hs))
      _ = _ := by rw [Real.rpow_add_of_nonneg (abs_nonneg _) hk hb.le]; ring
  have hle := integral_mono_ae hidiff.norm (hihigher.const_mul K.chi) hbound
  change (∫ t in Icc (-1/2 : ℝ) (1/2), ‖g t*q t*H t - g t*q t*m‖) ≤ _ at hle
  change _ ≤ ∫ t in Icc (-1/2 : ℝ) (1/2), K.chi * (|t| ^ (kappa+beta) * q t) at hle
  simpa only [integral_const_mul, weightMoment] using hle

/-- Every admissible positive inverse pair has a positive public denominator and the stated bias bound. [Under the stated conditions](hyp:hP,hq,hlaw,hbeta,hkappa,hsigma). [This is the stated conclusion](goal). -/
-- @node: lem:positive-ratio
lemma positive_ratio (E : PathSpace S) (beta kappa sigma : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2)
    (hsigma : sigma ∈ Icc (0 : ℝ) (1/4))
    (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    {K : ClassConstants} (hP : NoisyDoseModelClass E K beta kappa sigma P) (q : WeightPair)
    (hq : PairAdmissible kappa sigma q) (hlaw : LawAdmissible sigma P q) :
    ∀ x : Bool, 0 < populationD sigma P x q ∧
      bq K kappa q.q ≤ populationD sigma P x q ∧
      |localizedRatio sigma P x q - condPotMean E P x a0| ≤ Bq K beta kappa q.q := by
  obtain ⟨g, hg, hglaw, hgenv⟩ := hP.weakDesign
  obtain ⟨hqm, hellm, hqn, hi, hIpos, hintegral, hinverse⟩ := hq
  have hq : PairAdmissible kappa sigma q :=
    ⟨hqm, hellm, hqn, hi, hIpos, hintegral, hinverse⟩
  intro x
  let L := ∫ t in Icc (-1/2 : ℝ) (1/2), g x t * q.q t
  let N := ∫ t in Icc (-1/2 : ℝ) (1/2), g x t *
    (projectedMean E P (a0+t) x * q.q t)
  have hL : K.clo * weightMoment kappa q.q ≤ L :=
    latent_weight_lower kappa q.q (g x) hqm (hg x) hqn hi (hgenv x)
  have hcI : 0 < K.clo * weightMoment kappa q.q := mul_pos K.clo_pos hIpos
  have hchi : 0 ≤ K.chi := K.clo_pos.le.trans K.clo_le_chi
  have hLpos : 0 < L := lt_of_lt_of_le hcI hL
  have hp : 0 < strataProb P x := strataProb_pos P hP.strataPos x
  have hD : populationD sigma P x q = strataProb P x * L :=
    populationD_eq_latent E beta kappa sigma P hP x q hq hlaw g hg hglaw hgenv
  have hM : populationM sigma P x q = strataProb P x * N :=
    populationM_eq_latent E beta kappa sigma hbeta hkappa hsigma P hP x q hq hlaw
      g hg hglaw hgenv
  have hDpos : 0 < populationD sigma P x q := by rw [hD]; exact mul_pos hp hLpos
  refine ⟨hDpos, ?_, ?_⟩
  · rw [hD]
    have h := mul_le_mul (hP.stratumOverlap x).1 hL hcI.le hp.le
    dsimp [bq]
    nlinarith
  · have hb : 0 < beta := hbeta.1
    have hcenter : |N - condPotMean E P x a0 * L| ≤
        K.chi * weightMoment (kappa+beta) q.q :=
      latent_weight_centered_bias E beta kappa hb hkappa.1 P hP.holderMean hP.meanRange
        x q.q (g x) hqm (hg x) hqn hi (hgenv x)
    have hmoment : 0 ≤ weightMoment (kappa+beta) q.q := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hqn t ht)
    have hratio : localizedRatio sigma P x q = N/L := by
      dsimp [localizedRatio]
      rw [hM, hD]
      field_simp
    rw [hratio]
    have hid : N/L - condPotMean E P x a0 =
        (N - condPotMean E P x a0 * L)/L := by field_simp <;> ring
    rw [hid, abs_div, abs_of_pos hLpos]
    calc
      _ ≤ (K.chi * weightMoment (kappa+beta) q.q) / L :=
        div_le_div_of_nonneg_right hcenter hLpos.le
      _ ≤ (K.chi * weightMoment (kappa+beta) q.q) / (K.clo * weightMoment kappa q.q) :=
        div_le_div_of_nonneg_left (mul_nonneg hchi hmoment) hcI hL
      _ = Bq K beta kappa q.q := by
        have := K.clo_pos.ne'
        dsimp [Bq]; field_simp

end CausalSmith.Stat.NoisydoseWeakdesignTransition

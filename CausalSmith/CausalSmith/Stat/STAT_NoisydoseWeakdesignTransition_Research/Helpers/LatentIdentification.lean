module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.GaussianInjective
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.IdentificationBasics
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.PositiveRatio
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.RealizedDoseMean
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Order.ProjIcc

/-! Latent measures, local mass ratios, continuous mean recovery, and unmarked deconvolution. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
variable {S : Type*} [MeasurableSpace S]


/-- Unmarked and potential-mean-marked conditional latent measures used in identification. -/
def latentDoseLaw (P : Measure (StructSpace S)) (x : Bool) : Measure ℝ :=
  (stratumLaw P x).map latentCentered
/-- Conditional latent dose measure marked by the conditional potential-outcome mean. -/
def latentMeanMeasure (E : PathSpace S) (P : Measure (StructSpace S)) (x : Bool) : Measure ℝ :=
  (latentDoseLaw P x).withDensity (fun t => ENNReal.ofReal (condPotMean E P x (t+a0)))
/-- Shrinking-neighborhood mass ratio of the identified marked and unmarked latent measures. -/
def latentLocalRatio (E : PathSpace S) (P : Measure (StructSpace S)) (x : Bool) (j : ℕ) : ℝ :=
  (latentMeanMeasure E P x).real (Ioo (-1 / ((j : ℝ)+3)) (1 / ((j : ℝ)+3))) /
    (latentDoseLaw P x).real (Ioo (-1 / ((j : ℝ)+3)) (1 / ((j : ℝ)+3)))
/-- Normalized positive strata give finite latent dose laws. [Under the stated conditions](hyp:hoverlap). [This is the stated conclusion](goal). -/
-- @node: latentDoseLaw_probability
lemma latentDoseLaw_probability (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    (hoverlap : StratumPositive P) (x : Bool) : IsProbabilityMeasure (latentDoseLaw P x) := by
  letI := stratumLaw_probability P hoverlap x
  exact Measure.isProbabilityMeasure_map (by unfold latentCentered; fun_prop : Measurable (latentCentered (S := S))).aemeasurable

/-- The density representation puts all latent dose mass on the compact interval. [Under the stated conditions](hyp:hdesign). [This is the stated conclusion](goal). -/
-- @node: latentDoseLaw_ae_mem
lemma latentDoseLaw_ae_mem (P : Measure (StructSpace S)) (kappa : ℝ)
    {K : ClassConstants} (hdesign : WeakDesign K.clo K.chi kappa P) (x : Bool) :
    ∀ᵐ t ∂latentDoseLaw P x, t ∈ Icc (-1/2 : ℝ) (1/2) := by
  obtain ⟨g, hg, hlaw, hbounds⟩ := hdesign
  rw [latentDoseLaw, hlaw x]
  exact (ae_restrict_mem measurableSet_Icc).filter_mono (Measure.AbsolutelyContinuous.ae_le (show (volume.restrict (Icc (-1/2 : ℝ) (1/2))).withDensity
    (fun t => ENNReal.ofReal (g x t)) ≪ volume.restrict (Icc (-1/2 : ℝ) (1/2)) from
      withDensity_absolutelyContinuous _ _))

/-- The lower power envelope makes every target neighborhood have positive mass. [Under the stated conditions](hyp:hoverlap,hdesign,heps,hhalf). [This is the stated conclusion](goal). -/
-- @node: latentDoseLaw_local_mass_pos
lemma latentDoseLaw_local_mass_pos (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    (kappa : ℝ) (hoverlap : StratumPositive P) {K : ClassConstants} (hdesign : WeakDesign K.clo K.chi kappa P)
    (x : Bool) (eps : ℝ) (heps : 0 < eps) (hhalf : eps ≤ 1/2) :
    0 < (latentDoseLaw P x).real (Ioo (-eps) eps) := by
  letI := latentDoseLaw_probability P hoverlap x
  obtain ⟨g, hg, hlaw, hbounds⟩ := hdesign
  have hsub : Ioo (-eps) eps ⊆ Icc (-1/2 : ℝ) (1/2) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hb : ∀ᵐ t ∂volume.restrict (Ioo (-eps) eps),
      K.clo * |t| ^ kappa ≤ g x t := by
    exact (ae_restrict_of_ae_restrict_of_subset hsub (hbounds x)).mono (fun _ h => h.1)
  have hn : ∀ᵐ t ∂volume.restrict (Ioo (-eps) eps), t ≠ (0 : ℝ) :=
    (ae_iff.mpr (by simp)).filter_mono (ae_mono Measure.restrict_le_self)
  have hp : ∀ᵐ t ∂volume.restrict (Ioo (-eps) eps), 0 < ENNReal.ofReal (g x t) := by
    filter_upwards [hb, hn] with t ht hn
    apply ENNReal.ofReal_pos.mpr
    exact lt_of_lt_of_le (mul_pos K.clo_pos (Real.rpow_pos_of_pos (abs_pos.mpr hn) _)) ht
  have hm : (latentDoseLaw P x) (Ioo (-eps) eps) ≠ 0 := by
    rw [latentDoseLaw, hlaw x, withDensity_apply _ measurableSet_Ioo,
      Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.mpr hsub]
    intro hz
    have hz' := (lintegral_eq_zero_iff' (hg x).ennreal_ofReal.aemeasurable.restrict).mp hz
    have hfalse : ∀ᵐ t ∂volume.restrict (Ioo (-eps) eps), False := by
      filter_upwards [hp, hz'] with t ht hz
      exact (ne_of_gt ht) hz
    have : volume (Ioo (-eps) eps) = 0 := by
      simpa using (ae_iff.mp hfalse)
    rw [Real.volume_Ioo] at this
    have : eps - -eps ≤ 0 := ENNReal.ofReal_eq_zero.mp this
    linarith
  exact ENNReal.toReal_pos hm (measure_ne_top _ _)

/-- The Holder mean is measurable and integrable under its compact latent dose law. [Under the stated conditions](hyp:hbeta,hoverlap,hdesign,hholder,hrange). [This is the stated conclusion](goal). -/
-- @node: latentMean_integrable
lemma latentMean_integrable (E : PathSpace S) (P : Measure (StructSpace S))
    [IsProbabilityMeasure P] (beta kappa : ℝ) (hbeta : 0 < beta)
    (hoverlap : StratumPositive P) {K : ClassConstants} (hdesign : WeakDesign K.clo K.chi kappa P)
    (hholder : HolderMean E beta P) (hrange : MeanRange E P) (x : Bool) :
    Integrable (fun t => condPotMean E P x (t+a0)) (latentDoseLaw P x) := by
  letI := latentDoseLaw_probability P hoverlap x
  have hc : Continuous (fun t : ℝ => condPotMean E P x
      (Set.projIcc 0 1 zero_le_one (t+a0) : ℝ)) := by
    exact (condPotMean_continuousOn E beta P hbeta hholder x).comp_continuous
      (continuous_subtype_val.comp (continuous_projIcc.comp (by fun_prop)))
      (fun t => (Set.projIcc 0 1 zero_le_one (t+a0)).property)
  have heq : (fun t => condPotMean E P x
      (Set.projIcc 0 1 zero_le_one (t+a0) : ℝ)) =ᵐ[latentDoseLaw P x]
      (fun t => condPotMean E P x (t+a0)) := by
    filter_upwards [latentDoseLaw_ae_mem P kappa hdesign x] with t ht
    have ha : t+a0 ∈ Icc (0 : ℝ) 1 := by
      dsimp [a0]; constructor <;> linarith [ht.1, ht.2]
    rw [Set.projIcc_of_mem _ ha]
  apply Integrable.of_bound (hc.aestronglyMeasurable.congr heq) 1
  filter_upwards [latentDoseLaw_ae_mem P kappa hdesign x] with t ht
  have ha : t+a0 ∈ Icc (0 : ℝ) 1 := by
    dsimp [a0]; constructor <;> linarith [ht.1, ht.2]
  rw [Real.norm_eq_abs, abs_of_nonneg (le_trans (by norm_num) (hrange x _ ha).1)]
  exact (hrange x _ ha).2.trans (by norm_num)

/-- Marked latent mass is the integral of the potential mean against unmarked mass. [Under the stated conditions](hyp:hbeta,hoverlap,hdesign,hholder,hrange,hB). [This is the stated conclusion](goal). -/
-- @node: latentMeanMeasure_real
lemma latentMeanMeasure_real (E : PathSpace S) (P : Measure (StructSpace S))
    [IsProbabilityMeasure P] (beta kappa : ℝ) (hbeta : 0 < beta)
    (hoverlap : StratumPositive P) {K : ClassConstants} (hdesign : WeakDesign K.clo K.chi kappa P)
    (hholder : HolderMean E beta P) (hrange : MeanRange E P) (x : Bool)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (latentMeanMeasure E P x).real B = ∫ t in B, condPotMean E P x (t+a0) ∂latentDoseLaw P x := by
  have hi := latentMean_integrable E P beta kappa hbeta hoverlap hdesign hholder hrange x
  have hn : 0 ≤ᵐ[latentDoseLaw P x] (fun t => condPotMean E P x (t+a0)) := by
    filter_upwards [latentDoseLaw_ae_mem P kappa hdesign x] with t ht
    have ha : t+a0 ∈ Icc (0 : ℝ) 1 := by
      dsimp [a0]; constructor <;> linarith [ht.1, ht.2]
    exact le_trans (by norm_num) (hrange x _ ha).1
  rw [latentMeanMeasure, Measure.real, withDensity_apply _ hB,
    ← ofReal_integral_eq_lintegral_ofReal hi.integrableOn (hn.filter_mono (ae_mono Measure.restrict_le_self)),
    ENNReal.toReal_ofReal (integral_nonneg_of_ae (hn.filter_mono (ae_mono Measure.restrict_le_self)))]

/-- A positive local-mass ratio approximates the target with the paper's Holder error. [Under the stated conditions](hyp:hbeta,hoverlap,hdesign,hholder,hrange). [This is the stated conclusion](goal). -/
-- @node: latentLocalRatio_error
lemma latentLocalRatio_error (E : PathSpace S) (P : Measure (StructSpace S))
    [IsProbabilityMeasure P] (beta kappa : ℝ) (hbeta : 0 < beta)
    (hoverlap : StratumPositive P) {K : ClassConstants} (hdesign : WeakDesign K.clo K.chi kappa P)
    (hholder : HolderMean E beta P) (hrange : MeanRange E P) (x : Bool) (j : ℕ) :
    |latentLocalRatio E P x j - condPotMean E P x a0| ≤ (1 / ((j : ℝ)+3))^beta := by
  letI := latentDoseLaw_probability P hoverlap x
  let eps : ℝ := 1 / ((j : ℝ)+3)
  let B : Set ℝ := Ioo (-eps) eps
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hhalf : eps ≤ 1/2 := by
    dsimp [eps]
    apply (div_le_iff₀ (by positivity : 0 < (j : ℝ)+3)).mpr
    have := Nat.cast_nonneg (α := ℝ) j
    linarith
  have hp : 0 < (latentDoseLaw P x).real B :=
    latentDoseLaw_local_mass_pos P kappa hoverlap hdesign x eps heps hhalf
  have hi := latentMean_integrable E P beta kappa hbeta hoverlap hdesign hholder hrange x
  have herr : ‖∫ t in B, (condPotMean E P x (t+a0) - condPotMean E P x a0)
      ∂latentDoseLaw P x‖ ≤ eps^beta * (latentDoseLaw P x).real B := by
    apply norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _)
    intro t ht
    have ha : t+a0 ∈ Icc (0 : ℝ) 1 := by
      dsimp [B] at ht
      dsimp [a0]; constructor <;> linarith [ht.1, ht.2]
    have hh := hholder x (t+a0) ha a0 (by norm_num [a0])
    rw [Real.norm_eq_abs]
    apply hh.trans
    simp only [add_sub_cancel_right]
    apply Real.rpow_le_rpow (abs_nonneg _) _ hbeta.le
    apply abs_le.mpr
    constructor <;> linarith [ht.1, ht.2]
  rw [integral_sub hi.integrableOn (integrable_const _), setIntegral_const, smul_eq_mul,
    Real.norm_eq_abs] at herr
  rw [latentLocalRatio, latentMeanMeasure_real E P beta kappa hbeta hoverlap hdesign hholder hrange x _ measurableSet_Ioo]
  simp only [neg_div]
  change |(∫ t in B, condPotMean E P x (t+a0) ∂latentDoseLaw P x) /
    (latentDoseLaw P x).real B - condPotMean E P x a0| ≤ eps^beta
  rw [div_sub' (ne_of_gt hp), abs_div, abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  simpa only [mul_comm] using herr

/-- Positive Holder exponent sends the shrinking-neighborhood ratio to the target mean. [Under the stated conditions](hyp:hbeta,hoverlap,hdesign,hholder,hrange). [This is the stated conclusion](goal). -/
-- @node: latentLocalRatio_tendsto
lemma latentLocalRatio_tendsto (E : PathSpace S) (P : Measure (StructSpace S))
    [IsProbabilityMeasure P] (beta kappa : ℝ) (hbeta : 0 < beta)
    (hoverlap : StratumPositive P) {K : ClassConstants} (hdesign : WeakDesign K.clo K.chi kappa P)
    (hholder : HolderMean E beta P) (hrange : MeanRange E P) (x : Bool) :
    Tendsto (latentLocalRatio E P x) atTop (𝓝 (condPotMean E P x a0)) := by
  have heps : Tendsto (fun j : ℕ => 1 / ((j : ℝ)+3)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat, add_assoc, show (2 : ℝ)+1 = 3 by norm_num] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
  have hpow : Tendsto (fun j : ℕ => (1 / ((j : ℝ)+3))^beta) atTop (𝓝 (0 : ℝ)) := by
    simpa [Real.zero_rpow (ne_of_gt hbeta)] using
      heps.rpow_const (Or.inr hbeta.le)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun j => norm_nonneg _) _ hpow
  intro j
  simpa only [Real.norm_eq_abs] using
    latentLocalRatio_error E P beta kappa hbeta hoverlap hdesign hholder hrange x j

/-- The weak-design lower envelope makes Lebesgue measure dominated by latent dose mass,
including when the density vanishes at the single target point. [Under the stated conditions](hyp:hdesign). [This is the stated conclusion](goal). -/
-- @node: latentDoseLaw_volume_absolutelyContinuous
lemma latentDoseLaw_volume_absolutelyContinuous (P : Measure (StructSpace S))
    (kappa : ℝ) {K : ClassConstants} (hdesign : WeakDesign K.clo K.chi kappa P) (x : Bool) :
    volume.restrict (Icc (-1/2 : ℝ) (1/2)) ≪ latentDoseLaw P x := by
  obtain ⟨g, hg, hlaw, hbounds⟩ := hdesign
  rw [latentDoseLaw, hlaw x]
  apply withDensity_absolutelyContinuous' (hg x).ennreal_ofReal.aemeasurable.restrict
  have hn : ∀ᵐ t ∂volume.restrict (Icc (-1/2 : ℝ) (1/2)), t ≠ (0 : ℝ) :=
    (ae_iff.mpr (by simp)).filter_mono (ae_mono Measure.restrict_le_self)
  filter_upwards [hbounds x, hn] with t ht hn
  apply ne_of_gt
  apply ENNReal.ofReal_pos.mpr
  exact lt_of_lt_of_le
    (mul_pos K.clo_pos (Real.rpow_pos_of_pos (abs_pos.mpr hn) _)) ht.1

/-- Equality of the marked and unmarked measures identifies their nonnegative mean densities
almost everywhere under the common latent law. [Under the stated conditions](hyp:hbeta,hoverlap,hoverlap',hdesign,hdesign',hholder,hholder',hrange,hrange',hDose,hMean). [This is the stated conclusion](goal). -/
-- @node: latentMean_ae_eq_of_measures_eq
lemma latentMean_ae_eq_of_measures_eq (E : PathSpace S)
    (P P' : Measure (StructSpace S)) [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (beta kappa : ℝ) (hbeta : 0 < beta)
    (hoverlap : StratumPositive P) (hoverlap' : StratumPositive P')
    {K : ClassConstants} (hdesign : WeakDesign K.clo K.chi kappa P) (hdesign' : WeakDesign K.clo K.chi kappa P')
    (hholder : HolderMean E beta P) (hholder' : HolderMean E beta P')
    (hrange : MeanRange E P) (hrange' : MeanRange E P') (x : Bool)
    (hDose : latentDoseLaw P x = latentDoseLaw P' x)
    (hMean : latentMeanMeasure E P x = latentMeanMeasure E P' x) :
    (fun t => condPotMean E P x (t+a0)) =ᵐ[latentDoseLaw P x]
      (fun t => condPotMean E P' x (t+a0)) := by
  letI := latentDoseLaw_probability P hoverlap x
  have hi := latentMean_integrable E P beta kappa hbeta hoverlap hdesign hholder hrange x
  have hi' := latentMean_integrable E P' beta kappa hbeta hoverlap' hdesign' hholder' hrange' x
  rw [← hDose] at hi'
  have heq : (fun t => ENNReal.ofReal (condPotMean E P x (t+a0))) =ᵐ[latentDoseLaw P x]
      (fun t => ENNReal.ofReal (condPotMean E P' x (t+a0))) := by
    apply (withDensity_eq_iff_of_sigmaFinite
      hi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      hi'.aestronglyMeasurable.aemeasurable.ennreal_ofReal).mp
    simpa only [latentMeanMeasure, ← hDose] using hMean
  filter_upwards [heq, latentDoseLaw_ae_mem P kappa hdesign x] with t ht hsupport
  have ha : t+a0 ∈ Icc (0 : ℝ) 1 := by
    dsimp [a0]; constructor <;> linarith [hsupport.1, hsupport.2]
  exact (ENNReal.ofReal_eq_ofReal_iff
    (le_trans (by norm_num) (hrange x _ ha).1)
    (le_trans (by norm_num) (hrange' x _ ha).1)).mp ht

/-- Dominated Lebesgue mass and Holder continuity extend the identified latent density ratio
to every dose, including the design zero and both support endpoints. [Under the stated conditions](hyp:hbeta,hoverlap,hoverlap',hdesign,hdesign',hholder,hholder',hrange,hrange',hDose,hMean). [This is the stated conclusion](goal). -/
-- @node: condPotMean_eqOn_of_latent_measures_eq
lemma condPotMean_eqOn_of_latent_measures_eq (E : PathSpace S)
    (P P' : Measure (StructSpace S)) [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (beta kappa : ℝ) (hbeta : 0 < beta)
    (hoverlap : StratumPositive P) (hoverlap' : StratumPositive P')
    {K : ClassConstants} (hdesign : WeakDesign K.clo K.chi kappa P) (hdesign' : WeakDesign K.clo K.chi kappa P')
    (hholder : HolderMean E beta P) (hholder' : HolderMean E beta P')
    (hrange : MeanRange E P) (hrange' : MeanRange E P') (x : Bool)
    (hDose : latentDoseLaw P x = latentDoseLaw P' x)
    (hMean : latentMeanMeasure E P x = latentMeanMeasure E P' x) :
    EqOn (condPotMean E P x) (condPotMean E P' x) (Icc (0 : ℝ) 1) := by
  have hae := latentMean_ae_eq_of_measures_eq E P P' beta kappa hbeta
    hoverlap hoverlap' hdesign hdesign' hholder hholder' hrange hrange' x hDose hMean
  have haeVolume := hae.filter_mono
    (latentDoseLaw_volume_absolutelyContinuous P kappa hdesign x).ae_le
  have hshift : MapsTo (fun t : ℝ => t+a0) (Icc (-1/2 : ℝ) (1/2)) (Icc (0 : ℝ) 1) := by
    intro t ht
    dsimp [a0]; constructor <;> linarith [ht.1, ht.2]
  have hc := (condPotMean_continuousOn E beta P hbeta hholder x).comp
    (show ContinuousOn (fun t : ℝ => t+a0) (Icc (-1/2 : ℝ) (1/2)) by fun_prop) hshift
  have hc' := (condPotMean_continuousOn E beta P' hbeta hholder' x).comp
    (show ContinuousOn (fun t : ℝ => t+a0) (Icc (-1/2 : ℝ) (1/2)) by fun_prop) hshift
  have heq := Measure.eqOn_Icc_of_ae_eq volume
    (by norm_num : (-1/2 : ℝ) ≠ 1/2) haeVolume hc hc'
  intro a ha
  have ht : a-a0 ∈ Icc (-1/2 : ℝ) (1/2) := by
    dsimp [a0]; constructor <;> linarith [ha.1, ha.2]
  simpa only [sub_add_cancel] using heq ht

/-- The observed conditional record law is a normalized restriction of the public law. [This is the stated conclusion](goal). -/
-- @node: stratumLaw_map_obsMap
lemma stratumLaw_map_obsMap (sigma : ℝ) (P : Measure (StructSpace S)) (x : Bool) :
    (stratumLaw P x).map (obsMap sigma) =
      ((obsLaw sigma P) {o : Obs | o.1 = x})⁻¹ •
        (obsLaw sigma P).restrict {o : Obs | o.1 = x} := by
  have hm : Measurable (obsMap (S := S) sigma) := by
    unfold obsMap contaminatedDose
    fun_prop
  have hx : MeasurableSet {o : Obs | o.1 = x} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  rw [obsLaw, Measure.map_apply hm hx, Measure.restrict_map hm hx,
    stratumLaw, Measure.map_smul]
  rfl

/-- Observational equivalence identifies the stratum-conditional centered observed dose law. [Under the stated conditions](hyp:hobs). [This is the stated conclusion](goal). -/
-- @node: observedCentered_stratum_eq_of_obsLaw_eq
lemma observedCentered_stratum_eq_of_obsLaw_eq (sigma : ℝ)
    (P P' : Measure (StructSpace S)) (hobs : obsLaw sigma P = obsLaw sigma P')
    (x : Bool) :
    (stratumLaw P x).map (observedCentered sigma) =
      (stratumLaw P' x).map (observedCentered sigma) := by
  have hh : (stratumLaw P x).map (obsMap sigma) =
      (stratumLaw P' x).map (obsMap sigma) := by
    rw [stratumLaw_map_obsMap, stratumLaw_map_obsMap, hobs]
  have hh' := congrArg (Measure.map (fun o : Obs => o.2.1 - a0)) hh
  rw [Measure.map_map (by fun_prop) (by unfold obsMap contaminatedDose; fun_prop),
    Measure.map_map (by fun_prop) (by unfold obsMap contaminatedDose; fun_prop)] at hh'
  exact hh'

/-- The unmarked observed conditional dose measure is latent dose convolved with Gaussian noise. [Under the stated conditions](hyp:hoverlap,herr,hgauss). [This is the stated conclusion](goal). -/
-- @node: observedCentered_stratum_convolution
lemma observedCentered_stratum_convolution (sigma : ℝ)
    (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    (hoverlap : StratumPositive P) (herr : ErrorIndependence P)
    (hgauss : GaussianChannel P) (x : Bool) :
    (stratumLaw P x).map (observedCentered sigma) =
      (latentDoseLaw P x).conv (gaussianReal 0 (NNReal.mk (sigma^2) (sq_nonneg sigma))) := by
  letI := stratumLaw_probability P hoverlap x
  have hT : Measurable (latentCentered (S := S)) := by unfold latentCentered; fun_prop
  have hp := congrArg (Measure.map (fun p : ℝ × ℝ => p.2 + sigma*p.1))
    (error_centered_product_stratum P hoverlap herr x)
  rw [Measure.map_map (by fun_prop) (by fun_prop), hgauss] at hp
  have hscale : (gaussianReal (0 : ℝ) 1).map (fun z => sigma*z) =
      gaussianReal 0 (NNReal.mk (sigma^2) (sq_nonneg sigma)) := by
    simpa using (gaussianReal_map_const_mul (μ := 0) (v := 1) sigma)
  letI := latentDoseLaw_probability P hoverlap x
  have hprod := Measure.map_prod_map (gaussianReal (0 : ℝ) 1)
    ((stratumLaw P x).map latentCentered) (show Measurable (fun z : ℝ => sigma*z) by fun_prop)
    measurable_id
  simp only [Measure.map_id] at hprod
  rw [Measure.conv_comm, Measure.conv, latentDoseLaw, ← hscale, hprod,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have hp' : (stratumLaw P x).map (fun w => latentCentered w + sigma*sZ w) =
      (((gaussianReal (0 : ℝ) 1).prod ((stratumLaw P x).map latentCentered)).map
        ((fun p : ℝ × ℝ => p.1+p.2) ∘ Prod.map (fun z => sigma*z) id)) := by
    simpa [Function.comp_def, Prod.map, add_comm] using hp
  refine (Measure.map_congr ?_).trans hp'
  filter_upwards with w
  dsimp [Function.comp_def, observedCentered, contaminatedDose, latentCentered]
  ring

/-- Injective Gaussian convolution identifies the unmarked latent dose law from observations. [Under the stated conditions](hyp:hoverlap,hoverlap',hdesign,hdesign',herr,herr',hgauss,hgauss',hobs,hsigma). [This is the stated conclusion](goal). -/
-- @node: latentDoseLaw_eq_of_obsLaw_eq
lemma latentDoseLaw_eq_of_obsLaw_eq (sigma kappa : ℝ)
    (hsigma : sigma ∈ Icc (0 : ℝ) (1/4))
    (P P' : Measure (StructSpace S)) [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (hoverlap : StratumPositive P) (hoverlap' : StratumPositive P')
    {K : ClassConstants} (hdesign : WeakDesign K.clo K.chi kappa P) (hdesign' : WeakDesign K.clo K.chi kappa P')
    (herr : ErrorIndependence P) (herr' : ErrorIndependence P')
    (hgauss : GaussianChannel P) (hgauss' : GaussianChannel P')
    (hobs : obsLaw sigma P = obsLaw sigma P') (x : Bool) :
    latentDoseLaw P x = latentDoseLaw P' x := by
  letI := latentDoseLaw_probability P hoverlap x
  letI := latentDoseLaw_probability P' hoverlap' x
  have hc := observedCentered_stratum_eq_of_obsLaw_eq sigma P P' hobs x
  rw [observedCentered_stratum_convolution sigma P hoverlap herr hgauss x,
    observedCentered_stratum_convolution sigma P' hoverlap' herr' hgauss' x] at hc
  have hsupport : (latentDoseLaw P x) (Icc (-1/2 : ℝ) (1/2))ᶜ = 0 :=
    ae_iff.mp (latentDoseLaw_ae_mem P kappa hdesign x)
  have hsupport' : (latentDoseLaw P' x) (Icc (-1/2 : ℝ) (1/2))ᶜ = 0 :=
    ae_iff.mp (latentDoseLaw_ae_mem P' kappa hdesign' x)
  have hi := compact_gaussian_convolution_injective sigma hsigma
    (latentDoseLaw P x) 0 (latentDoseLaw P' x) 0
    hsupport (by simp) hsupport' (by simp) (by simpa using hc)
  simpa using hi

end CausalSmith.Stat.NoisydoseWeakdesignTransition

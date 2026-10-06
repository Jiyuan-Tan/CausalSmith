module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.LowerTuning
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.ObservedPerturbationBounds

/-! Direct-regime observed energy contraction, equations (17)--(18). -/
public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- Weighted Cauchy--Schwarz follows from the nonnegative centered quadratic integral. [Under the stated conditions](hyp:g,hg,hi,ha,hid,hid2). [This is the stated conclusion](goal). -/
-- @node: lower_weighted_integral_cauchy_schwarz
lemma lower_weighted_integral_cauchy_schwarz (g delta : ℝ → ℝ)
    (hg : ∀ t, 0 ≤ g t) (hi : Integrable g)
    (hid : Integrable (fun t => g t * delta t))
    (hid2 : Integrable (fun t => g t * (delta t)^2))
    (ha : 0 < ∫ t, g t) :
    (∫ t, g t * delta t)^2 ≤ (∫ t, g t) * ∫ t, g t * (delta t)^2 := by
  let a := ∫ t, g t
  let b := ∫ t, g t * delta t
  let c := ∫ t, g t * (delta t)^2
  have hv : 0 ≤ ∫ t, g t * (a * delta t - b)^2 :=
    integral_nonneg (fun t => mul_nonneg (hg t) (sq_nonneg _))
  have he : (∫ t, g t * (a * delta t - b)^2) = a^2*c - (2*a*b)*b + b^2*a := by
    simp_rw [show ∀ t, g t * (a * delta t - b)^2 =
      a^2*(g t*(delta t)^2) - (2*a*b)*(g t*delta t) + b^2*g t by intro t; ring]
    integral_linearity
    simp only [integral_const_mul, a, b, c]
  rw [he] at hv
  change b^2 ≤ a*c
  have ha' : 0 < a := ha
  nlinarith

/-- Multiplication by a continuous function preserves integrability of the compact design density. [Under the stated conditions](hyp:hk,hf). [This is the stated conclusion](goal). -/
-- @node: witnessDesignDensity_mul_continuous_integrable
@[fun_prop] lemma witnessDesignDensity_mul_continuous_integrable (kappa : ℝ)
    (hk : 0 ≤ kappa) (f : ℝ → ℝ) (hf : Continuous f) :
    Integrable (fun t => witnessDesignDensity kappa t * f t) := by
  have he : (fun t => witnessDesignDensity kappa t * f t) =
      (Icc (-1/2 : ℝ) (1/2)).indicator (fun t => (kappa+1)*2^kappa*|t|^kappa*f t) := by
    funext t
    simp only [witnessDesignDensity, indicator_apply]
    split_ifs <;> simp
  rw [he]
  have hc : Continuous (fun t : ℝ => (kappa+1)*2^kappa*|t|^kappa*f t) := by fun_prop
  exact hc.integrableOn_Icc.integrable_indicator measurableSet_Icc

/-- At each observed dose the squared signed convolution is controlled by its quadratic convolution. [Under the stated conditions](hyp:hd,hk,hs). [This is the stated conclusion](goal). -/
-- @node: gaussian_design_convolution_cauchy_schwarz
lemma gaussian_design_convolution_cauchy_schwarz (kappa sigma w : ℝ)
    (hk : kappa ∈ Icc (0 : ℝ) 2) (hs : sigma ∈ Ioc (0 : ℝ) (1/4))
    (delta : ℝ → ℝ) (hd : Continuous delta) :
    (smoothSigned sigma (fun t => witnessDesignDensity kappa t * delta t) w)^2 /
      smoothSigned sigma (witnessDesignDensity kappa) w ≤
        smoothSigned sigma (fun t => witnessDesignDensity kappa t * (delta t)^2) w := by
  have hp : 0 < smoothSigned sigma (witnessDesignDensity kappa) w :=
    (gaussian_design_density_lower kappa sigma hk hs w).1
  apply (div_le_iff₀ hp).mpr
  have hc : Continuous (fun t => phiDensity sigma (w-t)) := by unfold phiDensity; fun_prop
  have h0 := witnessDesignDensity_mul_continuous_integrable kappa hk.1 _ hc
  have h1 := witnessDesignDensity_mul_continuous_integrable kappa hk.1 _ (hc.mul hd)
  have h2 := witnessDesignDensity_mul_continuous_integrable kappa hk.1 _ (hc.mul (hd.pow 2))
  have hcs := lower_weighted_integral_cauchy_schwarz
    (fun t => witnessDesignDensity kappa t * phiDensity sigma (w-t)) delta
    (fun t => mul_nonneg (witnessDesignDensity_nonneg kappa t hk.1)
      (phiDensity_pos sigma (w-t) hs.1).le) h0
    (by simpa only [Pi.mul_apply, mul_assoc] using h1) (by simpa only [Pi.mul_apply, Pi.pow_apply, mul_assoc] using h2) hp
  simpa only [smoothSigned, mul_assoc, mul_comm, mul_left_comm] using hcs

/-- Absolute Fubini preserves the signed integral under Gaussian smoothing. [Under the stated conditions](hyp:hs,hv). [This is the stated conclusion](goal). -/
-- @node: lower_smoothSigned_integrable_integral
lemma lower_smoothSigned_integrable_integral (sigma : ℝ) (hs : 0 < sigma)
    (v : ℝ → ℝ) (hv : Integrable v) :
    Integrable (smoothSigned sigma v) ∧ (∫ w, smoothSigned sigma v w) = ∫ t, v t := by
  let K : ℝ → ℝ → ℝ := fun t w => v t * phiDensity sigma (w-t)
  have hKi (t : ℝ) : Integrable (K t) :=
    (phiDensity_shift_integrable sigma t hs).const_mul _
  have hKm : AEStronglyMeasurable (Function.uncurry K) (volume.prod volume) := by
    have hh := hv.aestronglyMeasurable.comp_fst.mul
      (show AEStronglyMeasurable (fun p : ℝ × ℝ => phiDensity sigma (p.2-p.1))
        (volume.prod volume) by unfold phiDensity; fun_prop)
    exact hh
  have hKn (t : ℝ) : (∫ w, ‖K t w‖) = ‖v t‖ := by
    simp only [K, norm_mul, Real.norm_eq_abs, abs_of_pos (phiDensity_pos sigma _ hs)]
    rw [integral_const_mul, integral_sub_right_eq_self, phiDensity_integral sigma hs, mul_one]
  have hK : Integrable (Function.uncurry K) (volume.prod volume) := by
    apply (integrable_prod_iff hKm).mpr
    refine ⟨ae_of_all _ hKi, ?_⟩
    simpa only [Function.uncurry, hKn] using hv.norm
  refine ⟨hK.integral_prod_right, ?_⟩
  calc
    _ = ∫ t, ∫ w, K t w := (integral_integral_swap hK).symm
    _ = _ := by
      simp only [K, integral_const_mul, integral_sub_right_eq_self,
        phiDensity_integral sigma hs, mul_one]

/-- Integrating the pointwise contraction gives the observed energy bound in equation (18). [Under the stated conditions](hyp:hd,hk,hs). [This is the stated conclusion](goal). -/
-- @node: gaussian_design_observed_energy_contraction
lemma gaussian_design_observed_energy_contraction (kappa sigma : ℝ)
    (hk : kappa ∈ Icc (0 : ℝ) 2) (hs : sigma ∈ Ioc (0 : ℝ) (1/4))
    (delta : ℝ → ℝ) (hd : Continuous delta) :
    (∫ w, (smoothSigned sigma (fun t => witnessDesignDensity kappa t * delta t) w)^2 /
      smoothSigned sigma (witnessDesignDensity kappa) w) ≤
        ∫ t, witnessDesignDensity kappa t * (delta t)^2 := by
  have hv := witnessDesignDensity_mul_continuous_integrable kappa hk.1 delta hd
  have hv2 := witnessDesignDensity_mul_continuous_integrable kappa hk.1 _ (hd.pow 2)
  have hmass := lower_smoothSigned_integrable_integral sigma hs.1 _ hv2
  have henergy := gaussian_observed_energy_integrable kappa sigma (1/2) hk hs
    _ hv (by have hk0 := hk.1; fun_prop) (fun t ht => by
      rw [← neg_div] at ht
      simp only [witnessDesignDensity, if_neg ht, zero_mul])
  calc
    _ ≤ ∫ w, smoothSigned sigma (fun t => witnessDesignDensity kappa t * (delta t)^2) w :=
      integral_mono henergy hmass.1
        (fun w => gaussian_design_convolution_cauchy_schwarz kappa sigma w hk hs delta hd)
    _ = _ := hmass.2

/-- The direct threshold pair has the actual observed one-record budget at every positive noise scale. [Under the stated conditions](hyp:h,he,hh,hk,hs,hrange,hformula). [This is the stated conclusion](goal). -/
-- @node: direct_profile_pair_observed_energy_bound
lemma direct_profile_pair_observed_energy_bound {S : Type*} [MeasurableSpace S]
    (E : PathSpace S) (beta kappa sigma epsilon h : ℝ)
    (hk : kappa ∈ Icc (0 : ℝ) 2) (hs : sigma ∈ Ioc (0 : ℝ) (1/4))
    (he : 0 ≤ epsilon) (hh : 0 < h) (muPlus muMinus : ThresholdProfile)
    (hrange : ∀ a, (muPlus a : ℝ) ∈ Icc (1/8) (7/8) ∧
      (muMinus a : ℝ) ∈ Icc (1/8) (7/8))
    (hformula : ∀ a : Dose,
      (muPlus a : ℝ) = 1/2 + directPerturbation beta epsilon h ((a : ℝ)-a0) ∧
      (muMinus a : ℝ) = 1/2 - directPerturbation beta epsilon h ((a : ℝ)-a0)) :
    Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muPlus))
      (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤
        (8*(kappa+1)*2^kappa*epsilon^2)*h^(2*beta+kappa+1) ∧
    Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muMinus))
      (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤
        (8*(kappa+1)*2^kappa*epsilon^2)*h^(2*beta+kappa+1) := by
  have hsingle (mu : ThresholdProfile) (delta : ℝ → ℝ) (hd : Continuous delta)
      (hr : ∀ a, (mu a : ℝ) ∈ Icc (1/8) (7/8))
      (hf : ∀ a : Dose, (mu a : ℝ) = 1/2 + delta ((a : ℝ)-a0))
      (henergy : (∫ t, witnessDesignDensity kappa t * (delta t)^2) ≤
        (2*(kappa+1)*2^kappa*epsilon^2)*h^(2*beta+kappa+1)) :
      Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa mu))
        (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤
          (8*(kappa+1)*2^kappa*epsilon^2)*h^(2*beta+kappa+1) := by
    have hchi := (observed_marked_chiSq_identity E kappa sigma hk hs mu hr).2
    change Causalean.Stat.chiSqDiv _ _ =
      4 * ∫ w, (smoothSigned sigma (markedSignedProfile kappa mu) w)^2 /
        smoothSigned sigma (witnessDesignDensity kappa) w at hchi
    rw [markedSignedProfile_eq_perturbation kappa mu delta hf] at hchi
    rw [hchi]
    have hc := gaussian_design_observed_energy_contraction kappa sigma hk hs delta hd
    nlinarith
  constructor
  · exact hsingle muPlus (directPerturbation beta epsilon h)
      (directPerturbation_continuous beta epsilon h hh) (fun a => (hrange a).1)
      (fun a => (hformula a).1) (directPerturbation_quadratic_energy_le beta kappa epsilon h hk.1 he hh)
  · refine hsingle muMinus (fun t => -directPerturbation beta epsilon h t)
      (directPerturbation_continuous beta epsilon h hh).neg (fun a => (hrange a).2) ?_ ?_
    · intro a
      simpa only [sub_eq_add_neg] using (hformula a).2
    · simpa only [neg_sq] using directPerturbation_quadratic_energy_le beta kappa epsilon h hk.1 he hh

/-- With the direct bandwidth, the observed pair has a sample budget independent of noise and sample size. [Under the stated conditions](hyp:he,hd,hn,hk,hs,hrange,hformula). [This is the stated conclusion](goal). -/
-- @node: direct_profile_pair_observed_sample_budget
lemma direct_profile_pair_observed_sample_budget {S : Type*} [MeasurableSpace S]
    (E : PathSpace S) (beta kappa sigma epsilon : ℝ) (n : ℕ)
    (hk : kappa ∈ Icc (0 : ℝ) 2) (hs : sigma ∈ Ioc (0 : ℝ) (1/4))
    (he : 0 ≤ epsilon) (hd : 0 < effDim beta kappa) (hn : 0 < n)
    (muPlus muMinus : ThresholdProfile)
    (hrange : ∀ a, (muPlus a : ℝ) ∈ Icc (1/8) (7/8) ∧
      (muMinus a : ℝ) ∈ Icc (1/8) (7/8))
    (hformula : ∀ a : Dose,
      (muPlus a : ℝ) = 1/2 + directPerturbation beta epsilon
        (directScale beta kappa n) ((a : ℝ)-a0) ∧
      (muMinus a : ℝ) = 1/2 - directPerturbation beta epsilon
        (directScale beta kappa n) ((a : ℝ)-a0)) :
    (n : ℝ)*Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muPlus))
      (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤
        (8*(kappa+1)*2^kappa)*epsilon^2 ∧
    (n : ℝ)*Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muMinus))
      (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤
        (8*(kappa+1)*2^kappa)*epsilon^2 := by
  have hh : 0 < directScale beta kappa n := by
    unfold directScale
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hb := direct_profile_pair_observed_energy_bound E beta kappa sigma epsilon
    (directScale beta kappa n) hk hs he hh muPlus muMinus hrange hformula
  have hid := lower_direct_scale_sample_identity beta kappa n hd hn
  change (n : ℝ)*(directScale beta kappa n)^(2*beta+kappa+1) = 1 at hid
  constructor
  all_goals
    calc
      _ ≤ (n : ℝ)*((8*(kappa+1)*2^kappa*epsilon^2)*
          (directScale beta kappa n)^(2*beta+kappa+1)) :=
        mul_le_mul_of_nonneg_left (by first | exact hb.1 | exact hb.2) (Nat.cast_nonneg n)
      _ = (8*(kappa+1)*2^kappa)*epsilon^2*
          ((n : ℝ)*(directScale beta kappa n)^(2*beta+kappa+1)) := by ring
      _ = _ := by rw [hid, mul_one]

end CausalSmith.Stat.NoisydoseWeakdesignTransition

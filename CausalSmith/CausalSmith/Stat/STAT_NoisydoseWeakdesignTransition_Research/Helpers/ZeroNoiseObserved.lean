module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.DirectObservedContraction
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.LowerAssembly

/-! The zero-noise observed Bernoulli likelihood and its quadratic energy. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
variable {S : Type*} [MeasurableSpace S]

/-- At zero noise the observed dose directly indexes the Bernoulli likelihood. -/
-- @node: zeroNoiseLikelihood
def zeroNoiseLikelihood (mu : ThresholdProfile) (o : Obs) : ℝ :=
  if o.2.2 = 1 then 2*(mu (Set.projIcc 0 1 zero_le_one o.2.1) : ℝ)
  else 2*(1-(mu (Set.projIcc 0 1 zero_le_one o.2.1) : ℝ))

/-- The zero-noise likelihood is measurable. [This is the stated conclusion](goal). -/
-- @node: zeroNoiseLikelihood_measurable
@[fun_prop] lemma zeroNoiseLikelihood_measurable (mu : ThresholdProfile) :
    Measurable (zeroNoiseLikelihood mu) := by
  unfold zeroNoiseLikelihood
  apply Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
  all_goals fun_prop

/-- The zero-noise likelihood is nonnegative on the full observed space. [This is the stated conclusion](goal). -/
-- @node: zeroNoiseLikelihood_nonneg
lemma zeroNoiseLikelihood_nonneg (mu : ThresholdProfile) (o : Obs) :
    0 ≤ zeroNoiseLikelihood mu o := by
  unfold zeroNoiseLikelihood
  split_ifs
  · exact mul_nonneg (by norm_num) (mu _).property.1
  · exact mul_nonneg (by norm_num) (sub_nonneg.mpr (mu _).property.2)

/-- The exact zero-noise observed law is a likelihood tilt of the half-success reference. [Under the stated conditions](hyp:hk). [This is the stated conclusion](goal). -/
-- @node: obsLaw_zero_witness_withDensity
lemma obsLaw_zero_witness_withDensity (E : PathSpace S) (kappa : ℝ)
    (hk : 0 ≤ kappa) (mu : ThresholdProfile) :
    obsLaw 0 (lowerWitnessLaw E kappa mu) =
      (obsLaw 0 (lowerWitnessLaw E kappa referenceProfile)).withDensity
        (fun o => ENNReal.ofReal (zeroNoiseLikelihood mu o)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_withDensity_eq_lintegral_mul _
    (zeroNoiseLikelihood_measurable mu).ennreal_ofReal hf,
    obsLaw_witness_lintegral E kappa 0 hk mu f hf,
    obsLaw_witness_lintegral E kappa 0 hk referenceProfile _
      ((zeroNoiseLikelihood_measurable mu).ennreal_ofReal.mul hf)]
  apply lintegral_congr; intro x
  apply lintegral_congr; intro a
  apply lintegral_congr; intro z
  simp only [Pi.mul_apply, zero_mul, add_zero, zeroNoiseLikelihood, Set.projIcc_of_mem zero_le_one a.property,
    if_pos rfl, show (0 : ℝ) ≠ 1 by norm_num, if_false,
    referenceProfile, ContinuousMap.const_apply]
  norm_num only [Set.projIcc, max_eq_right, min_eq_right, ENNReal.ofReal_mul,
    ENNReal.ofReal_ofNat]
  rw [← mul_assoc, ← mul_assoc]
  norm_num [ENNReal.ofReal_div_of_pos]
  simp [← mul_assoc, ENNReal.inv_mul_cancel]

/-- Radon--Nikodym uniqueness identifies the zero-noise observed likelihood. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hk). -/
-- @node: obsLaw_zero_witness_rnDeriv_toReal
lemma obsLaw_zero_witness_rnDeriv_toReal (E : PathSpace S) (kappa : ℝ)
    (hk : kappa ∈ Icc (0 : ℝ) 2) (mu : ThresholdProfile) :
    (fun o => ((obsLaw 0 (lowerWitnessLaw E kappa mu)).rnDeriv
      (obsLaw 0 (lowerWitnessLaw E kappa referenceProfile)) o).toReal) =ᵐ[
        obsLaw 0 (lowerWitnessLaw E kappa referenceProfile)] zeroNoiseLikelihood mu := by
  letI := lowerWitnessLaw_probability E kappa hk referenceProfile
  have hobs : Measurable (obsMap (S := S) 0) := by
    unfold obsMap contaminatedDose; fun_prop
  letI : IsProbabilityMeasure (obsLaw 0 (lowerWitnessLaw E kappa referenceProfile)) :=
    Measure.isProbabilityMeasure_map hobs.aemeasurable
  rw [obsLaw_zero_witness_withDensity E kappa hk.1 mu]
  filter_upwards [Measure.rnDeriv_withDensity
    (obsLaw 0 (lowerWitnessLaw E kappa referenceProfile))
    (zeroNoiseLikelihood_measurable mu).ennreal_ofReal] with o ho
  rw [ho, ENNReal.toReal_ofReal (zeroNoiseLikelihood_nonneg mu o)]

/-- The zero-noise version of (12) is exactly the latent quadratic energy, evaluated in the observed experiment. [Under the stated conditions](hyp:hd,hk,hf). [This is the stated conclusion](goal). -/
-- @node: observed_zero_marked_chiSq_identity
lemma observed_zero_marked_chiSq_identity (E : PathSpace S) (kappa : ℝ)
    (hk : kappa ∈ Icc (0 : ℝ) 2) (mu : ThresholdProfile)
    (delta : ℝ → ℝ) (hd : Continuous delta)
    (hf : ∀ a : Dose, (mu a : ℝ) = 1/2 + delta ((a : ℝ)-a0)) :
    Causalean.Stat.chiSqDiv (obsLaw 0 (lowerWitnessLaw E kappa mu))
      (obsLaw 0 (lowerWitnessLaw E kappa referenceProfile)) =
        4 * ∫ t, witnessDesignDensity kappa t * (delta t)^2 := by
  let R := obsLaw 0 (lowerWitnessLaw E kappa referenceProfile)
  let D := doseVolume.withDensity (fun a : Dose =>
    ENNReal.ofReal (witnessDesignDensity kappa ((a : ℝ)-a0)))
  let f := zeroNoiseLikelihood mu
  have hm : Measurable (fun o => (f o-1)^2) := by dsimp [f]; fun_prop
  have hi : Integrable (fun t => witnessDesignDensity kappa t * (delta t)^2) :=
    witnessDesignDensity_mul_continuous_integrable kappa hk.1 _ (hd.pow 2)
  have hchi : Causalean.Stat.chiSqDiv (obsLaw 0 (lowerWitnessLaw E kappa mu)) R =
      ∫ o, (f o-1)^2 ∂ R := by
    apply integral_congr_ae
    filter_upwards [obsLaw_zero_witness_rnDeriv_toReal E kappa hk mu] with o ho
    rw [ho]
  have hmarks (x : Bool) (a : Dose) :
      (f (x,(a : ℝ),1)-1)^2 = 4*(delta ((a : ℝ)-a0))^2 ∧
      (f (x,(a : ℝ),0)-1)^2 = 4*(delta ((a : ℝ)-a0))^2 := by
    dsimp [f, zeroNoiseLikelihood]
    simp only [if_pos rfl, show (0 : ℝ) ≠ 1 by norm_num, if_false,
      Set.projIcc_of_mem zero_le_one a.property, hf a, ite_true, ite_false]
    constructor <;> ring
  have hlin : (∫⁻ o, ENNReal.ofReal ((f o-1)^2) ∂ R) =
      ∫⁻ t, ENNReal.ofReal (4*(witnessDesignDensity kappa t*(delta t)^2)) := by
    rw [obsLaw_witness_lintegral E kappa 0 hk.1 referenceProfile _ hm.ennreal_ofReal]
    have he (x : Bool) (a : Dose) (z : ℝ) :
        ENNReal.ofReal (referenceProfile a : ℝ) *
            ENNReal.ofReal ((f (x,(a : ℝ)+0*z,1)-1)^2) +
          ENNReal.ofReal (1-(referenceProfile a : ℝ)) *
            ENNReal.ofReal ((f (x,(a : ℝ)+0*z,0)-1)^2) =
          ENNReal.ofReal (4*(delta ((a : ℝ)-a0))^2) := by
      simp only [zero_mul, add_zero, (hmarks x a).1, (hmarks x a).2,
        referenceProfile, ContinuousMap.const_apply]
      norm_num [Set.projIcc, ← add_mul, ENNReal.ofReal_div_of_pos]
      rw [ENNReal.inv_two_add_inv_two, one_mul]
    simp_rw [he]
    simp only [lintegral_const, measure_univ, mul_one]
    simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _),
      smul_eq_mul, mul_one, ENNReal.inv_two_add_inv_two]
    simp only [one_div, ENNReal.inv_two_add_inv_two, mul_one]
    have hmap := witnessDose_map_centered kappa hk.1
    have htransport := lintegral_map
      (show Measurable (fun t => ENNReal.ofReal (4*(delta t)^2)) by fun_prop)
      (show Measurable (fun a : Dose => (a : ℝ)-a0) by fun_prop) (μ := D)
    rw [hmap] at htransport
    rw [← htransport, lintegral_withDensity_eq_lintegral_mul _
      (by have hk0 := hk.1; fun_prop) (by fun_prop)]
    rw [← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr; intro t
    by_cases ht : t ∈ Icc (-1/2 : ℝ) (1/2)
    · rw [indicator_of_mem ht]
      simp only [Pi.mul_apply]
      rw [← ENNReal.ofReal_mul (witnessDesignDensity_nonneg kappa t hk.1)]
      congr 1
      ring
    · rw [indicator_of_notMem ht]
      rw [witnessDesignDensity, if_neg ht]
      simp
  rw [hchi, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun o => sq_nonneg (f o-1)))
    hm.aestronglyMeasurable, hlin,
    ← ofReal_integral_eq_lintegral_ofReal (hi.const_mul 4)
      (ae_of_all _ (fun t => mul_nonneg (by norm_num)
        (mul_nonneg (witnessDesignDensity_nonneg kappa t hk.1) (sq_nonneg _)))),
    ENNReal.toReal_ofReal (integral_nonneg (fun t => mul_nonneg (by norm_num)
      (mul_nonneg (witnessDesignDensity_nonneg kappa t hk.1) (sq_nonneg _)))),
    integral_const_mul]

/-- Equation (18) holds for the observed direct profiles uniformly down to zero noise. [Under the stated conditions](hyp:h,he,hh,hk,hs,hrange,hformula). [This is the stated conclusion](goal). -/
-- @node: direct_profile_pair_observed_energy_bound_nonneg_noise
lemma direct_profile_pair_observed_energy_bound_nonneg_noise (E : PathSpace S)
    (beta kappa sigma epsilon h : ℝ)
    (hk : kappa ∈ Icc (0 : ℝ) 2) (hs : sigma ∈ Icc (0 : ℝ) (1/4))
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
  by_cases hs0 : sigma = 0
  · subst sigma
    have hp := observed_zero_marked_chiSq_identity E kappa hk muPlus
      (directPerturbation beta epsilon h) (directPerturbation_continuous beta epsilon h hh)
      (fun a => (hformula a).1)
    have hm := observed_zero_marked_chiSq_identity E kappa hk muMinus
      (fun t => -directPerturbation beta epsilon h t)
      (directPerturbation_continuous beta epsilon h hh).neg
      (fun a => by simpa only [sub_eq_add_neg] using (hformula a).2)
    simp only [neg_sq] at hm
    have hb := directPerturbation_quadratic_energy_le beta kappa epsilon h hk.1 he hh
    constructor <;> nlinarith
  · exact direct_profile_pair_observed_energy_bound E beta kappa sigma epsilon h hk
      ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), hs.2⟩ he hh muPlus muMinus hrange hformula

/-- The uniform direct sample budget includes the zero-noise boundary. [Under the stated conditions](hyp:he,hd,hn,hk,hs,hrange,hformula). [This is the stated conclusion](goal). -/
-- @node: direct_profile_pair_observed_sample_budget_nonneg_noise
lemma direct_profile_pair_observed_sample_budget_nonneg_noise (E : PathSpace S)
    (beta kappa sigma epsilon : ℝ) (n : ℕ)
    (hk : kappa ∈ Icc (0 : ℝ) 2) (hs : sigma ∈ Icc (0 : ℝ) (1/4))
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
  have hb := direct_profile_pair_observed_energy_bound_nonneg_noise E beta kappa sigma epsilon
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

/-- The direct construction gives observed product total variation at most τ, including zero noise, under the common amplitude budget log(1+τ²) (51). [Under the stated conditions](hyp:he,hd,hn,hk,hs,htau,hbudget,hrange,hformula). [This is the stated conclusion](goal). -/
-- @node: direct_profile_pair_observed_tv_bound
lemma direct_profile_pair_observed_tv_bound (E : PathSpace S)
    (beta kappa sigma epsilon : ℝ) (n : ℕ)
    (hk : kappa ∈ Icc (0 : ℝ) 2) (hs : sigma ∈ Icc (0 : ℝ) (1/4))
    (he : 0 ≤ epsilon) (hd : 0 < effDim beta kappa) (hn : 0 < n)
    (tau : ℝ) (htau : 0 ≤ tau)
    (hbudget : (8*(kappa+1)*2^kappa)*epsilon^2 ≤ Real.log (1 + tau^2))
    (muPlus muMinus : ThresholdProfile)
    (hrange : ∀ a, (muPlus a : ℝ) ∈ Icc (1/8) (7/8) ∧
      (muMinus a : ℝ) ∈ Icc (1/8) (7/8))
    (hformula : ∀ a : Dose,
      (muPlus a : ℝ) = 1/2 + directPerturbation beta epsilon
        (directScale beta kappa n) ((a : ℝ)-a0) ∧
      (muMinus a : ℝ) = 1/2 - directPerturbation beta epsilon
        (directScale beta kappa n) ((a : ℝ)-a0)) :
    Causalean.Stat.tvDist (experiment n sigma (lowerWitnessLaw E kappa muPlus))
      (experiment n sigma (lowerWitnessLaw E kappa muMinus)) ≤ tau := by
  have hb := direct_profile_pair_observed_sample_budget_nonneg_noise E beta kappa sigma
    epsilon n hk hs he hd hn muPlus muMinus hrange hformula
  exact lower_observed_experiment_tv_le E kappa sigma hk muPlus muMinus n tau htau
    (obsLaw_witness_ac E kappa sigma hk hs muPlus (fun a => (hrange a).1))
    (obsLaw_witness_ac E kappa sigma hk hs muMinus (fun a => (hrange a).2))
    (obsLaw_witness_sqdev_integrable E kappa sigma hk hs muPlus (fun a => (hrange a).1))
    (obsLaw_witness_sqdev_integrable E kappa sigma hk hs muMinus (fun a => (hrange a).2))
    (hb.1.trans hbudget) (hb.2.trans hbudget)

end CausalSmith.Stat.NoisydoseWeakdesignTransition

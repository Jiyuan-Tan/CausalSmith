module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.GaussianMomentSeries
public import Mathlib.MeasureTheory.Group.LIntegral

/-! The observed marked likelihood ratio and its exact chi-square energy (12). -/
@[expose] public section
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
variable {S : Type*} [MeasurableSpace S]

/-- The centered signed density of a threshold profile. -/
-- @node: markedSignedProfile
def markedSignedProfile (kappa : ℝ) (mu : ThresholdProfile) (t : ℝ) : ℝ :=
  witnessDesignDensity kappa t *
    ((mu (Set.projIcc 0 1 zero_le_one (t+a0)) : ℝ)-1/2)

/-- The success mark adds the centered convolution; the failure mark subtracts it. -/
-- @node: markedLikelihood
def markedLikelihood (kappa sigma : ℝ) (mu : ThresholdProfile) (o : Obs) : ℝ :=
  1 + (if o.2.2 = 1 then 2 else -2) *
    smoothSigned sigma (markedSignedProfile kappa mu) (o.2.1-a0) /
      smoothSigned sigma (witnessDesignDensity kappa) (o.2.1-a0)

/-- The reference has equal success and failure densities. [Under the stated conditions](hyp:hkappa,hsigma,f,hf). [This is the stated conclusion](goal). [Under the stated conditions](hyp:hkappa,hsigma,hf). [This is the stated conclusion](goal). [Under the stated conditions](hyp:hkappa,hsigma,hf). [This is the stated conclusion](goal). [Under the stated conditions](hyp:hkappa,hsigma,hf). [This is the stated conclusion](goal). -/
-- @node: obsLaw_reference_density_lintegral
lemma obsLaw_reference_density_lintegral (E : PathSpace S) (kappa sigma : ℝ)
    (hkappa : 0 ≤ kappa) (hsigma : 0 < sigma)
    (f : Obs → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ o, f o ∂obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) =
      ∫⁻ x, ∫⁻ w,
        ENNReal.ofReal (smoothSigned sigma (witnessDesignDensity kappa) (w-a0)/2) *
          (f (x,w,1) + f (x,w,0)) ∂volume
        ∂((1/2 : ℝ≥0∞) • Measure.dirac false + (1/2 : ℝ≥0∞) • Measure.dirac true) := by
  rw [obsLaw_witness_signed_density_lintegral E kappa sigma hkappa hsigma referenceProfile f hf]
  have hz : (fun t => witnessDesignDensity kappa t *
      ((referenceProfile (Set.projIcc 0 1 zero_le_one (t+a0)) : ℝ)-1/2)) = 0 := by
    funext t
    norm_num [referenceProfile, Set.projIcc]
  rw [hz]
  simp only [smoothSigned, Pi.zero_apply, zero_mul, integral_zero, add_zero, sub_zero,
    mul_add]

/-- The two mark densities are nonnegative because they are convolutions of nonnegative latent densities. [Under the stated conditions](hyp:hkappa,hsigma). [This is the stated conclusion](goal). -/
-- @node: marked_densities_nonneg
lemma marked_densities_nonneg (kappa sigma w : ℝ) (hkappa : 0 ≤ kappa)
    (hsigma : 0 < sigma) (mu : ThresholdProfile) :
    0 ≤ smoothSigned sigma (witnessDesignDensity kappa) w / 2 +
        smoothSigned sigma (markedSignedProfile kappa mu) w ∧
    0 ≤ smoothSigned sigma (witnessDesignDensity kappa) w / 2 -
        smoothSigned sigma (markedSignedProfile kappa mu) w := by
  unfold markedSignedProfile
  rw [← marked_success_density_eq kappa sigma w hkappa hsigma mu,
    ← marked_failure_density_eq kappa sigma w hkappa hsigma mu]
  constructor
  · apply integral_nonneg
    intro t
    exact mul_nonneg (mul_nonneg (witnessDesignDensity_nonneg kappa t hkappa)
      (mu _).property.1) (phiDensity_pos sigma _ hsigma).le
  · apply integral_nonneg
    intro t
    exact mul_nonneg (mul_nonneg (witnessDesignDensity_nonneg kappa t hkappa)
      (sub_nonneg.mpr (mu _).property.2)) (phiDensity_pos sigma _ hsigma).le

/-- The likelihood is a measurable real function on the entire observed space. [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: markedLikelihood_measurable
@[fun_prop] lemma markedLikelihood_measurable (kappa sigma : ℝ)
    (hkappa : 0 ≤ kappa) (mu : ThresholdProfile) :
    Measurable (markedLikelihood kappa sigma mu) := by
  have hm : Measurable (fun o : Obs => if o.2.2 = 1 then (2 : ℝ) else -2) :=
    Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
      measurable_const measurable_const
  unfold markedLikelihood markedSignedProfile
  fun_prop

/-- Multiplying the reference mark density by the likelihood recovers each alternative mark. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hkappa,hsigma). -/
-- @node: markedLikelihood_density_mul
lemma markedLikelihood_density_mul (kappa sigma w : ℝ)
    (hkappa : kappa ∈ Icc (0 : ℝ) 2) (hsigma : sigma ∈ Ioc (0 : ℝ) (1/4))
    (mu : ThresholdProfile) (x : Bool) :
    ENNReal.ofReal (smoothSigned sigma (witnessDesignDensity kappa) (w-a0)/2) *
      ENNReal.ofReal (markedLikelihood kappa sigma mu (x,w,1)) =
        ENNReal.ofReal (smoothSigned sigma (witnessDesignDensity kappa) (w-a0)/2 +
          smoothSigned sigma (markedSignedProfile kappa mu) (w-a0)) ∧
    ENNReal.ofReal (smoothSigned sigma (witnessDesignDensity kappa) (w-a0)/2) *
      ENNReal.ofReal (markedLikelihood kappa sigma mu (x,w,0)) =
        ENNReal.ofReal (smoothSigned sigma (witnessDesignDensity kappa) (w-a0)/2 -
          smoothSigned sigma (markedSignedProfile kappa mu) (w-a0)) := by
  have hp := (gaussian_design_density_lower kappa sigma hkappa hsigma (w-a0)).1
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  constructor <;> congr 1 <;> simp only [markedLikelihood, Prod.fst, Prod.snd, if_true,
    show (0 : ℝ) ≠ 1 by norm_num, if_false] <;> field_simp [ne_of_gt hp] <;> ring

/-- The observed alternative is the reference law weighted by its explicit marked likelihood. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hkappa,hsigma). -/
-- @node: obsLaw_witness_withDensity
lemma obsLaw_witness_withDensity (E : PathSpace S) (kappa sigma : ℝ)
    (hkappa : kappa ∈ Icc (0 : ℝ) 2) (hsigma : sigma ∈ Ioc (0 : ℝ) (1/4))
    (mu : ThresholdProfile) :
    obsLaw sigma (lowerWitnessLaw E kappa mu) =
      (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)).withDensity
        (fun o => ENNReal.ofReal (markedLikelihood kappa sigma mu o)) := by
  have hk : 0 ≤ kappa := hkappa.1
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hf,
    obsLaw_reference_density_lintegral E kappa sigma hkappa.1 hsigma.1 _ (by fun_prop),
    obsLaw_witness_signed_density_lintegral E kappa sigma hkappa.1 hsigma.1 mu f hf]
  apply lintegral_congr
  intro x
  apply lintegral_congr
  intro w
  symm
  simp only [Pi.mul_apply]
  change _ = ENNReal.ofReal (_ + smoothSigned sigma (markedSignedProfile kappa mu) (w-a0)) * _ +
    ENNReal.ofReal (_ - smoothSigned sigma (markedSignedProfile kappa mu) (w-a0)) * _
  rw [mul_add, ← mul_assoc, ← mul_assoc,
    (markedLikelihood_density_mul kappa sigma w hkappa hsigma mu x).1,
    (markedLikelihood_density_mul kappa sigma w hkappa hsigma mu x).2]

/-- The likelihood stays nonnegative for either choice of mark. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hkappa,hsigma). -/
-- @node: markedLikelihood_nonneg
lemma markedLikelihood_nonneg (kappa sigma : ℝ)
    (hkappa : kappa ∈ Icc (0 : ℝ) 2) (hsigma : sigma ∈ Ioc (0 : ℝ) (1/4))
    (mu : ThresholdProfile) (o : Obs) : 0 ≤ markedLikelihood kappa sigma mu o := by
  have hp := (gaussian_design_density_lower kappa sigma hkappa hsigma (o.2.1-a0)).1
  have hd := marked_densities_nonneg kappa sigma (o.2.1-a0) hkappa.1 hsigma.1 mu
  unfold markedLikelihood
  split_ifs
  · have he : 1 + 2 * smoothSigned sigma (markedSignedProfile kappa mu) (o.2.1-a0) /
        smoothSigned sigma (witnessDesignDensity kappa) (o.2.1-a0) =
      (smoothSigned sigma (witnessDesignDensity kappa) (o.2.1-a0) +
        2*smoothSigned sigma (markedSignedProfile kappa mu) (o.2.1-a0)) /
          smoothSigned sigma (witnessDesignDensity kappa) (o.2.1-a0) := by
      field_simp <;> ring
    rw [he]
    exact div_nonneg (by linarith [hd.1]) hp.le
  · have he : 1 + (-2) * smoothSigned sigma (markedSignedProfile kappa mu) (o.2.1-a0) /
        smoothSigned sigma (witnessDesignDensity kappa) (o.2.1-a0) =
      (smoothSigned sigma (witnessDesignDensity kappa) (o.2.1-a0) -
        2*smoothSigned sigma (markedSignedProfile kappa mu) (o.2.1-a0)) /
          smoothSigned sigma (witnessDesignDensity kappa) (o.2.1-a0) := by
      field_simp <;> ring
    rw [he]
    exact div_nonneg (by linarith [hd.2]) hp.le

/-- Radon--Nikodym uniqueness identifies the real observed likelihood with the explicit mark ratio. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hkappa,hsigma). -/
-- @node: obsLaw_witness_rnDeriv_toReal
lemma obsLaw_witness_rnDeriv_toReal (E : PathSpace S) (kappa sigma : ℝ)
    (hkappa : kappa ∈ Icc (0 : ℝ) 2) (hsigma : sigma ∈ Ioc (0 : ℝ) (1/4))
    (mu : ThresholdProfile) :
    (fun o => ((obsLaw sigma (lowerWitnessLaw E kappa mu)).rnDeriv
      (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) o).toReal) =ᵐ[
        obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)] markedLikelihood kappa sigma mu := by
  letI := lowerWitnessLaw_probability E kappa hkappa referenceProfile
  have hobs : Measurable (obsMap (S := S) sigma) := by
    unfold obsMap contaminatedDose; fun_prop
  letI : IsProbabilityMeasure (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) :=
    Measure.isProbabilityMeasure_map hobs.aemeasurable
  rw [obsLaw_witness_withDensity E kappa sigma hkappa hsigma mu]
  have h := Measure.rnDeriv_withDensity
    (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile))
    ((markedLikelihood_measurable kappa sigma hkappa.1 mu).ennreal_ofReal)
  filter_upwards [h] with o ho
  rw [ho, ENNReal.toReal_ofReal (markedLikelihood_nonneg kappa sigma hkappa hsigma mu o)]

/-- Each reference mark contributes twice the signed-density energy to chi-square. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hkappa,hsigma). -/
-- @node: markedLikelihood_sq_density
lemma markedLikelihood_sq_density (kappa sigma w : ℝ)
    (hkappa : kappa ∈ Icc (0 : ℝ) 2) (hsigma : sigma ∈ Ioc (0 : ℝ) (1/4))
    (mu : ThresholdProfile) (x : Bool) :
    ENNReal.ofReal (smoothSigned sigma (witnessDesignDensity kappa) (w-a0)/2) *
      (ENNReal.ofReal ((markedLikelihood kappa sigma mu (x,w,1)-1)^2) +
       ENNReal.ofReal ((markedLikelihood kappa sigma mu (x,w,0)-1)^2)) =
      ENNReal.ofReal (4 * (smoothSigned sigma (markedSignedProfile kappa mu) (w-a0))^2 /
        smoothSigned sigma (witnessDesignDensity kappa) (w-a0)) := by
  have hp := (gaussian_design_density_lower kappa sigma hkappa hsigma (w-a0)).1
  rw [mul_add, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  simp only [markedLikelihood, Prod.fst, Prod.snd, if_true,
    show (0 : ℝ) ≠ 1 by norm_num, if_false]
  field_simp [ne_of_gt hp]
  ring

/-- The exact observed marked-law chi-square formula and finiteness, rather than an oracle-treatment distance. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hkappa,hsigma,hrange). -/
-- @node: observed_marked_chiSq_identity
lemma observed_marked_chiSq_identity (E : PathSpace S) (kappa sigma : ℝ)
    (hkappa : kappa ∈ Icc (0 : ℝ) 2) (hsigma : sigma ∈ Ioc (0 : ℝ) (1/4))
    (mu : ThresholdProfile) (hrange : ∀ a, (mu a : ℝ) ∈ Icc (1/8) (7/8)) :
    let v := fun t => witnessDesignDensity kappa t *
      ((mu (Set.projIcc 0 1 zero_le_one (t+a0)) : ℝ)-1/2)
    let pV := smoothSigned sigma (witnessDesignDensity kappa)
    Integrable (fun w => (smoothSigned sigma v w)^2 / pV w) ∧
    Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa mu))
      (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) =
        4 * ∫ w, (smoothSigned sigma v w)^2 / pV w := by
  refine ⟨marked_profile_energy_integrable kappa sigma hkappa hsigma mu, ?_⟩
  have hk : 0 ≤ kappa := hkappa.1
  let R := obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)
  let f := markedLikelihood kappa sigma mu
  let e := fun w => (smoothSigned sigma (markedSignedProfile kappa mu) w)^2 /
    smoothSigned sigma (witnessDesignDensity kappa) w
  have hm : Measurable (fun o => (f o-1)^2) := by
    dsimp [f]
    fun_prop
  have he : Integrable e := marked_profile_energy_integrable kappa sigma hkappa hsigma mu
  have hen : ∀ w, 0 ≤ e w := fun w => div_nonneg (sq_nonneg _)
    (gaussian_design_density_lower kappa sigma hkappa hsigma w).1.le
  have hchi : Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa mu)) R =
      ∫ o, (f o-1)^2 ∂ R := by
    apply integral_congr_ae
    filter_upwards [obsLaw_witness_rnDeriv_toReal E kappa sigma hkappa hsigma mu] with o ho
    rw [ho]
  have hlin : (∫⁻ o, ENNReal.ofReal ((f o-1)^2) ∂ R) =
      ∫⁻ w, ENNReal.ofReal (4*e w) := by
    rw [obsLaw_reference_density_lintegral E kappa sigma hk hsigma.1 _ hm.ennreal_ofReal]
    have hi : ∀ x : Bool,
        (∫⁻ w, ENNReal.ofReal (smoothSigned sigma (witnessDesignDensity kappa) (w-a0)/2) *
          (ENNReal.ofReal ((f (x,w,1)-1)^2) + ENNReal.ofReal ((f (x,w,0)-1)^2))) =
          ∫⁻ w, ENNReal.ofReal (4*e w) := by
      intro x
      calc
        _ = ∫⁻ w, ENNReal.ofReal (4*e (w-a0)) := by
          apply lintegral_congr
          intro w
          convert markedLikelihood_sq_density kappa sigma w hkappa hsigma mu x using 1 <;>
            dsimp [f, e] <;> congr 1 <;> ring
        _ = _ := lintegral_sub_right_eq_self (μ := (volume : Measure ℝ)) (fun w => ENNReal.ofReal (4*e w)) a0
    simp only [hi, lintegral_const, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
    norm_num
    rw [ENNReal.inv_two_add_inv_two, mul_one]
  rw [hchi, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun o => sq_nonneg (f o-1)))
    hm.aestronglyMeasurable, hlin,
    ← ofReal_integral_eq_lintegral_ofReal (he.const_mul 4)
      (ae_of_all _ (fun w => mul_nonneg (by norm_num) (hen w))),
    ENNReal.toReal_ofReal (integral_nonneg (fun w => mul_nonneg (by norm_num) (hen w))),
    integral_const_mul]
  rfl

end CausalSmith.Stat.NoisydoseWeakdesignTransition

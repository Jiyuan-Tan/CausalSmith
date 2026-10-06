module

public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.GaussianEnergy

/-! Finiteness and moment-tail control of the observed Gaussian weighted energy. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- A measurable signed input gives a measurable Gaussian convolution. [Under the stated conditions](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: smoothSigned_measurable
@[fun_prop] lemma smoothSigned_measurable (sigma : ℝ) (v : ℝ → ℝ)
    (hv : Measurable v) : Measurable (smoothSigned sigma v) := by
  have hm : Measurable (fun p : ℝ × ℝ => v p.2 * phiDensity sigma (p.1-p.2)) := by
    unfold phiDensity
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- Gaussian reference domination converts compact Gaussian energy to observed energy. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hkappa,hsigma). -/
-- @node: gaussian_observed_energy_le
lemma gaussian_observed_energy_le (kappa sigma w : ℝ)
    (hkappa : kappa ∈ Icc (0 : ℝ) 2) (hsigma : sigma ∈ Ioc (0 : ℝ) (1/4))
    (v : ℝ → ℝ) :
    (smoothSigned sigma v w)^2 / smoothSigned sigma (witnessDesignDensity kappa) w ≤
      (1 / (Real.exp (-1/2)*sigma^(kappa+1))) *
        ((smoothSigned sigma v w)^2 / phiDensity sigma w) := by
  have hb := gaussian_design_density_lower kappa sigma hkappa hsigma w
  have hD : 0 < Real.exp (-1/2)*sigma^(kappa+1) :=
    mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hsigma.1 _)
  calc
    _ ≤ (smoothSigned sigma v w)^2 /
        ((Real.exp (-1/2)*sigma^(kappa+1))*phiDensity sigma w) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hD (phiDensity_pos _ _ hsigma.1)) hb.2
    _ = _ := by ring

/-- Compact signed densities have finite energy under the observed witness density. [Under the stated conditions](hyp:hkappa,hsigma,hv,hm,hsupp). [This is the stated conclusion](goal). -/
-- @node: gaussian_observed_energy_integrable
@[fun_prop] lemma gaussian_observed_energy_integrable (kappa sigma ell : ℝ)
    (hkappa : kappa ∈ Icc (0 : ℝ) 2) (hsigma : sigma ∈ Ioc (0 : ℝ) (1/4))
    (v : ℝ → ℝ) (hv : Integrable v) (hm : Measurable v)
    (hsupp : ∀ t, t ∉ Icc (-ell) ell → v t = 0) :
    Integrable (fun w => (smoothSigned sigma v w)^2 /
      smoothSigned sigma (witnessDesignDensity kappa) w) := by
  have he := (gaussian_convolution_energy_integrable sigma ell hsigma.1 v hv hsupp).const_mul
    (1 / (Real.exp (-1/2)*sigma^(kappa+1)))
  have hm' : AEStronglyMeasurable (fun w => (smoothSigned sigma v w)^2 /
      smoothSigned sigma (witnessDesignDensity kappa) w) volume := by
    exact ((smoothSigned_measurable sigma v hm).pow_const 2).div
      (smoothSigned_measurable sigma _ (witnessDesignDensity_measurable kappa hkappa.1))
      |>.aestronglyMeasurable
  apply he.mono' hm'
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _)
    (gaussian_design_density_lower kappa sigma hkappa hsigma w).1.le)]
  exact gaussian_observed_energy_le kappa sigma w hkappa hsigma v

/-- The constructed threshold profile gives an integrable compact signed density. [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: marked_profile_signed_integrable
@[fun_prop] lemma marked_profile_signed_integrable (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (mu : ThresholdProfile) :
    Integrable (fun t => witnessDesignDensity kappa t *
      ((mu (Set.projIcc 0 1 zero_le_one (t+a0)) : ℝ)-1/2)) := by
  have hc : Continuous (fun t : ℝ => (kappa+1)*2^kappa*|t|^kappa *
      ((mu (Set.projIcc 0 1 zero_le_one (t+a0)) : ℝ)-1/2)) := by
    fun_prop
  have he : (fun t => witnessDesignDensity kappa t *
      ((mu (Set.projIcc 0 1 zero_le_one (t+a0)) : ℝ)-1/2)) =
      (Icc (-1/2 : ℝ) (1/2)).indicator (fun t : ℝ => (kappa+1)*2^kappa*|t|^kappa *
        ((mu (Set.projIcc 0 1 zero_le_one (t+a0)) : ℝ)-1/2)) := by
    funext t
    simp only [witnessDesignDensity, indicator_apply]
    split_ifs <;> simp
  rw [he]
  exact hc.integrableOn_Icc.integrable_indicator measurableSet_Icc

/-- The integrability conclusion in the observed marked-law identity is automatic for its constructed profile. [Under the stated conditions](hyp:hkappa,hsigma). [This is the stated conclusion](goal). -/
-- @node: marked_profile_energy_integrable
@[fun_prop] lemma marked_profile_energy_integrable (kappa sigma : ℝ)
    (hkappa : kappa ∈ Icc (0 : ℝ) 2) (hsigma : sigma ∈ Ioc (0 : ℝ) (1/4))
    (mu : ThresholdProfile) :
    Integrable (fun w =>
      (smoothSigned sigma (fun t => witnessDesignDensity kappa t *
        ((mu (Set.projIcc 0 1 zero_le_one (t+a0)) : ℝ)-1/2)) w)^2 /
      smoothSigned sigma (witnessDesignDensity kappa) w) := by
  apply gaussian_observed_energy_integrable kappa sigma (1/2) hkappa hsigma
    _ (marked_profile_signed_integrable kappa hkappa.1 mu)
  · have hk : 0 ≤ kappa := hkappa.1
    fun_prop
  · intro t ht
    rw [← neg_div] at ht
    simp only [witnessDesignDensity, if_neg ht, zero_mul]

/-- Weighted cancellations control observed Gaussian energy by the factorial tail, with the same tuning data. [Under the stated conditions](hyp:hell,hv,hm,hmom,hkappa,hsigma,hsupp). [This is the stated conclusion](goal). -/
-- @node: gaussian_observed_energy_moment_bound
lemma gaussian_observed_energy_moment_bound (kappa sigma ell : ℝ)
    (hkappa : kappa ∈ Icc (0 : ℝ) 2) (hsigma : sigma ∈ Ioc (0 : ℝ) (1/4))
    (hell : 0 ≤ ell) (J : ℕ) (v : ℝ → ℝ) (hv : Integrable v) (hm : Measurable v)
    (hsupp : ∀ t, t ∉ Icc (-ell) ell → v t = 0)
    (hmom : ∀ j < J, ∫ t, t^j*v t = 0) :
    (∫ w, (smoothSigned sigma v w)^2 / smoothSigned sigma (witnessDesignDensity kappa) w) ≤
      (1 / (Real.exp (-1/2)*sigma^(kappa+1))) * (∫ t, |v t|)^2 * momentTail sigma ell J := by
  have hi := gaussian_observed_energy_integrable kappa sigma ell hkappa hsigma v hv hm hsupp
  have hG := gaussian_convolution_energy_integrable sigma ell hsigma.1 v hv hsupp
  have hc : 0 ≤ 1 / (Real.exp (-1/2)*sigma^(kappa+1)) := by
    exact le_of_lt (one_div_pos.mpr
      (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hsigma.1 _)))
  calc
    _ ≤ ∫ w, (1 / (Real.exp (-1/2)*sigma^(kappa+1))) *
        ((smoothSigned sigma v w)^2 / phiDensity sigma w) :=
      integral_mono hi (hG.const_mul _) (fun w =>
        gaussian_observed_energy_le kappa sigma w hkappa hsigma v)
    _ = (1 / (Real.exp (-1/2)*sigma^(kappa+1))) *
        (∫ w, (smoothSigned sigma v w)^2 / phiDensity sigma w) := integral_const_mul _ _
    _ ≤ _ := by
      rw [gaussian_compact_energy_tail_identity sigma ell hsigma.1 hell J v hv hsupp hmom]
      exact (mul_le_mul_of_nonneg_left
        (compact_signed_moment_tail_bound sigma ell hsigma.1 hell J v hv hsupp) hc).trans_eq
        (mul_assoc _ _ _).symm

end CausalSmith.Stat.NoisydoseWeakdesignTransition

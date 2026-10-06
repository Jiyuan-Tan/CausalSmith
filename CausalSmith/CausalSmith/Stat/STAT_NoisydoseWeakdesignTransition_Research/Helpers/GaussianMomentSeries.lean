module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.MarkedGaussianEnergy
public import Causalean.Stat.Minimax.ChiSquared
public import Mathlib.Analysis.SpecificLimits.Normed

/-! Helpers — GaussianMomentSeries -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
variable {S : Type*} [MeasurableSpace S]


/-- Uniform rank thresholding gives the two-point outcome law. [This is the stated conclusion](goal). -/
-- @node: doseVolume_threshold_map
lemma doseVolume_threshold_map (p : Dose) :
    doseVolume.map (fun u : Dose => if (u : ℝ) ≤ (p : ℝ) then (1 : ℝ) else 0) =
      ENNReal.ofReal (p : ℝ) • Measure.dirac 1 +
        ENNReal.ofReal (1-(p : ℝ)) • Measure.dirac 0 := by
  have hm : Measurable (fun u : Dose => if (u : ℝ) ≤ (p : ℝ) then (1 : ℝ) else 0) := by
    exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
      measurable_const measurable_const
  have hlow : doseVolume {u : Dose | (u : ℝ) ≤ (p : ℝ)} = ENNReal.ofReal (p : ℝ) := by
    rw [doseVolume, comap_subtype_coe_apply measurableSet_Icc]
    have heq : Subtype.val '' {u : Dose | (u : ℝ) ≤ (p : ℝ)} = Icc 0 (p : ℝ) := by
      ext t
      constructor
      · rintro ⟨u, hu, rfl⟩; exact ⟨u.property.1, hu⟩
      · intro ht; exact ⟨⟨t, ⟨ht.1, ht.2.trans p.property.2⟩⟩, ht.2, rfl⟩
    rw [heq, Real.volume_Icc, sub_zero]
  have hhigh : doseVolume {u : Dose | ¬ (u : ℝ) ≤ (p : ℝ)} = ENNReal.ofReal (1-(p : ℝ)) := by
    rw [doseVolume, comap_subtype_coe_apply measurableSet_Icc]
    have heq : Subtype.val '' {u : Dose | ¬ (u : ℝ) ≤ (p : ℝ)} = Ioc (p : ℝ) 1 := by
      ext t
      constructor
      · rintro ⟨u, hu, rfl⟩; exact ⟨lt_of_not_ge hu, u.property.2⟩
      · intro ht; exact ⟨⟨t, ⟨p.property.1.trans ht.1.le, ht.2⟩⟩, not_le_of_gt ht.1, rfl⟩
    rw [heq, Real.volume_Ioc]
  ext B hB
  rw [Measure.map_apply hm hB, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  by_cases h1 : (1 : ℝ) ∈ B <;> by_cases h0 : (0 : ℝ) ∈ B
  · have heq : (fun u : Dose => if (u : ℝ) ≤ (p : ℝ) then (1 : ℝ) else 0) ⁻¹' B = univ := by
      ext u; simp only [mem_preimage, mem_univ, iff_true]; split <;> assumption
    rw [heq]
    letI := doseVolume_probability
    simp only [measure_univ, Measure.dirac_apply_of_mem h1, Measure.dirac_apply_of_mem h0,
      smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add p.property.1 (sub_nonneg.mpr p.property.2)]
    simp
  · have heq : (fun u : Dose => if (u : ℝ) ≤ (p : ℝ) then (1 : ℝ) else 0) ⁻¹' B =
        {u : Dose | (u : ℝ) ≤ (p : ℝ)} := by
      ext u; simp only [mem_preimage, mem_setOf_eq]; split_ifs <;> simp_all
    rw [heq, hlow]
    simp [Measure.dirac_apply' _ hB, h1, h0]
  · have heq : (fun u : Dose => if (u : ℝ) ≤ (p : ℝ) then (1 : ℝ) else 0) ⁻¹' B =
        {u : Dose | ¬ (u : ℝ) ≤ (p : ℝ)} := by
      ext u; simp only [mem_preimage, mem_setOf_eq]; split_ifs <;> simp_all
    rw [heq, hhigh]
    simp [Measure.dirac_apply' _ hB, h1, h0]
  · have heq : (fun u : Dose => if (u : ℝ) ≤ (p : ℝ) then (1 : ℝ) else 0) ⁻¹' B = ∅ := by
      ext u; simp only [mem_preimage, mem_empty_iff_false, iff_false]; split <;> assumption
    rw [heq]
    simp [Measure.dirac_apply' _ hB, h1, h0]

/-- Integrating out the independent rank exposes the two observed Bernoulli marks. [Under the stated conditions](hyp:hkappa,f,hf). [This is the stated conclusion](goal). -/
-- @node: obsLaw_witness_lintegral
lemma obsLaw_witness_lintegral (E : PathSpace S) (kappa sigma : ℝ)
    (hkappa : 0 ≤ kappa) (mu : ThresholdProfile) (f : Obs → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ o, f o ∂obsLaw sigma (lowerWitnessLaw E kappa mu)) =
      ∫⁻ x, ∫⁻ a, ∫⁻ z,
        ENNReal.ofReal (mu a : ℝ) * f (x, (a : ℝ)+sigma*z, 1) +
          ENNReal.ofReal (1-(mu a : ℝ)) * f (x, (a : ℝ)+sigma*z, 0)
        ∂gaussianReal 0 1
        ∂(doseVolume.withDensity (fun a : Dose =>
          ENNReal.ofReal (witnessDesignDensity kappa ((a : ℝ)-a0))))
        ∂((1/2 : ℝ≥0∞) • Measure.dirac false + (1/2 : ℝ≥0∞) • Measure.dirac true) := by
  letI := doseVolume_probability
  letI := witnessDose_probability kappa hkappa
  have hm : Measurable (obsMap (S := S) sigma) := by
    unfold obsMap contaminatedDose; fun_prop
  rw [obsLaw, lintegral_map hf hm, lowerWitnessLaw,
    lintegral_map (show Measurable (fun w => f (obsMap sigma w)) from hf.comp hm)
      (lowerWitness_seedMap_measurable E mu)]
  simp only [Function.comp_def, obsMap, contaminatedDose, sX, sA, sY, E.eval_embed]
  have hout : Measurable (fun p : Bool × Dose × ℝ × Dose =>
      if (p.2.2.2 : ℝ) ≤ (mu p.2.1 : ℝ) then (1 : ℝ) else 0) := by
    exact Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop))
      measurable_const measurable_const
  have hfull : Measurable (fun p : Bool × Dose × ℝ × Dose =>
      f (p.1, (p.2.1 : ℝ)+sigma*p.2.2.1,
        if (p.2.2.2 : ℝ) ≤ (mu p.2.1 : ℝ) then (1 : ℝ) else 0)) := by
    fun_prop
  unfold lowerSeedLaw
  rw [lintegral_prod _ hfull.aemeasurable]
  congr 1; funext x
  have hxa := hfull.comp (show Measurable (fun p : Dose × ℝ × Dose => (x, p)) by fun_prop)
  dsimp only [Function.comp_def] at hxa ⊢
  rw [lintegral_prod _ hxa.aemeasurable]
  congr 1; funext a
  have hxaz := hxa.comp (show Measurable (fun p : ℝ × Dose => (a, p)) by fun_prop)
  dsimp only [Function.comp_def] at hxaz ⊢
  rw [lintegral_prod _ hxaz.aemeasurable]
  congr 1; funext z
  have hmark : Measurable (fun y : ℝ => f (x, (a : ℝ)+sigma*z, y)) := by fun_prop
  have hthresh : Measurable (fun u : Dose => if (u : ℝ) ≤ (mu a : ℝ) then (1 : ℝ) else 0) := by
    exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
      measurable_const measurable_const
  rw [← lintegral_map hmark hthresh, doseVolume_threshold_map,
    lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  simp [lintegral_dirac, hmark, smul_eq_mul]

/-- Scaling and translating the standard normal gives the Gaussian kernel used in the observed density. [Under the stated conditions](hyp:hsigma). [This is the stated conclusion](goal). -/
-- @node: gaussian_affine_map_density
lemma gaussian_affine_map_density (sigma a : ℝ) (hsigma : 0 < sigma) :
    (gaussianReal 0 1).map (fun z => a+sigma*z) =
      volume.withDensity (fun w => ENNReal.ofReal (phiDensity sigma (w-a))) := by
  have hvar : (NNReal.mk (sigma^2) (sq_nonneg sigma)) ≠ 0 := by
    intro h
    have hz := congrArg (fun r : ℝ≥0 => (r : ℝ)) h
    exact (ne_of_gt (sq_pos_of_pos hsigma)) hz
  rw [show (fun z => a+sigma*z) = (fun z => a+z) ∘ (fun z => sigma*z) by rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_const_add]
  simp only [mul_zero, mul_one, add_zero]
  rw [gaussianReal_of_var_ne_zero _ hvar]
  congr 1
  funext w
  rw [phiDensity_eq_gaussianPDFReal sigma (w-a) hsigma]
  simp [gaussianPDF, gaussianPDFReal]
  rfl

/-- The Gaussian channel integrates any measurable nonnegative test against its translated density. [Under the stated conditions](hyp:hsigma,f,hf). [This is the stated conclusion](goal). -/
-- @node: gaussian_affine_lintegral
lemma gaussian_affine_lintegral (sigma a : ℝ) (hsigma : 0 < sigma)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f (a+sigma*z) ∂gaussianReal 0 1) =
      ∫⁻ w, ENNReal.ofReal (phiDensity sigma (w-a))*f w := by
  rw [← lintegral_map hf (by fun_prop), gaussian_affine_map_density sigma a hsigma]
  apply lintegral_withDensity_eq_lintegral_mul
  · unfold phiDensity; fun_prop
  · exact hf

/-- Conditioning on dose and integrating out Gaussian noise gives the two nonnegative mark kernels. [Under the stated conditions](hyp:hkappa,hsigma,f,hf). [This is the stated conclusion](goal). -/
-- @node: obsLaw_witness_kernel_lintegral
lemma obsLaw_witness_kernel_lintegral (E : PathSpace S) (kappa sigma : ℝ)
    (hkappa : 0 ≤ kappa) (hsigma : 0 < sigma) (mu : ThresholdProfile)
    (f : Obs → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ o, f o ∂obsLaw sigma (lowerWitnessLaw E kappa mu)) =
      ∫⁻ x, ∫⁻ a, ∫⁻ w,
        ENNReal.ofReal (phiDensity sigma (w-(a : ℝ))) *
          (ENNReal.ofReal (mu a : ℝ)*f (x,w,1) +
            ENNReal.ofReal (1-(mu a : ℝ))*f (x,w,0)) ∂volume
        ∂(doseVolume.withDensity (fun a : Dose =>
          ENNReal.ofReal (witnessDesignDensity kappa ((a : ℝ)-a0))))
        ∂((1/2 : ℝ≥0∞) • Measure.dirac false + (1/2 : ℝ≥0∞) • Measure.dirac true) := by
  rw [obsLaw_witness_lintegral E kappa sigma hkappa mu f hf]
  congr 1; funext x
  congr 1; funext a
  exact gaussian_affine_lintegral sigma (a : ℝ) hsigma
    (fun w => ENNReal.ofReal (mu a : ℝ)*f (x,w,1) +
      ENNReal.ofReal (1-(mu a : ℝ))*f (x,w,0)) (by fun_prop)

/-- Centering the latent dose replaces the compact subtype measure by its power density on the real line. [Under the stated conditions](hyp:hkappa,f,hf). [This is the stated conclusion](goal). -/
-- @node: witnessDose_centered_lintegral
lemma witnessDose_centered_lintegral (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ a : Dose, f ((a : ℝ)-a0) ∂doseVolume.withDensity
      (fun a : Dose => ENNReal.ofReal (witnessDesignDensity kappa ((a : ℝ)-a0)))) =
      ∫⁻ t, ENNReal.ofReal (witnessDesignDensity kappa t)*f t := by
  rw [← lintegral_map hf (by fun_prop), witnessDose_map_centered kappa hkappa,
    lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (fun t => ENNReal.ofReal (witnessDesignDensity kappa t)) by fun_prop) hf,
    ← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro t
  by_cases ht : t ∈ Icc (-1/2 : ℝ) (1/2)
  · rw [indicator_of_mem ht]; rfl
  · rw [indicator_of_notMem ht]
    simp only [witnessDesignDensity, if_neg ht, ENNReal.ofReal_zero, zero_mul]

/-- Each marked convolution integrand is integrable, so its real and nonnegative integrals agree. [Under the stated conditions](hyp:hkappa,hsigma). [This is the stated conclusion](goal). -/
-- @node: marked_kernel_integrable
@[fun_prop] lemma marked_kernel_integrable (kappa sigma w : ℝ) (hkappa : 0 ≤ kappa)
    (hsigma : 0 < sigma) (mu : ThresholdProfile) :
    Integrable (fun t => witnessDesignDensity kappa t *
      (mu (Set.projIcc 0 1 zero_le_one (t+a0)) : ℝ) * phiDensity sigma (w-t)) := by
  have hc : Continuous (fun t : ℝ => (kappa+1)*2^kappa*|t|^kappa *
      (mu (Set.projIcc 0 1 zero_le_one (t+a0)) : ℝ) * phiDensity sigma (w-t)) := by
    unfold phiDensity
    fun_prop
  have he : (fun t => witnessDesignDensity kappa t *
      (mu (Set.projIcc 0 1 zero_le_one (t+a0)) : ℝ) * phiDensity sigma (w-t)) =
      (Icc (-1/2 : ℝ) (1/2)).indicator (fun t : ℝ => (kappa+1)*2^kappa*|t|^kappa *
        (mu (Set.projIcc 0 1 zero_le_one (t+a0)) : ℝ) * phiDensity sigma (w-t)) := by
    funext t
    simp only [witnessDesignDensity, indicator_apply]
    split_ifs <;> simp
  rw [he]
  exact hc.integrableOn_Icc.integrable_indicator measurableSet_Icc

/-- The success-mark density is the half-reference density plus the smoothed centered profile. [Under the stated conditions](hyp:hkappa,hsigma). [This is the stated conclusion](goal). -/
-- @node: marked_success_density_eq
lemma marked_success_density_eq (kappa sigma w : ℝ) (hkappa : 0 ≤ kappa)
    (hsigma : 0 < sigma) (mu : ThresholdProfile) :
    smoothSigned sigma (fun t => witnessDesignDensity kappa t *
      (mu (Set.projIcc 0 1 zero_le_one (t+a0)) : ℝ)) w =
      smoothSigned sigma (witnessDesignDensity kappa) w / 2 +
        smoothSigned sigma (fun t => witnessDesignDensity kappa t *
          ((mu (Set.projIcc 0 1 zero_le_one (t+a0)) : ℝ)-1/2)) w := by
  have hbase := gaussian_design_integrable kappa sigma w hkappa hsigma
  have hsuccess := marked_kernel_integrable kappa sigma w hkappa hsigma mu
  have hsplit : (fun t => witnessDesignDensity kappa t *
      ((mu (Set.projIcc 0 1 zero_le_one (t+a0)) : ℝ)-1/2) * phiDensity sigma (w-t)) =
      (fun t => witnessDesignDensity kappa t *
        (mu (Set.projIcc 0 1 zero_le_one (t+a0)) : ℝ) * phiDensity sigma (w-t) -
        (witnessDesignDensity kappa t * phiDensity sigma (w-t))/2) := by
    funext t; ring
  unfold smoothSigned
  rw [hsplit]
  rw [integral_sub hsuccess (hbase.div_const 2), integral_div]
  ring

/-- The failure-mark density is the half-reference density minus the same smoothed centered profile. [Under the stated conditions](hyp:hkappa,hsigma). [This is the stated conclusion](goal). -/
-- @node: marked_failure_density_eq
lemma marked_failure_density_eq (kappa sigma w : ℝ) (hkappa : 0 ≤ kappa)
    (hsigma : 0 < sigma) (mu : ThresholdProfile) :
    smoothSigned sigma (fun t => witnessDesignDensity kappa t *
      (1-(mu (Set.projIcc 0 1 zero_le_one (t+a0)) : ℝ))) w =
      smoothSigned sigma (witnessDesignDensity kappa) w / 2 -
        smoothSigned sigma (fun t => witnessDesignDensity kappa t *
          ((mu (Set.projIcc 0 1 zero_le_one (t+a0)) : ℝ)-1/2)) w := by
  have hbase := gaussian_design_integrable kappa sigma w hkappa hsigma
  have hsuccess := marked_kernel_integrable kappa sigma w hkappa hsigma mu
  have hsplit : (fun t => witnessDesignDensity kappa t *
      (1-(mu (Set.projIcc 0 1 zero_le_one (t+a0)) : ℝ)) * phiDensity sigma (w-t)) =
      (fun t => witnessDesignDensity kappa t * phiDensity sigma (w-t) -
        witnessDesignDensity kappa t *
        (mu (Set.projIcc 0 1 zero_le_one (t+a0)) : ℝ) * phiDensity sigma (w-t)) := by
    funext t; ring
  change (∫ t, witnessDesignDensity kappa t *
    (1-(mu (Set.projIcc 0 1 zero_le_one (t+a0)) : ℝ)) * phiDensity sigma (w-t)) = _
  rw [hsplit]
  rw [integral_sub hbase hsuccess]
  change smoothSigned sigma (witnessDesignDensity kappa) w -
    smoothSigned sigma (fun t => witnessDesignDensity kappa t *
      (mu (Set.projIcc 0 1 zero_le_one (t+a0)) : ℝ)) w = _
  rw [marked_success_density_eq kappa sigma w hkappa hsigma mu]
  ring

/-- A nonnegative dose mark integrates to its centered Gaussian convolution density. [Under the stated conditions](hyp:hkappa,hsigma,hq,hnonneg,hint). [This is the stated conclusion](goal). -/
-- @node: witness_mark_kernel_lintegral
lemma witness_mark_kernel_lintegral (kappa sigma w : ℝ) (hkappa : 0 ≤ kappa)
    (hsigma : 0 < sigma) (q : Dose → ℝ) (hq : Measurable q)
    (hnonneg : ∀ a, 0 ≤ q a)
    (hint : Integrable (fun t => witnessDesignDensity kappa t *
      q (Set.projIcc 0 1 zero_le_one (t+a0)) * phiDensity sigma ((w-a0)-t))) :
    (∫⁻ a : Dose, ENNReal.ofReal (q a)*ENNReal.ofReal (phiDensity sigma (w-(a : ℝ)))
      ∂doseVolume.withDensity (fun a : Dose =>
        ENNReal.ofReal (witnessDesignDensity kappa ((a : ℝ)-a0)))) =
      ENNReal.ofReal (smoothSigned sigma (fun t => witnessDesignDensity kappa t *
        q (Set.projIcc 0 1 zero_le_one (t+a0))) (w-a0)) := by
  have he : (fun a : Dose => ENNReal.ofReal (q a)*
      ENNReal.ofReal (phiDensity sigma (w-(a : ℝ)))) =
      (fun a : Dose => ENNReal.ofReal (q (Set.projIcc 0 1 zero_le_one ((a : ℝ)-a0+a0)))*
        ENNReal.ofReal (phiDensity sigma ((w-a0)-((a : ℝ)-a0)))) := by
    funext a
    rw [sub_add_cancel, Set.projIcc_of_mem zero_le_one a.property]
    congr 2
    ring
  rw [he, witnessDose_centered_lintegral kappa hkappa
    (fun t => ENNReal.ofReal (q (Set.projIcc 0 1 zero_le_one (t+a0)))*
      ENNReal.ofReal (phiDensity sigma ((w-a0)-t))) (by unfold phiDensity; fun_prop)]
  change _ = ENNReal.ofReal (∫ t, witnessDesignDensity kappa t *
    q (Set.projIcc 0 1 zero_le_one (t+a0)) * phiDensity sigma ((w-a0)-t))
  rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun t =>
    mul_nonneg (mul_nonneg (witnessDesignDensity_nonneg kappa t hkappa) (hnonneg _))
      (phiDensity_pos sigma _ hsigma).le))]
  apply lintegral_congr
  intro t
  rw [ENNReal.ofReal_mul (mul_nonneg (witnessDesignDensity_nonneg kappa t hkappa) (hnonneg _)),
    ENNReal.ofReal_mul (witnessDesignDensity_nonneg kappa t hkappa), mul_assoc]

/-- The two observed marks have exactly the Gaussian convolutions of their latent success and failure densities. [Under the stated conditions](hyp:hkappa,hsigma,f,hf). [This is the stated conclusion](goal). -/
-- @node: obsLaw_witness_density_lintegral
lemma obsLaw_witness_density_lintegral (E : PathSpace S) (kappa sigma : ℝ)
    (hkappa : 0 ≤ kappa) (hsigma : 0 < sigma) (mu : ThresholdProfile)
    (f : Obs → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ o, f o ∂obsLaw sigma (lowerWitnessLaw E kappa mu)) =
      ∫⁻ x, ∫⁻ w,
        ENNReal.ofReal (smoothSigned sigma (fun t => witnessDesignDensity kappa t *
          (mu (Set.projIcc 0 1 zero_le_one (t+a0)) : ℝ)) (w-a0)) * f (x,w,1) +
        ENNReal.ofReal (smoothSigned sigma (fun t => witnessDesignDensity kappa t *
          (1-(mu (Set.projIcc 0 1 zero_le_one (t+a0)) : ℝ))) (w-a0)) * f (x,w,0)
        ∂volume
        ∂((1/2 : ℝ≥0∞) • Measure.dirac false + (1/2 : ℝ≥0∞) • Measure.dirac true) := by
  letI := witnessDose_probability kappa hkappa
  rw [obsLaw_witness_kernel_lintegral E kappa sigma hkappa hsigma mu f hf]
  congr 1; funext x
  rw [lintegral_lintegral_swap (by unfold phiDensity; fun_prop)]
  apply lintegral_congr
  intro w
  have hp := marked_kernel_integrable kappa sigma (w-a0) hkappa hsigma mu
  have hn : Integrable (fun t => witnessDesignDensity kappa t *
      (1-(mu (Set.projIcc 0 1 zero_le_one (t+a0)) : ℝ)) * phiDensity sigma ((w-a0)-t)) := by
    convert (gaussian_design_integrable kappa sigma (w-a0) hkappa hsigma).sub hp using 1
    funext t; dsimp only [Pi.sub_apply]; ring
  simp_rw [mul_add, ← mul_assoc, mul_comm (ENNReal.ofReal (phiDensity sigma (w-_)))]
  rw [lintegral_add_left (by unfold phiDensity; fun_prop),
    lintegral_mul_const _ (by unfold phiDensity; fun_prop),
    lintegral_mul_const _ (by unfold phiDensity; fun_prop),
    witness_mark_kernel_lintegral kappa sigma w hkappa hsigma
      (fun a => (mu a : ℝ)) (by fun_prop) (fun a => (mu a).property.1) hp,
    witness_mark_kernel_lintegral kappa sigma w hkappa hsigma
      (fun a => 1-(mu a : ℝ)) (by fun_prop)
      (fun a => sub_nonneg.mpr (mu a).property.2) hn]

/-- Equation (11): the observed law has the half-reference density plus or minus the centered signed convolution. [Under the stated conditions](hyp:hkappa,hsigma,f,hf). [This is the stated conclusion](goal). -/
-- @node: obsLaw_witness_signed_density_lintegral
lemma obsLaw_witness_signed_density_lintegral (E : PathSpace S) (kappa sigma : ℝ)
    (hkappa : 0 ≤ kappa) (hsigma : 0 < sigma) (mu : ThresholdProfile)
    (f : Obs → ℝ≥0∞) (hf : Measurable f) :
    let pV := smoothSigned sigma (witnessDesignDensity kappa)
    let v := fun t => witnessDesignDensity kappa t *
      ((mu (Set.projIcc 0 1 zero_le_one (t+a0)) : ℝ)-1/2)
    (∫⁻ o, f o ∂obsLaw sigma (lowerWitnessLaw E kappa mu)) =
      ∫⁻ x, ∫⁻ w,
        ENNReal.ofReal (pV (w-a0)/2 + smoothSigned sigma v (w-a0)) * f (x,w,1) +
        ENNReal.ofReal (pV (w-a0)/2 - smoothSigned sigma v (w-a0)) * f (x,w,0)
        ∂volume
        ∂((1/2 : ℝ≥0∞) • Measure.dirac false + (1/2 : ℝ≥0∞) • Measure.dirac true) := by
  dsimp only
  rw [obsLaw_witness_density_lintegral E kappa sigma hkappa hsigma mu f hf]
  simp_rw [marked_success_density_eq kappa sigma _ hkappa hsigma mu,
    marked_failure_density_eq kappa sigma _ hkappa hsigma mu]

/-- Each observed alternative is dominated by twice the half-success reference law. [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: obsLaw_witness_le_two
lemma obsLaw_witness_le_two (E : PathSpace S) (kappa sigma : ℝ)
    (hkappa : 0 ≤ kappa) (mu : ThresholdProfile) :
    obsLaw sigma (lowerWitnessLaw E kappa mu) ≤
      (2 : ℝ≥0∞) • obsLaw sigma (lowerWitnessLaw E kappa referenceProfile) := by
  apply Measure.le_iff.mpr
  intro B hB
  let f : Obs → ℝ≥0∞ := B.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hB
  have hlin : (∫⁻ o, f o ∂obsLaw sigma (lowerWitnessLaw E kappa mu)) ≤
      2 * (∫⁻ o, f o ∂obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) := by
    rw [obsLaw_witness_lintegral E kappa sigma hkappa mu f hf,
      obsLaw_witness_lintegral E kappa sigma hkappa referenceProfile f hf]
    simp only [referenceProfile, ContinuousMap.const_apply,
      show ((Set.projIcc 0 1 zero_le_one (1/2) : Dose) : ℝ) = 1/2 by norm_num [Set.projIcc],
      show (1 : ℝ)-1/2 = 1/2 by norm_num]
    rw [← lintegral_const_mul' _ _ (by norm_num)]
    apply lintegral_mono; intro x
    dsimp only
    rw [← lintegral_const_mul' _ _ (by norm_num)]
    apply lintegral_mono; intro a
    dsimp only
    rw [← lintegral_const_mul' _ _ (by norm_num)]
    apply lintegral_mono; intro z
    dsimp only
    have hp : ENNReal.ofReal (mu a : ℝ) ≤ 1 := by
      exact (ENNReal.ofReal_le_ofReal (mu a).property.2).trans_eq ENNReal.ofReal_one
    have hn : ENNReal.ofReal (1-(mu a : ℝ)) ≤ 1 := by
      apply (ENNReal.ofReal_le_ofReal (show 1-(mu a : ℝ) ≤ 1 by linarith [(mu a).property.1])).trans_eq
      exact ENNReal.ofReal_one
    calc
      _ ≤ 1 * f (x, (a : ℝ)+sigma*z, 1) + 1 * f (x, (a : ℝ)+sigma*z, 0) :=
        by gcongr
      _ = _ := by
        rw [mul_add, ← mul_assoc, ← mul_assoc]
        simp [ENNReal.ofReal_div_of_pos, ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  simpa [f, Measure.smul_apply, smul_eq_mul, lintegral_indicator hB] using hlin

/-- The observed threshold alternative is absolutely continuous with respect to the half-success reference. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hkappa,hsigma,hrange). -/
-- @node: obsLaw_witness_ac
lemma obsLaw_witness_ac (E : PathSpace S) (kappa sigma : ℝ)
    (hkappa : kappa ∈ Icc (0 : ℝ) 2) (hsigma : sigma ∈ Icc (0 : ℝ) (1/4))
    (mu : ThresholdProfile) (hrange : ∀ a, (mu a : ℝ) ∈ Icc (1/8) (7/8)) :
    obsLaw sigma (lowerWitnessLaw E kappa mu) ≪ obsLaw sigma (lowerWitnessLaw E kappa referenceProfile) := by
  exact (Measure.absolutelyContinuous_of_le (obsLaw_witness_le_two E kappa sigma hkappa.1 mu)).trans
    Measure.smul_absolutelyContinuous
/-- The observed likelihood ratio has a finite squared deviation, including at zero noise. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hkappa,hsigma,hrange). -/
-- @node: obsLaw_witness_sqdev_integrable
lemma obsLaw_witness_sqdev_integrable (E : PathSpace S) (kappa sigma : ℝ)
    (hkappa : kappa ∈ Icc (0 : ℝ) 2) (hsigma : sigma ∈ Icc (0 : ℝ) (1/4))
    (mu : ThresholdProfile) (hrange : ∀ a, (mu a : ℝ) ∈ Icc (1/8) (7/8)) :
    Integrable (fun o =>
      (((obsLaw sigma (lowerWitnessLaw E kappa mu)).rnDeriv
        (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) o).toReal - 1)^2)
      (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) := by
  let Q := obsLaw sigma (lowerWitnessLaw E kappa mu)
  let R := obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)
  letI := lowerWitnessLaw_probability E kappa hkappa referenceProfile
  have hobs : Measurable (obsMap (S := S) sigma) := by
    unfold obsMap contaminatedDose; fun_prop
  letI : IsProbabilityMeasure R := Measure.isProbabilityMeasure_map hobs.aemeasurable
  have hdom : Q ≤ (2 : ℝ≥0∞) • R := obsLaw_witness_le_two E kappa sigma hkappa.1 mu
  have hb : ∀ᵐ o ∂ R, Q.rnDeriv R o ≤ 2 := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv Q R)
    intro B hB hfinite
    rw [← withDensity_apply _ hB]
    calc
      _ ≤ Q B := Measure.le_iff'.mp (Measure.withDensity_rnDeriv_le Q R) B
      _ ≤ ((2 : ℝ≥0∞) • R) B := Measure.le_iff'.mp hdom B
      _ = ∫⁻ o in B, (2 : ℝ≥0∞) ∂ R := by simp [Measure.smul_apply, smul_eq_mul]
  have hreal : Measurable (fun o => (Q.rnDeriv R o).toReal) :=
    (Measure.measurable_rnDeriv Q R).ennreal_toReal
  have hm : AEStronglyMeasurable (fun o => ((Q.rnDeriv R o).toReal - 1)^2) R :=
    ((hreal.sub measurable_const).pow_const 2).aestronglyMeasurable
  apply (integrable_const (1 : ℝ)).mono' hm
  filter_upwards [hb] with o ho
  have hlo : 0 ≤ (Q.rnDeriv R o).toReal := ENNReal.toReal_nonneg
  have hhi : (Q.rnDeriv R o).toReal ≤ 2 := by
    have h := ENNReal.toReal_mono (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) ho
    norm_num at h ⊢
    exact h
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith

/-- Compact support and integrability justify the exact Gaussian moment identity and its convergent tail. [Under the stated conditions](hyp:hsigma,hell,hv,hmom,hsupp). [This is the stated conclusion](goal). -/
-- @node: gaussian_moment_series
lemma gaussian_moment_series (sigma ell : ℝ) (hsigma : 0 < sigma) (hell : 0 < ell)
    (J : ℕ) (v : ℝ → ℝ) (hv : Integrable v)
    (hsupp : ∀ t, t ∉ Icc (-ell) ell → v t = 0)
    (hmom : ∀ j < J, ∫ t, t^j*v t = 0) :
    Summable (fun j : ℕ => (∫ t, t^j*v t)^2 / (sigma^(2*j)*(j.factorial : ℝ))) ∧
    (∫ w, (smoothSigned sigma v w)^2 / phiDensity sigma w) =
      (∑' j : ℕ, if J ≤ j then (∫ t, t^j*v t)^2 / (sigma^(2*j)*(j.factorial : ℝ)) else 0) ∧
    (∫ w, (smoothSigned sigma v w)^2 / phiDensity sigma w) ≤
      (∫ t, |v t|)^2 * momentTail sigma ell J := by
  refine ⟨compact_signed_moment_summable sigma ell hsigma hell.le v hv hsupp, ?_⟩
  have hid : (∫ w, (smoothSigned sigma v w)^2 / phiDensity sigma w) =
      (∑' j : ℕ, if J ≤ j then
        (∫ t, t^j*v t)^2 / (sigma^(2*j)*(j.factorial : ℝ)) else 0) := by
    exact gaussian_compact_energy_tail_identity sigma ell hsigma hell.le J v hv hsupp hmom
  exact ⟨hid, hid.le.trans
    (compact_signed_moment_tail_bound sigma ell hsigma hell.le J v hv hsupp)⟩
/-- Explicit AC and square-integrability obligations discharge the general-space iid tensorization API. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hkappa,hsigma,hrange). -/
-- @node: witness_tensorization
lemma witness_tensorization (E : PathSpace S) (kappa sigma : ℝ)
    (hkappa : kappa ∈ Icc (0 : ℝ) 2) (hsigma : sigma ∈ Icc (0 : ℝ) (1/4))
    (mu : ThresholdProfile) (hrange : ∀ a, (mu a : ℝ) ∈ Icc (1/8) (7/8)) (n : ℕ) :
    1 + Causalean.Stat.chiSqDiv (experiment n sigma (lowerWitnessLaw E kappa mu))
      (experiment n sigma (lowerWitnessLaw E kappa referenceProfile)) =
      (1 + Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa mu))
        (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)))^n := by
  letI := lowerWitnessLaw_probability E kappa hkappa mu
  letI := lowerWitnessLaw_probability E kappa hkappa referenceProfile
  have hobs : Measurable (obsMap (S := S) sigma) := by
    unfold obsMap contaminatedDose
    fun_prop
  letI : IsProbabilityMeasure (obsLaw sigma (lowerWitnessLaw E kappa mu)) :=
    Measure.isProbabilityMeasure_map hobs.aemeasurable
  letI : IsProbabilityMeasure (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) :=
    Measure.isProbabilityMeasure_map hobs.aemeasurable
  exact Causalean.Stat.one_add_chiSqDiv_pi_iid_general
    (obsLaw sigma (lowerWitnessLaw E kappa mu))
    (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile))
    (obsLaw_witness_ac E kappa sigma hkappa hsigma mu hrange)
    (obsLaw_witness_sqdev_integrable E kappa sigma hkappa hsigma mu hrange) n

end CausalSmith.Stat.NoisydoseWeakdesignTransition

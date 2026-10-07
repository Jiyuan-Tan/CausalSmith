module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.DictionaryScore.FourierInverse
public import Causalean.Mathlib.Analysis.Fourier.WeightedSpecialization
public import Causalean.Stat.Nonparametric.Specialization

/-! Sinc-six profile prerequisites for the promoted weighted inverse-Gaussian bounds. -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology FourierTransform
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- Whole-line localization moments give three continuous spectral derivatives. [Under the stated conditions](hyp:h,hh). [This is the stated conclusion](goal). -/
-- @node: qF_fourier_contDiff
lemma qF_fourier_contDiff (h : ℝ) (hh : 0 < h) :
    ContDiff ℝ 3 (𝓕 (fun t => (qF h t : ℂ))) := by
  apply Real.contDiff_fourier
  intro j hj
  have hj3 : j ≤ 3 := by exact_mod_cast hj
  have hs : (j : ℝ) ∈ Icc (0 : ℝ) 3 := ⟨by positivity, by exact_mod_cast hj3⟩
  simpa only [Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (qF_nonneg h _), Real.rpow_natCast] using
    qF_whole_weighted_integrable (j : ℝ) h hs hh

/-- The spectral support radius agrees with the promoted theorem's convention. [Under the stated conditions](hyp:h,hh). [This is the stated conclusion](goal). -/
-- @node: qF_fourier_support_radius
lemma qF_fourier_support_radius (h : ℝ) (hh : 0 < h) :
    Function.support (𝓕 (fun t => (qF h t : ℂ))) ⊆
      Icc (-(3 / (Real.pi * h))) (3 / (Real.pi * h)) := by
  convert qF_fourier_support h hh using 1 <;> congr 1 <;> ring

/-- Compact spectral support is independent of the noise scale. [Under the stated conditions](hyp:h,hh). [This is the stated conclusion](goal). -/
-- @node: qF_fourier_hasCompactSupport
lemma qF_fourier_hasCompactSupport (h : ℝ) (hh : 0 < h) :
    HasCompactSupport (𝓕 (fun t => (qF h t : ℂ))) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (qF_fourier_support h hh)

/-- The spectral height is controlled by the unscaled sinc-six mass. [Under the stated conditions](hyp:h,hh). [This is the stated conclusion](goal). -/
-- @node: qF_fourier_height
lemma qF_fourier_height (h : ℝ) (hh : 0 < h) (xi : ℝ) :
    ‖𝓕 (fun t => (qF h t : ℂ)) xi‖ ≤ (∫ u : ℝ, qF 1 u) * h := by
  have hn : (fun t => ‖(qF h t : ℂ)‖) = qF h := by
    funext t
    simp [Complex.norm_real, abs_of_nonneg (qF_nonneg h t)]
  have hb := VectorFourier.norm_fourierIntegral_le_integral_norm
    Real.fourierChar volume (innerₗ ℝ) (fun t => (qF h t : ℂ)) xi
  change ‖𝓕 (fun t => (qF h t : ℂ)) xi‖ ≤ _ at hb
  rw [hn] at hb
  have hs := qF_whole_moment_scaling 0 h hh
  simp only [Real.rpow_zero, one_mul, zero_add, Real.rpow_one] at hs
  rw [hs, mul_comm] at hb
  exact hb

/-- The first absolute localization moment justifies differentiation under the Fourier integral. [Under the stated conditions](hyp:h,hh). [This is the stated conclusion](goal). -/
-- @node: qF_mul_integrable_complex
lemma qF_mul_integrable_complex (h : ℝ) (hh : 0 < h) :
    Integrable (fun t : ℝ => t • (qF h t : ℂ)) := by
  apply (qF_whole_weighted_integrable 1 h (by norm_num) hh).mono'
    (by fun_prop)
  filter_upwards with t
  simp [norm_smul, Complex.norm_real, abs_of_nonneg (qF_nonneg h t)]

/-- The derivative height has order h squared with a fixed unscaled moment constant. [Under the stated conditions](hyp:h,hh). [This is the stated conclusion](goal). -/
-- @node: qF_fourier_deriv_height
lemma qF_fourier_deriv_height (h : ℝ) (hh : 0 < h) (xi : ℝ) :
    ‖deriv (𝓕 (fun t => (qF h t : ℂ))) xi‖ ≤
      (2 * Real.pi * (∫ u : ℝ, |u| * qF 1 u)) * h^2 := by
  rw [Real.deriv_fourier (qF_integrable_complex h hh) (qF_mul_integrable_complex h hh)]
  have hb := VectorFourier.norm_fourierIntegral_le_integral_norm
    Real.fourierChar volume (innerₗ ℝ)
      (fun t : ℝ => (-2 * Real.pi * Complex.I * t) • (qF h t : ℂ)) xi
  change ‖𝓕 (fun t : ℝ => (-2 * Real.pi * Complex.I * t) • (qF h t : ℂ)) xi‖ ≤ _ at hb
  have hn : (fun t : ℝ => ‖(-2 * Real.pi * Complex.I * t) • (qF h t : ℂ)‖) =
      fun t : ℝ => (2 * Real.pi) * (|t| * qF h t) := by
    funext t
    simp [norm_smul, norm_mul, Complex.norm_real, abs_of_nonneg Real.pi_pos.le,
      abs_of_nonneg (qF_nonneg h t)]
    ring
  rw [hn, integral_const_mul] at hb
  have hs := qF_whole_moment_scaling 1 h hh
  norm_num only [Real.rpow_one, show (1 : ℝ)+1 = 2 by norm_num,
    Real.rpow_two] at hs
  rw [hs] at hb
  convert hb using 1 <;> ring

/-- Fixed nonnegative constants supply precisely the profile hypotheses of the promoted bound. [This is the stated conclusion](goal). -/
-- @node: qF_fourier_profile_bounds
lemma qF_fourier_profile_bounds :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ ∀ h : ℝ, 0 < h →
      (∀ xi, ‖𝓕 (fun t => (qF h t : ℂ)) xi‖ ≤ a*h) ∧
      (∀ xi, ‖deriv (𝓕 (fun t => (qF h t : ℂ))) xi‖ ≤ b*h^2) := by
  refine ⟨∫ u : ℝ, qF 1 u, 2*Real.pi*(∫ u : ℝ, |u| * qF 1 u),
    integral_nonneg (qF_nonneg 1), ?_, ?_⟩
  · exact mul_nonneg (by positivity) (integral_nonneg (fun u =>
      mul_nonneg (abs_nonneg u) (qF_nonneg 1 u)))
  · intro h hh
    exact ⟨qF_fourier_height h hh, qF_fourier_deriv_height h hh⟩

/-- Two continuous compactly supported frequency derivatives make the inverse absolutely integrable.
This is the integrability part of S6, obtained from Mathlib's derivative identities. [Under the stated conditions](hyp:hG,hc). [This is the stated conclusion](goal). -/
-- @node: compactC2_fourier_integrable
lemma compactC2_fourier_integrable (G : ℝ → ℂ) (hG : ContDiff ℝ 2 G)
    (hc : HasCompactSupport G) : Integrable (𝓕 G) := by
  have hD : ContDiff ℝ 1 (deriv G) := by
    exact (contDiff_succ_iff_deriv (n := 1)).mp hG |>.2.2
  have hi : Integrable G := hG.continuous.integrable_of_hasCompactSupport hc
  have hiD : Integrable (deriv G) := hD.continuous.integrable_of_hasCompactSupport hc.deriv
  have hiDD : Integrable (deriv (deriv G)) := (hD.continuous_deriv (by norm_num)).integrable_of_hasCompactSupport hc.deriv.deriv
  let A : ℝ := ∫ xi, ‖G xi‖
  let B : ℝ := (∫ xi, ‖deriv (deriv G) xi‖) / (2*Real.pi)^2
  have hA : 0 ≤ A := integral_nonneg (fun _ => norm_nonneg _)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbound (v : ℝ) : ‖𝓕 G v‖ ≤ A :=
    VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) G v
  have hbound2 (v : ℝ) : |v|^2 * ‖𝓕 G v‖ ≤ B := by
    have ht := VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) (deriv (deriv G)) v
    change ‖𝓕 (deriv (deriv G)) v‖ ≤ _ at ht
    rw [Real.fourier_deriv hiD (hD.differentiable (by norm_num)) hiDD,
      Real.fourier_deriv hi (hG.differentiable (by norm_num)) hiD] at ht
    simp only [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one, abs_mul, abs_neg, abs_of_pos Real.pi_pos,
      norm_neg] at ht
    norm_num at ht
    apply (le_div_iff₀ (by positivity : 0 < (2*Real.pi)^2)).mpr
    nlinarith [ht]
  have hdecay (v : ℝ) : ‖𝓕 G v‖ ≤ 4*(A+B)/(1+|v|)^2 := by
    apply (le_div_iff₀ (by positivity : 0 < (1+|v|)^2)).mpr
    by_cases hv : |v| ≤ 1
    · have hp : (1+|v|)^2 ≤ 4 := by nlinarith [abs_nonneg v]
      nlinarith [mul_le_mul (hbound v) hp (sq_nonneg (1+|v|)) hA]
    · have hp : (1+|v|)^2 ≤ 4*|v|^2 := by nlinarith [abs_nonneg v, lt_of_not_ge hv]
      have hm := mul_le_mul_of_nonneg_left hp (norm_nonneg (𝓕 G v))
      nlinarith [hbound2 v]
  have hd : Integrable (fun v : ℝ => 4*(A+B)/(1+|v|)^2) := by
    simpa [Real.norm_eq_abs, Real.rpow_neg, div_eq_mul_inv] using
      (integrable_one_add_norm (by norm_num : (Module.finrank ℝ ℝ : ℝ) < 2)).const_mul (4*(A+B))
  apply hd.mono'
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by fun_prop) hi).aestronglyMeasurable
  exact Eventually.of_forall hdecay

/-- The inverse and derivative inverse satisfy the promoted theorem's absolute inversion hypotheses. [Under the stated conditions](hyp:h,hh). [This is the stated conclusion](goal). -/
-- @node: qF_inverseGaussian_integrable
lemma qF_inverseGaussian_integrable (sigma h : ℝ) (hh : 0 < h) :
    Integrable (𝓕⁻ (Causalean.Mathlib.Analysis.Fourier.inverseGaussian sigma
      (𝓕 (fun t => (qF h t : ℂ))))) ∧
    Integrable (𝓕⁻ (deriv (Causalean.Mathlib.Analysis.Fourier.inverseGaussian sigma
      (𝓕 (fun t => (qF h t : ℂ)))))) := by
  let G := Causalean.Mathlib.Analysis.Fourier.inverseGaussian sigma
    (𝓕 (fun t => (qF h t : ℂ)))
  have hG : ContDiff ℝ 3 G := by
    dsimp [G, Causalean.Mathlib.Analysis.Fourier.inverseGaussian]
    apply (qF_fourier_contDiff h hh).mul
    exact Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_exp.comp ((contDiff_const.mul
        ((contDiff_const.mul contDiff_id).pow 2)).div_const 2))
  have hc : HasCompactSupport G :=
    Causalean.Mathlib.Analysis.Fourier.inverseGaussian_hasCompactSupport _ _
      (qF_fourier_hasCompactSupport h hh)
  have hD : ContDiff ℝ 2 (deriv G) := (contDiff_succ_iff_deriv (n := 2)).mp hG |>.2.2
  have hi := compactC2_fourier_integrable G (hG.of_le (by norm_num)) hc
  have hiD := compactC2_fourier_integrable (deriv G) hD hc.deriv
  constructor
  · change Integrable (fun t => 𝓕⁻ G t)
    simp_rw [Real.fourierInv_eq_fourier_neg]
    exact hi.comp_neg
  · change Integrable (fun t => 𝓕⁻ (deriv G) t)
    simp_rw [Real.fourierInv_eq_fourier_neg]
    exact hiD.comp_neg

/-- Specializing the promoted frequency estimate proves the weighted physical-space bound in S6. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hkappa). -/
-- @node: qF_inverseGaussian_weightedEnergy_bound
lemma qF_inverseGaussian_weightedEnergy_bound (kappa : ℝ)
    (hkappa : kappa ∈ Icc (0 : ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → ∀ sigma : ℝ, 0 ≤ sigma →
      Integrable (fun v => |v| ^ kappa *
        ‖𝓕⁻ (Causalean.Mathlib.Analysis.Fourier.inverseGaussian sigma
          (𝓕 (fun t => (qF h t : ℂ)))) v‖ ^ 2) ∧
      Causalean.Mathlib.Analysis.Fourier.weightedEnergy kappa
        (𝓕⁻ (Causalean.Mathlib.Analysis.Fourier.inverseGaussian sigma
          (𝓕 (fun t => (qF h t : ℂ))))) ≤
        C * h ^ (kappa+1) * (1+sigma/h)^4 * Real.exp (36*(sigma/h)^2) := by
  obtain ⟨a, b, ha, hb, hprofile⟩ := qF_fourier_profile_bounds
  let C := (6 / Real.pi) * (a^2 + (2*Real.pi)⁻¹^2 * (b+12*Real.pi*a)^2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C+1, by positivity, ?_⟩
  intro h hh sigma hsigma
  obtain ⟨hinv, hinvD⟩ := qF_inverseGaussian_integrable sigma h hh
  obtain ⟨hi, hbound⟩ := Causalean.Mathlib.Analysis.Fourier.inverseGaussian_weightedEnergy_le
    (𝓕 (fun t => (qF h t : ℂ))) kappa sigma h a b
    ((qF_fourier_contDiff h hh).of_le (by norm_num)) (qF_fourier_hasCompactSupport h hh)
    hkappa.1 hkappa.2 hh hsigma ha hb (qF_fourier_support_radius h hh)
    (hprofile h hh).1 (hprofile h hh).2 hinv hinvD
  refine ⟨hi, hbound.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity)

/-- Finite ordinary and quadratic kernel energies imply joint design/noise integrability.
A measure-preserving dose translation reduces this bookkeeping step to product integrals. [Under the stated conditions](hyp:g,hg,hkappa,h0,h2). [This is the stated conclusion](goal). -/
-- @node: gaussian_shifted_joint_integrable
lemma gaussian_shifted_joint_integrable (g : ℝ → ℂ) (kappa sigma : ℝ)
    (hkappa : kappa ∈ Icc (0 : ℝ) 2) (hg : Measurable g)
    (h0 : Integrable (fun v => ‖g v‖^2))
    (h2 : Integrable (fun v : ℝ => v^2 * ‖g v‖^2)) :
    Integrable (fun p : ℝ × ℝ => |p.1|^kappa * ‖g (p.1+sigma*p.2)‖^2)
      (volume.prod (gaussianReal 0 1)) := by
  have hz : Integrable (fun z : ℝ => z^2) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq
  have hd : Integrable (fun p : ℝ × ℝ =>
      (1+2*p.2^2+2*sigma^2*p.1^2) * ‖g p.2‖^2)
      ((gaussianReal 0 1).prod volume) := by
    convert! ((integrable_const (1 : ℝ) (μ := gaussianReal 0 1)).mul_prod
      (h0.add (h2.const_mul 2))).add ((hz.const_mul (2*sigma^2)).mul_prod h0) using 1
    funext p
    dsimp
    ring
  have mp : MeasurePreserving (fun p : ℝ × ℝ => (p.1, p.2+sigma*p.1))
      ((gaussianReal 0 1).prod volume) ((gaussianReal 0 1).prod volume) := by
    simpa only [id_eq] using
      (MeasurePreserving.id (gaussianReal 0 1)).skew_product
        (g := fun z t : ℝ => t+sigma*z) (by fun_prop)
        (Eventually.of_forall (fun z => (measurePreserving_add_right volume (sigma*z)).map_eq))
  have hcomp := mp.integrable_comp_of_integrable hd
  have hi : Integrable (fun p : ℝ × ℝ => |p.2|^kappa * ‖g (p.2+sigma*p.1)‖^2)
      ((gaussianReal 0 1).prod volume) := by
    apply hcomp.mono' (by fun_prop)
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _))]
    have hw : |p.2|^kappa ≤ 1+p.2^2 := by
      by_cases ht : |p.2| ≤ 1
      · have := Real.rpow_le_one (abs_nonneg p.2) ht hkappa.1
        nlinarith [sq_nonneg p.2]
      · have := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge ht) hkappa.2
        simp only [Real.rpow_two, sq_abs] at this
        linarith
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    change |p.2|^kappa ≤ 1+2*(p.2+sigma*p.1)^2+2*sigma^2*p.1^2
    nlinarith [sq_nonneg (p.2+2*sigma*p.1)]
  exact (Measure.measurePreserving_swap (μ := volume) (ν := gaussianReal 0 1)).integrable_comp_of_integrable hi

/-- The complex sinc-six inverse has jointly integrable weighted second moments on the full dose line. [Under the stated conditions](hyp:h,hh,hkappa). [This is the stated conclusion](goal). -/
-- @node: qF_inverseGaussian_joint_integrable
lemma qF_inverseGaussian_joint_integrable (kappa sigma h : ℝ)
    (hkappa : kappa ∈ Icc (0 : ℝ) 2) (hh : 0 < h) :
    Integrable (fun p : ℝ × ℝ => |p.1|^kappa *
      ‖𝓕⁻ (Causalean.Mathlib.Analysis.Fourier.inverseGaussian sigma
        (𝓕 (fun t => (qF h t : ℂ)))) (p.1+sigma*p.2)‖^2)
      (volume.prod (gaussianReal 0 1)) := by
  let F := 𝓕 (fun t => (qF h t : ℂ))
  let G := Causalean.Mathlib.Analysis.Fourier.inverseGaussian sigma F
  have hF : ContDiff ℝ 1 F := (qF_fourier_contDiff h hh).of_le (by norm_num)
  obtain ⟨hi, hiD⟩ := qF_inverseGaussian_integrable sigma h hh
  have hdata := Causalean.Mathlib.Analysis.Fourier.inverseGaussian_compactInverseData
    F sigma hF (qF_fourier_hasCompactSupport h hh) hi hiD
  obtain ⟨h0, h2, _⟩ := Causalean.Mathlib.Analysis.Fourier.inverse_energy_endpoints G hdata
  apply gaussian_shifted_joint_integrable _ kappa sigma hkappa _ h0 h2
  have hc : Continuous (𝓕⁻ G) := by
    have hc' : Continuous (𝓕 G) := VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (by fun_prop)
      (hdata.regularity.continuous.integrable_of_hasCompactSupport hdata.compactSupport)
    change Continuous (fun v => 𝓕⁻ G v)
    simp_rw [Real.fourierInv_eq_fourier_neg]
    exact hc'.comp continuous_neg
  exact hc.measurable

/-- The public real inverse is the real part of the promoted complex inverse multiplier. [Under the stated conditions](hyp:h). [This is the stated conclusion](goal). -/
-- @node: ellF_eq_inverseGaussian_real
lemma ellF_eq_inverseGaussian_real (sigma h v : ℝ) :
    ellF sigma h v =
      (𝓕⁻ (Causalean.Mathlib.Analysis.Fourier.inverseGaussian sigma
        (𝓕 (fun t => (qF h t : ℂ)))) v).re := by
  unfold ellF
  rw [← fourier_eq_scalar_integral, ← fourier_eq_scalar_integral,
    Real.fourierInv_eq_fourier_neg]
  rfl

/-- The public real second moment is bounded by the complex shifted-variance quantity. [Under the stated conditions](hyp:h,hh,hkappa). [This is the stated conclusion](goal). -/
-- @node: ellF_Vq_le_shiftedVariance
lemma ellF_Vq_le_shiftedVariance (kappa sigma h : ℝ)
    (hkappa : kappa ∈ Icc (0 : ℝ) 2) (hh : 0 < h) :
    Vq kappa sigma (ellF sigma h) ≤
      Causalean.Stat.Nonparametric.shiftedVariance kappa sigma
        (𝓕⁻ (Causalean.Mathlib.Analysis.Fourier.inverseGaussian sigma
          (𝓕 (fun t => (qF h t : ℂ))))) := by
  let G := Causalean.Mathlib.Analysis.Fourier.inverseGaussian sigma
    (𝓕 (fun t => (qF h t : ℂ)))
  have hGi : Integrable G := qF_inverse_multiplier_integrable sigma h hh
  have hg : Measurable (𝓕⁻ G) := by
    have hc : Continuous (𝓕 G) := VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (by fun_prop) hGi
    change Measurable (fun v => 𝓕⁻ G v)
    simp_rw [Real.fourierInv_eq_fourier_neg]
    exact (hc.comp continuous_neg).measurable
  have hv := Causalean.Stat.Nonparametric.shiftedVariance_realPart_le
    (𝓕⁻ G) kappa sigma hg (qF_inverseGaussian_joint_integrable kappa sigma h hkappa hh)
  rw [ellF_Vq_integral kappa sigma h hkappa.1]
  simpa only [Causalean.Stat.Nonparametric.shiftedVariance,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, ellF_eq_inverseGaussian_real] using hv

/-- The promoted specialization gives the full uniform inverse-variance envelope in S7. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hkappa). -/
-- @node: ellF_variance_bound
lemma ellF_variance_bound (kappa : ℝ) (hkappa : kappa ∈ Icc (0 : ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ h ∈ Ioc (0 : ℝ) (1/4), ∀ sigma ∈ Icc (0 : ℝ) (1/4),
      Vq kappa sigma (ellF sigma h) ≤
        C * h^(kappa+1) * (1+sigma/h)^10 * Real.exp (36*(sigma/h)^2) := by
  obtain ⟨a, b, ha, hb, hprofile⟩ := qF_fourier_profile_bounds
  let C := 32*(6/Real.pi)*(3*a^2 + (2*Real.pi)⁻¹^2 * (b+12*Real.pi*a)^2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C+1, by positivity, ?_⟩
  intro h hh sigma hsigma
  obtain ⟨hinv, hinvD⟩ := qF_inverseGaussian_integrable sigma h hh.1
  have hbound := Causalean.Stat.Nonparametric.inverseGaussian_shiftedVariance_le
    (𝓕 (fun t => (qF h t : ℂ))) kappa sigma h a b
    ((qF_fourier_contDiff h hh.1).of_le (by norm_num)) (qF_fourier_hasCompactSupport h hh.1)
    hkappa.1 hkappa.2 hh.1 hh.2 hsigma.1 ha hb
    (qF_fourier_support_radius h hh.1) (hprofile h hh.1).1 (hprofile h hh.1).2
    hinv hinvD (qF_inverseGaussian_joint_integrable kappa sigma h hkappa hh.1)
  apply (ellF_Vq_le_shiftedVariance kappa sigma h hkappa hh.1).trans (hbound.trans _)
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (Real.rpow_nonneg hh.1.le _)

/-- S1 and S7 assemble the observable certificate in S8, with its stochastic term kept under
one square root for subsequent tuning. All constants are independent of n, h and sigma. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hbeta,hkappa). -/
-- @node: qF_certificate_bound
lemma qF_certificate_bound (beta kappa : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∀ h ∈ Ioc (0 : ℝ) (1/4),
      ∀ sigma ∈ Icc (0 : ℝ) (1/4),
      unitAq beta kappa n sigma ⟨qF h, ellF sigma h⟩ ≤
        C * (h^beta + Real.sqrt (h^(-kappa-1) * (1+sigma/h)^10 *
          Real.exp (36*(sigma/h)^2) / n) + Real.sqrt (1/(n : ℝ))) := by
  obtain ⟨Cb, hCb, hbias⟩ := qF_bias_bound beta kappa hbeta hkappa
  obtain ⟨Cv, hCv, hvar⟩ := ellF_variance_bound kappa hkappa
  let c := weightMoment kappa (qF 1)
  have hc : 0 < c := qF_weightMoment_pos kappa hkappa.1 1
  let D := (192/c)*Real.sqrt Cv
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let E := 2*Real.sqrt 3
  have hE : 0 ≤ E := by dsimp [E]; positivity
  refine ⟨Cb+D+E+1, by positivity, ?_⟩
  intro n hn h hh sigma hsigma
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hhR : 0 < h := hh.1
  let H := h^(kappa+1)
  let X := (1+sigma/h)^10 * Real.exp (36*(sigma/h)^2)
  have hH : 0 < H := Real.rpow_pos_of_pos hhR _
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hlo : H*c ≤ weightMoment kappa (qF h) := qF_weightMoment_lower kappa h
    ⟨hkappa.1, by linarith [hkappa.2]⟩ ⟨hh.1, by linarith [hh.2]⟩
  have hcoef : 12 / unitbq kappa (qF h) ≤ (192/c)/H := by
    calc
      _ = 192 / weightMoment kappa (qF h) := by unfold unitbq; ring
      _ ≤ 192/(H*c) := div_le_div_of_nonneg_left (by norm_num) (mul_pos hH hc) hlo
      _ = _ := by ring
  have hv : Real.sqrt (Vq kappa sigma (ellF sigma h) / n) ≤
      Real.sqrt (Cv*H*X/n) := by
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_right (by simpa only [H, X, mul_assoc] using hvar h hh sigma hsigma) hnR.le
  have hscale : Real.sqrt (Cv*H*X/n) / H =
      Real.sqrt Cv * Real.sqrt (h^(-kappa-1)*X/n) := by
    have hp : h^(-kappa-1) = H⁻¹ := by
      dsimp [H]
      rw [show -kappa-1 = -(kappa+1) by ring, Real.rpow_neg hhR.le]
    rw [hp]
    have hsH : Real.sqrt (H^(2 : ℕ)) = H := Real.sqrt_sq hH.le
    calc
      _ = Real.sqrt ((Cv*H*X/n)/H^(2 : ℕ)) := by
        simpa only [hsH] using
          (Real.sqrt_div (show 0 ≤ Cv*H*X/n by positivity) (H^(2 : ℕ))).symm
      _ = _ := by
        have he : (Cv*H*X/n)/H^(2 : ℕ) = Cv*(H⁻¹*X/n) := by field_simp
        rw [he, Real.sqrt_mul hCv.le]
  have hnoise : (12 / unitbq kappa (qF h)) * Real.sqrt (Vq kappa sigma (ellF sigma h) / n) ≤
      D * Real.sqrt (h^(-kappa-1)*X/n) := by
    calc
      _ ≤ ((192/c)/H) * Real.sqrt (Cv*H*X/n) :=
        mul_le_mul hcoef hv (Real.sqrt_nonneg _) (by positivity)
      _ = (192/c) * (Real.sqrt (Cv*H*X/n) / H) := by ring
      _ = _ := by rw [hscale]; dsimp [D]; ring
  have hfreq : 2*Real.sqrt (3/(n : ℝ)) = E*Real.sqrt (1/(n : ℝ)) := by
    rw [show (3 : ℝ)/n = 3*(1/n) by ring, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    dsimp [E]
    ring
  have hA : unitAq beta kappa n sigma ⟨qF h, ellF sigma h⟩ ≤
      Cb*h^beta + D*Real.sqrt (h^(-kappa-1)*X/n) + E*Real.sqrt (1/(n : ℝ)) := by
    unfold unitAq
    dsimp only
    rw [hfreq]
    exact add_le_add (add_le_add (hbias h hh) hnoise) le_rfl
  have ht : 0 ≤ h^beta := Real.rpow_nonneg hhR.le _
  have hcb : Cb ≤ Cb+D+E+1 := by linarith
  have hd : D ≤ Cb+D+E+1 := by linarith
  have he : E ≤ Cb+D+E+1 := by linarith
  have hsum : Cb*h^beta + D*Real.sqrt (h^(-kappa-1)*X/n) + E*Real.sqrt (1/(n : ℝ)) ≤
      (Cb+D+E+1) * (h^beta + Real.sqrt (h^(-kappa-1)*X/n) + Real.sqrt (1/(n : ℝ))) := by
    nlinarith [mul_le_mul_of_nonneg_right hcb ht,
      mul_le_mul_of_nonneg_right hd (Real.sqrt_nonneg (h^(-kappa-1)*X/n)),
      mul_le_mul_of_nonneg_right he (Real.sqrt_nonneg (1/(n : ℝ)))]
  simpa only [X, mul_assoc] using hA.trans hsum

end CausalSmith.Stat.NoisydoseWeakdesignTransition

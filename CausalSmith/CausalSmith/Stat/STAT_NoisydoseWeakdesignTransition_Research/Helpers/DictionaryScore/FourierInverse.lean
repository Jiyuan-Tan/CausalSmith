module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.DictionaryScore.Fourier
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Finite box convolutions and Gaussian inversion for the Fourier dictionary. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Convolution
open scoped ENNReal Topology FourierTransform
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- The uniform frequency box whose transform is the bandwidth-scaled sinc. -/
-- @node: fourierSincBox
def fourierSincBox (h t : ℝ) : ℂ :=
  (Ioc (-((2*Real.pi*h)⁻¹)) ((2*Real.pi*h)⁻¹)).indicator
    (fun _ => (Real.pi*h : ℂ)) t

/-- The frequency box has finite absolute mass. [Under the stated conditions](hyp:h). [This is the stated conclusion](goal). [This is the stated conclusion](goal). [This is the stated conclusion](goal). [This is the stated conclusion](goal). -/
-- @node: fourierSincBox_integrable
lemma fourierSincBox_integrable (h : ℝ) : Integrable (fourierSincBox h) := by
  exact (continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self).integrable_indicator
    measurableSet_Ioc

/-- Direct integration of the uniform box gives the sinc transform. [Under the stated conditions](hyp:h,hh). [This is the stated conclusion](goal). -/
-- @node: fourier_fourierSincBox
lemma fourier_fourierSincBox (h : ℝ) (hh : 0 < h) (x : ℝ) :
    FourierTransform.fourier (fourierSincBox h) x = (Real.sinc (x/h) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold fourierSincBox
  let a : ℝ := (2*Real.pi*h)⁻¹
  have ha : 0 < a := by dsimp [a]; positivity
  have hind :
      (fun v : ℝ => Complex.exp (↑(-2*Real.pi*v*x)*Complex.I) •
        (Ioc (-a) a).indicator (fun _ => (Real.pi*h : ℂ)) v) =
      (Ioc (-a) a).indicator (fun v =>
        Complex.exp (↑(-2*Real.pi*v*x)*Complex.I) • (Real.pi*h : ℂ)) := by
    funext v
    by_cases hv : v ∈ Ioc (-a) a <;> simp [Set.indicator, hv]
  change (∫ v : ℝ, Complex.exp (↑(-2*Real.pi*v*x)*Complex.I) •
    (Ioc (-a) a).indicator (fun _ => (Real.pi*h : ℂ)) v) = _
  rw [hind, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (neg_le_self ha.le)]
  by_cases hx : x = 0
  · subst x
    simp [a]
    field_simp [Real.pi_ne_zero, hh.ne'] <;> ring
  · simp_rw [smul_eq_mul]
    rw [intervalIntegral.integral_mul_const]
    have hexp : (fun t : ℝ => Complex.exp (↑(-2*Real.pi*t*x)*Complex.I)) =
        (fun t : ℝ => Complex.exp ((↑(-2*Real.pi*x)*Complex.I)*t)) := by
      funext t; congr 1; push_cast; ring
    rw [hexp, integral_exp_mul_complex]
    · rw [Real.sinc_of_ne_zero (div_ne_zero hx hh.ne')]
      dsimp [a]
      push_cast
      have h₁ : -2*(Real.pi : ℂ)*x*Complex.I*(2*(Real.pi : ℂ)*h)⁻¹ =
          -(x/h : ℂ)*Complex.I := by field_simp [Real.pi_ne_zero, hh.ne']
      have h₂ : -2*(Real.pi : ℂ)*x*Complex.I*-(2*(Real.pi : ℂ)*h)⁻¹ =
          (x/h : ℂ)*Complex.I := by field_simp [Real.pi_ne_zero, hh.ne']
      rw [h₁, h₂]
      simp only [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
      field_simp [Real.pi_ne_zero, hx, hh.ne']
      ring
    · norm_num [Real.pi_ne_zero, hx]

/-- Supports of two box convolutions add their radii. [Under the stated conditions](hyp:f,g,hf,hg). [This is the stated conclusion](goal). -/
-- @node: convolution_support_Icc
lemma convolution_support_Icc (f g : ℝ → ℂ) (a b : ℝ)
    (hf : Function.support f ⊆ Icc (-a) a)
    (hg : Function.support g ⊆ Icc (-b) b) :
    Function.support (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) ⊆ Icc (-(a+b)) (a+b) := by
  intro x hx
  rcases support_convolution_subset (ContinuousLinearMap.mul ℂ ℂ) hx with
    ⟨u, hu, v, hv, huv⟩
  have hu' := hf hu
  have hv' := hg hv
  subst x
  exact ⟨by linarith [hu'.1, hv'.1], by linarith [hu'.2, hv'.2]⟩

/-- The sixth sinc power is the Fourier transform of six uniform boxes (S2--S3). [Under the stated conditions](hyp:h,hh). [This is the stated conclusion](goal). -/
-- @node: qF_fourier_box_representation
lemma qF_fourier_box_representation (h : ℝ) (hh : 0 < h) :
    ∃ p : ℝ → ℂ, Integrable p ∧
      Function.support p ⊆ Icc (-(6*(2*Real.pi*h)⁻¹)) (6*(2*Real.pi*h)⁻¹) ∧
      ∀ x, FourierTransform.fourier p x = (qF h x : ℂ) := by
  let a : ℝ := (2*Real.pi*h)⁻¹
  let b := fourierSincBox h
  let q := b ⋆[ContinuousLinearMap.mul ℂ ℂ] b
  let r := q ⋆[ContinuousLinearMap.mul ℂ ℂ] b
  let p := r ⋆[ContinuousLinearMap.mul ℂ ℂ] r
  have hb : Integrable b := fourierSincBox_integrable h
  have hq : Integrable q := hb.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hb
  have hr : Integrable r := hq.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hb
  have hp : Integrable p := hr.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hr
  have hbs : Function.support b ⊆ Icc (-a) a := by
    intro x hx
    by_contra hn
    exact hx (indicator_of_notMem (fun hx' => hn ⟨hx'.1.le, hx'.2⟩) _)
  have hqs := convolution_support_Icc b b a a hbs hbs
  have hrs := convolution_support_Icc q b (a+a) a hqs hbs
  have hps := convolution_support_Icc r r (a+a+a) (a+a+a) hrs hrs
  refine ⟨p, hp, ?_, ?_⟩
  · convert hps using 1 <;> congr 1 <;> dsimp [a] <;> ring
  · intro x
    dsimp [p, r, q]
    rw [Real.fourier_mul_convolution_eq hr hr,
      Real.fourier_mul_convolution_eq hq hb,
      Real.fourier_mul_convolution_eq hb hb, fourier_fourierSincBox h hh]
    simp only [qF, sincSix_eq_sinc_pow, Complex.ofReal_pow]
    ring

/-- The sinc-six localization is absolutely integrable on the real line. [Under the stated conditions](hyp:h,hh). [This is the stated conclusion](goal). -/
-- @node: qF_integrable_complex
lemma qF_integrable_complex (h : ℝ) (hh : 0 < h) :
    Integrable (fun t => (qF h t : ℂ)) := by
  have hi := qF_whole_weighted_integrable 0 h (by norm_num) hh
  simp only [Real.rpow_zero, one_mul] at hi
  exact hi.ofReal

/-- Fourier inversion of the finite box convolution proves compact spectral support. [Under the stated conditions](hyp:h,hh). [This is the stated conclusion](goal). -/
-- @node: qF_fourier_support
lemma qF_fourier_support (h : ℝ) (hh : 0 < h) :
    Function.support (FourierTransform.fourier (fun t => (qF h t : ℂ))) ⊆
      Icc (-(6*(2*Real.pi*h)⁻¹)) (6*(2*Real.pi*h)⁻¹) := by
  obtain ⟨p, hp, hs, hF⟩ := qF_fourier_box_representation h hh
  let R := 6*(2*Real.pi*h)⁻¹
  have hFi : Integrable (FourierTransform.fourier p) := by
    rw [funext hF]; exact qF_integrable_complex h hh
  intro xi hxi
  by_contra hn
  have hneg : -xi ∉ Icc (-R) R := by
    intro ht; exact hn ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hevent : p =ᶠ[nhds (-xi)] fun _ => 0 := by
    filter_upwards [IsOpen.mem_nhds isClosed_Icc.isOpen_compl hneg] with y hy
    by_contra hpy
    exact hy (hs hpy)
  have hc : ContinuousAt p (-xi) := continuousAt_const.congr_of_eventuallyEq hevent
  have hi := hp.fourierInv_fourier_eq hFi hc
  rw [funext hF, Real.fourierInv_eq_fourier_neg] at hi
  have hz : p (-xi) = 0 := by
    by_contra hpy; exact hneg (hs hpy)
  apply hxi
  simpa only [neg_neg, hz] using hi

/-- The continuous transform is integrable because its spectrum is compact. [Under the stated conditions](hyp:h,hh). [This is the stated conclusion](goal). -/
-- @node: qF_fourier_integrable
lemma qF_fourier_integrable (h : ℝ) (hh : 0 < h) :
    Integrable (FourierTransform.fourier (fun t => (qF h t : ℂ))) := by
  apply (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by fun_prop) (qF_integrable_complex h hh)).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  exact qF_fourier_support h hh

/-- The scalar and vector Fourier conventions agree on the real line. [Under the stated conditions](hyp:f). [This is the stated conclusion](goal). -/
-- @node: fourier_eq_scalar_integral
lemma fourier_eq_scalar_integral (f : ℝ → ℂ) :
    FourierTransform.fourier f = Fourier.fourierIntegral Real.fourierChar volume f := by
  funext w
  rw [Real.fourier_real_eq]
  rfl

/-- Compact spectral support makes the inverse Gaussian multiplier integrable. [Under the stated conditions](hyp:h,hh). [This is the stated conclusion](goal). -/
-- @node: qF_inverse_multiplier_integrable
lemma qF_inverse_multiplier_integrable (sigma h : ℝ) (hh : 0 < h) :
    Integrable (fun xi => FourierTransform.fourier (fun t => (qF h t : ℂ)) xi *
      (Real.exp (sigma^2*(2*Real.pi*xi)^2/2) : ℂ)) := by
  have hc : Continuous (FourierTransform.fourier (fun t => (qF h t : ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by fun_prop) (qF_integrable_complex h hh)
  apply (hc.mul (by fun_prop)).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  exact (Function.support_mul_subset_left _ _).trans (qF_fourier_support h hh)

/-- Gaussian averaging cancels the inverse multiplier frequency by frequency. [This is the stated conclusion](goal). -/
-- @node: gaussian_fourier_phase
lemma gaussian_fourier_phase (sigma t xi : ℝ) :
    (∫ z : ℝ, Complex.exp (↑(2*Real.pi*xi*(t+sigma*z))*Complex.I)
      ∂gaussianReal 0 1) =
    Complex.exp (↑(2*Real.pi*xi*t)*Complex.I) *
      (Real.exp (-(sigma^2*(2*Real.pi*xi)^2/2)) : ℂ) := by
  have heq : (fun z : ℝ => Complex.exp (↑(2*Real.pi*xi*(t+sigma*z))*Complex.I)) =
      (fun z : ℝ => Complex.exp (↑(2*Real.pi*xi*t)*Complex.I) *
        Complex.exp (↑((2*Real.pi*xi*sigma)*z)*Complex.I)) := by
    funext z
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [heq, integral_const_mul]
  congr 1
  simp_rw [show ∀ z : ℝ, (↑((2*Real.pi*xi*sigma)*z) : ℂ) =
    ↑(2*Real.pi*xi*sigma) * ↑z from fun z => Complex.ofReal_mul _ _]
  rw [← charFun_apply_real, charFun_gaussianReal]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
  rw [Complex.ofReal_exp]
  congr 1
  norm_num
  ring

/-- Absolute Fubini gives exact cancellation of the Gaussian multiplier (S4--S5). [Under the stated conditions](hyp:h,hh). [This is the stated conclusion](goal). -/
-- @node: ellF_gaussian_inverse
lemma ellF_gaussian_inverse (sigma h t : ℝ) (hh : 0 < h) :
    (∫ z, ellF sigma h (t+sigma*z) ∂gaussianReal 0 1) = qF h t := by
  let F : ℝ → ℂ := FourierTransform.fourier (fun u => (qF h u : ℂ))
  let G : ℝ → ℂ := fun xi => F xi * (Real.exp (sigma^2*(2*Real.pi*xi)^2/2) : ℂ)
  have hG : Integrable G := qF_inverse_multiplier_integrable sigma h hh
  let K : ℝ → ℝ → ℂ := fun z xi =>
    Complex.exp (↑(2*Real.pi*xi*(t+sigma*z))*Complex.I) * G xi
  have hFc : Continuous F := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (by fun_prop) (qF_integrable_complex h hh)
  have hGc : Continuous G := hFc.mul (by fun_prop)
  have hKc : Continuous (Function.uncurry K) := by
    dsimp [K, Function.uncurry]
    exact (show Continuous (fun p : ℝ × ℝ =>
      Complex.exp (↑(2*Real.pi*p.2*(t+sigma*p.1))*Complex.I)) by fun_prop).mul
      (hGc.comp continuous_snd)
  have hK : Integrable (Function.uncurry K) ((gaussianReal 0 1).prod volume) := by
    apply ((integrable_const (1 : ℝ) (μ := gaussianReal 0 1)).mul_prod hG.norm).mono'
      hKc.aestronglyMeasurable
    filter_upwards with p
    change ‖Complex.exp (↑(2*Real.pi*p.2*(t+sigma*p.1))*Complex.I) * G p.2‖ ≤
      1 * ‖G p.2‖
    rw [norm_mul, Complex.norm_exp]
    simp
  have hKg : Integrable (fun z => ∫ xi, K z xi) (gaussianReal 0 1) :=
    hK.integral_prod_left
  have hell (v : ℝ) : ellF sigma h v =
      (∫ xi, Complex.exp (↑(2*Real.pi*xi*v)*Complex.I) * G xi).re := by
    unfold ellF
    rw [← fourier_eq_scalar_integral, ← fourier_eq_scalar_integral,
      Real.fourier_real_eq_integral_exp_smul]
    congr 1
    apply integral_congr_ae
    filter_upwards with xi
    dsimp [G, F]
    congr 2
    push_cast
    ring
  simp_rw [hell]
  have hRe : (∫ z, (∫ xi, K z xi).re ∂gaussianReal 0 1) =
      (∫ z, (∫ xi, K z xi) ∂gaussianReal 0 1).re :=
    Complex.reCLM.integral_comp_comm hKg
  change (∫ z, (∫ xi, K z xi).re ∂gaussianReal 0 1) = _
  rw [hRe, integral_integral_swap hK]
  have hfreq (xi : ℝ) : (∫ z, K z xi ∂gaussianReal 0 1) =
      Complex.exp (↑(2*Real.pi*xi*t)*Complex.I) * F xi := by
    dsimp [K]
    rw [integral_mul_const, gaussian_fourier_phase]
    dsimp [G]
    rw [show (Complex.exp (↑(2*Real.pi*xi*t)*Complex.I) *
        ↑(Real.exp (-(sigma^2*(2*Real.pi*xi)^2/2)))) *
        (F xi * ↑(Real.exp (sigma^2*(2*Real.pi*xi)^2/2))) =
        Complex.exp (↑(2*Real.pi*xi*t)*Complex.I) * F xi *
          ↑(Real.exp (-(sigma^2*(2*Real.pi*xi)^2/2)) *
            Real.exp (sigma^2*(2*Real.pi*xi)^2/2)) by push_cast; ring]
    rw [← Real.exp_add]
    simp
  simp_rw [hfreq]
  have hinv := (qF_integrable_complex h hh).fourierInv_fourier_eq
    (qF_fourier_integrable h hh) ((Complex.continuous_ofReal.comp (qF_continuous h)).continuousAt (x := t))
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul] at hinv
  have heq : (∫ xi, Complex.exp (↑(2*Real.pi*xi*t)*Complex.I) * F xi) =
      (qF h t : ℂ) := by
    convert hinv using 1
    apply integral_congr_ae
    filter_upwards with xi
    dsimp [F]
    congr 2
    push_cast
    ring
  rw [heq]
  rfl

/-- Exact Fourier inversion has positive finite weighted moments and finite Gaussian second moments. [Under the stated conditions](hyp:h,hkappa,hsigma,hvalid). [This is the stated conclusion](goal). -/
-- @node: fourier_pair_admissible
lemma fourier_pair_admissible (kappa sigma : ℝ) (hkappa : kappa ∈ Icc (0 : ℝ) 2)
    (hsigma : sigma ∈ Icc (0 : ℝ) (1/4)) (h : ℝ) (hvalid : h ∈ Ioc (0 : ℝ) (1/4)) :
    PairAdmissible kappa sigma ⟨qF h, ellF sigma h⟩ ∧ VqENN kappa sigma (⟨qF h, ellF sigma h⟩ : WeightPair).ell < ⊤ := by
  have hinverse :
      (∀ t ∈ Icc (-1/2 : ℝ) (1/2),
        Integrable (fun z => ellF sigma h (t+sigma*z)) (gaussianReal 0 1)) ∧
      (∀ t ∈ Icc (-1/2 : ℝ) (1/2),
        ∫ z, ellF sigma h (t+sigma*z) ∂gaussianReal 0 1 = qF h t) ∧
      VqENN kappa sigma (ellF sigma h) < ⊤ := by
    refine ⟨fun t _ => ellF_gaussian_integrable sigma h t, ?_,
      ellF_VqENN_lt_top kappa sigma h hkappa.1⟩
    intro t ht
    exact ellF_gaussian_inverse sigma h t hvalid.1
  refine ⟨?_, hinverse.2.2⟩
  exact ⟨(qF_continuous h).measurable, ellF_measurable sigma h,
    fun t _ => qF_nonneg h t, qF_weighted_integrable kappa hkappa.1 h,
    qF_weightMoment_pos kappa hkappa.1 h, hinverse.1, hinverse.2.1⟩

/-- The public Fourier second moment is an ordinary nonnegative joint integral. [Under the stated conditions](hyp:h,hkappa). [This is the stated conclusion](goal). -/
-- @node: ellF_Vq_integral
lemma ellF_Vq_integral (kappa sigma h : ℝ) (hkappa : 0 ≤ kappa) :
    Vq kappa sigma (ellF sigma h) =
      16 * ∫ t in Icc (-1/2 : ℝ) (1/2),
        |t| ^ kappa * (∫ z, (ellF sigma h (t+sigma*z))^2 ∂gaussianReal 0 1) := by
  have hi := ellF_weighted_sq_integrable kappa sigma h hkappa
  have hn : ∀ x : ℝ × ℝ, 0 ≤ |x.1| ^ kappa * (ellF sigma h (x.1+sigma*x.2))^2 :=
    fun x => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _)
  have he := ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn)
  rw [lintegral_prod _ (by fun_prop)] at he
  simp_rw [ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _)] at he
  have hm : ∀ t : ℝ, Measurable (fun z => ENNReal.ofReal ((ellF sigma h (t+sigma*z))^2)) := by
    intro t
    fun_prop
  simp_rw [lintegral_const_mul _ (hm _)] at he
  have hj := integral_prod _ hi
  simp_rw [integral_const_mul] at hj
  rw [Vq, VqENN, ENNReal.toReal_mul, ← he, ENNReal.toReal_ofReal
    (integral_nonneg hn), hj]
  norm_num

end CausalSmith.Stat.NoisydoseWeakdesignTransition

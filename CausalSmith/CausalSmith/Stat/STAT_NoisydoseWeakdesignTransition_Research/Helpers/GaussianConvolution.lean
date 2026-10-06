module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.LowerWitness
public import Mathlib.Analysis.SpecificLimits.Normed

/-! Compact signed moments, Gaussian kernels, and witness-density domination -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
variable {S : Type*} [MeasurableSpace S]


/-- Centered Gaussian density on the real line for positive sigma. -/
def phiDensity (sigma w : ℝ) : ℝ :=
  Real.exp (-w^2/(2*sigma^2)) / (Real.sqrt (2*Real.pi)*sigma)
/-- Convolution of an integrable signed density with the centered Gaussian density. -/
def smoothSigned (sigma : ℝ) (v : ℝ → ℝ) (w : ℝ) : ℝ :=
  ∫ t, v t * phiDensity sigma (w-t)
/-- Factorial tail in the observed Gaussian moment-series comparison. -/
def momentTail (sigma ell : ℝ) (J : ℕ) : ℝ :=
  ∑' j : ℕ, if J ≤ j then (ell^2/sigma^2)^j/(j.factorial : ℝ) else 0

/-- The centered Gaussian density is strictly positive at every real argument when its scale is positive. [Under the stated conditions](hyp:hsigma). [This is the stated conclusion](goal). [Under the stated conditions](hyp:hsigma). [This is the stated conclusion](goal). [Under the stated conditions](hyp:hsigma). [This is the stated conclusion](goal). [Under the stated conditions](hyp:hsigma). [This is the stated conclusion](goal). -/
-- @node: phiDensity_pos
lemma phiDensity_pos (sigma w : ℝ) (hsigma : 0 < sigma) : 0 < phiDensity sigma w := by
  unfold phiDensity
  exact div_pos (Real.exp_pos _) (mul_pos (Real.sqrt_pos.mpr (by positivity)) hsigma)

/-- The centered Gaussian density is invariant under reflection. [This is the stated conclusion](goal). -/
-- @node: phiDensity_even
lemma phiDensity_even (sigma w : ℝ) : phiDensity sigma (-w) = phiDensity sigma w := by
  simp [phiDensity]

/-- The compact power-law witness density is nonnegative for nonnegative degeneracy. [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: witnessDesignDensity_nonneg
lemma witnessDesignDensity_nonneg (kappa t : ℝ) (hkappa : 0 ≤ kappa) :
    0 ≤ witnessDesignDensity kappa t := by
  unfold witnessDesignDensity
  split_ifs
  · positivity
  · rfl

/-- The common compact witness density is symmetric about zero. [This is the stated conclusion](goal). -/
-- @node: witnessDesignDensity_even
lemma witnessDesignDensity_even (kappa t : ℝ) :
    witnessDesignDensity kappa (-t) = witnessDesignDensity kappa t := by
  have he : -t ∈ Icc (-1/2 : ℝ) (1/2) ↔ t ∈ Icc (-1/2 : ℝ) (1/2) := by
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  simp only [witnessDesignDensity, he, abs_neg]

/-- On the short interval on the same side as the observed dose, the Gaussian kernel is bounded below by its centered value times exp(-1/2). [Under the stated conditions](hyp:hsigma,hw,ht). [This is the stated conclusion](goal). -/
-- @node: phiDensity_same_side_lower
lemma phiDensity_same_side_lower (sigma w t : ℝ) (hsigma : 0 < sigma)
    (ht : t ∈ Icc (0 : ℝ) sigma) (hw : 0 ≤ w) :
    Real.exp (-1/2) * phiDensity sigma w ≤ phiDensity sigma (w-t) := by
  have hd : 0 < 2*sigma^2 := by positivity
  have hexp : (-1/2 : ℝ) + -(w^2)/(2*sigma^2) ≤ -((w-t)^2)/(2*sigma^2) := by
    apply (le_div_iff₀ hd).mpr
    field_simp
    nlinarith [mul_nonneg hw ht.1, mul_nonneg (sub_nonneg.mpr ht.2) (show 0 ≤ sigma+t by linarith [ht.1])]
  unfold phiDensity
  rw [← mul_div_assoc, ← Real.exp_add]
  exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hexp) (by positivity)

/-- The Gaussian convolution integrand of the compact witness density is integrable. [Under the stated conditions](hyp:hkappa,hsigma). [This is the stated conclusion](goal). -/
-- @node: gaussian_design_integrable
@[fun_prop] lemma gaussian_design_integrable (kappa sigma w : ℝ) (hkappa : 0 ≤ kappa)
    (hsigma : 0 < sigma) :
    Integrable (fun t => witnessDesignDensity kappa t * phiDensity sigma (w-t)) := by
  have hc : Continuous (fun t : ℝ => (kappa+1)*2^kappa*|t|^kappa * phiDensity sigma (w-t)) := by
    unfold phiDensity
    fun_prop
  have he : (fun t => witnessDesignDensity kappa t * phiDensity sigma (w-t)) =
      (Icc (-1/2 : ℝ) (1/2)).indicator
        (fun t : ℝ => (kappa+1)*2^kappa*|t|^kappa * phiDensity sigma (w-t)) := by
    funext t
    simp only [witnessDesignDensity, indicator_apply]
    split_ifs <;> simp
  rw [he]
  exact hc.integrableOn_Icc.integrable_indicator measurableSet_Icc

/-- Convolving the symmetric witness density with a centered Gaussian preserves reflection symmetry. [This is the stated conclusion](goal). -/
-- @node: smoothSigned_design_even
lemma smoothSigned_design_even (kappa sigma w : ℝ) :
    smoothSigned sigma (witnessDesignDensity kappa) (-w) =
      smoothSigned sigma (witnessDesignDensity kappa) w := by
  unfold smoothSigned
  rw [← integral_neg_eq_self (fun t => witnessDesignDensity kappa t * phiDensity sigma (-w-t))]
  congr 1
  funext t
  rw [witnessDesignDensity_even]
  have he : -w-(-t) = -(w-t) := by ring
  rw [he, phiDensity_even]

/-- Integrating over the positive short interval gives the public Gaussian reference-density bound for nonnegative observed doses. [Under the stated conditions](hyp:hkappa,hw,hsigma). [This is the stated conclusion](goal). -/
-- @node: gaussian_design_lower_nonneg
lemma gaussian_design_lower_nonneg (kappa sigma w : ℝ) (hkappa : 0 ≤ kappa)
    (hsigma : sigma ∈ Ioc (0 : ℝ) (1/4)) (hw : 0 ≤ w) :
    Real.exp (-1/2)*sigma^(kappa+1)*phiDensity sigma w ≤
      smoothSigned sigma (witnessDesignDensity kappa) w := by
  let c : ℝ := (kappa+1)*2^kappa
  let f : ℝ → ℝ := fun t => witnessDesignDensity kappa t * phiDensity sigma (w-t)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hp : 0 < phiDensity sigma w := phiDensity_pos sigma w hsigma.1
  have hi : Integrable f := gaussian_design_integrable kappa sigma w hkappa hsigma.1
  have hpow : IntervalIntegrable (fun t : ℝ => t^kappa) volume 0 sigma := by
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < kappa)
  have hcomp : IntervalIntegrable (fun t : ℝ => c*t^kappa*(Real.exp (-1/2)*phiDensity sigma w)) volume 0 sigma :=
    (hpow.const_mul c).mul_const _
  have hmono : (∫ t in (0 : ℝ)..sigma, c*t^kappa*(Real.exp (-1/2)*phiDensity sigma w)) ≤
      ∫ t in (0 : ℝ)..sigma, f t := by
    apply intervalIntegral.integral_mono_on hsigma.1.le hcomp hi.intervalIntegrable
    intro t ht
    have ht' : t ∈ Icc (-1/2 : ℝ) (1/2) := by constructor <;> linarith [ht.1, ht.2, hsigma.2]
    dsimp [f, witnessDesignDensity]
    rw [if_pos ht', abs_of_nonneg ht.1]
    exact mul_le_mul_of_nonneg_left (phiDensity_same_side_lower sigma w t hsigma.1 ht hw)
      (mul_nonneg hc (Real.rpow_nonneg ht.1 _))
  have hsmall : (∫ t in (0 : ℝ)..sigma, f t) ≤ smoothSigned sigma (witnessDesignDensity kappa) w := by
    rw [intervalIntegral.integral_of_le hsigma.1.le]
    exact setIntegral_le_integral hi (ae_of_all _ (fun t =>
      mul_nonneg (witnessDesignDensity_nonneg kappa t hkappa) (phiDensity_pos sigma (w-t) hsigma.1).le))
  have heval : (∫ t in (0 : ℝ)..sigma, c*t^kappa*(Real.exp (-1/2)*phiDensity sigma w)) =
      2^kappa * (Real.exp (-1/2)*sigma^(kappa+1)*phiDensity sigma w) := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by linarith : -1 < kappa)),
      Real.zero_rpow (by linarith : kappa+1 ≠ 0), sub_zero]
    dsimp [c]
    field_simp
  rw [heval] at hmono
  have htwo : 1 ≤ (2 : ℝ)^kappa := Real.one_le_rpow (by norm_num) hkappa
  calc
    _ ≤ 2^kappa * (Real.exp (-1/2)*sigma^(kappa+1)*phiDensity sigma w) := by
      exact le_mul_of_one_le_left
        (mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hsigma.1.le _)) hp.le) htwo
    _ ≤ _ := hmono.trans hsmall

/-- Positive Gaussian reference-density domination holds on the entire observed real line. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hkappa,hsigma). -/
-- @node: gaussian_design_density_lower
lemma gaussian_design_density_lower (kappa sigma : ℝ)
    (hkappa : kappa ∈ Icc (0 : ℝ) 2) (hsigma : sigma ∈ Ioc (0 : ℝ) (1/4)) :
    ∀ w, 0 < smoothSigned sigma (witnessDesignDensity kappa) w ∧
      Real.exp (-1/2)*sigma^(kappa+1)*phiDensity sigma w ≤
        smoothSigned sigma (witnessDesignDensity kappa) w := by
  intro w
  have hlower : Real.exp (-1/2)*sigma^(kappa+1)*phiDensity sigma w ≤
      smoothSigned sigma (witnessDesignDensity kappa) w := by
    by_cases hw : 0 ≤ w
    · exact gaussian_design_lower_nonneg kappa sigma w hkappa.1 hsigma hw
    · have h := gaussian_design_lower_nonneg kappa sigma (-w) hkappa.1 hsigma (by linarith)
      simpa only [phiDensity_even, smoothSigned_design_even] using h
  exact ⟨(mul_pos (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hsigma.1 _))
    (phiDensity_pos sigma w hsigma.1)).trans_le hlower, hlower⟩

/-- Every polynomial moment of a compactly supported integrable signed density is integrable. [Under the stated conditions](hyp:hell,hv,hsupp). [This is the stated conclusion](goal). -/
-- @node: compact_signed_moment_integrable
lemma compact_signed_moment_integrable (ell : ℝ) (hell : 0 ≤ ell)
    (v : ℝ → ℝ) (hv : Integrable v)
    (hsupp : ∀ t, t ∉ Icc (-ell) ell → v t = 0) (j : ℕ) :
    Integrable (fun t => t^j*v t) := by
  apply (hv.norm.const_mul (ell^j)).mono' ((by fun_prop : Measurable (fun t : ℝ => t^j)).aestronglyMeasurable.mul hv.aestronglyMeasurable)
  filter_upwards with t
  by_cases ht : t ∈ Icc (-ell) ell
  · simp only [Pi.mul_apply, norm_mul, Real.norm_eq_abs, abs_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg t) (abs_le.mpr ht) j) (abs_nonneg _)
  · simp [hsupp t ht]

/-- The absolute signed moment is bounded by the support radius power times the absolute mass. [Under the stated conditions](hyp:hell,hv,hsupp). [This is the stated conclusion](goal). -/
-- @node: compact_signed_moment_bound
lemma compact_signed_moment_bound (ell : ℝ) (hell : 0 ≤ ell)
    (v : ℝ → ℝ) (hv : Integrable v)
    (hsupp : ∀ t, t ∉ Icc (-ell) ell → v t = 0) (j : ℕ) :
    |∫ t, t^j*v t| ≤ ell^j * ∫ t, |v t| := by
  calc
    _ ≤ ∫ t, |t^j*v t| := abs_integral_le_integral_abs
    _ ≤ ∫ t, ell^j * |v t| := by
      apply integral_mono_ae (compact_signed_moment_integrable ell hell v hv hsupp j).norm (hv.norm.const_mul _)
      filter_upwards with t
      by_cases ht : t ∈ Icc (-ell) ell
      · simp only [Real.norm_eq_abs, abs_mul, abs_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg t) (abs_le.mpr ht) j) (abs_nonneg _)
      · simp [hsupp t ht]
    _ = _ := integral_const_mul _ _
/-- Each squared Gaussian moment coefficient is bounded by the corresponding factorial majorant. [Under the stated conditions](hyp:hsigma,hell,hv,hsupp). [This is the stated conclusion](goal). -/
-- @node: compact_signed_moment_coefficient_bound
lemma compact_signed_moment_coefficient_bound (sigma ell : ℝ)
    (hsigma : 0 < sigma) (hell : 0 ≤ ell) (v : ℝ → ℝ) (hv : Integrable v)
    (hsupp : ∀ t, t ∉ Icc (-ell) ell → v t = 0) (j : ℕ) :
    (∫ t, t^j*v t)^2 / (sigma^(2*j)*(j.factorial : ℝ)) ≤
      (∫ t, |v t|)^2 * ((ell^2/sigma^2)^j/(j.factorial : ℝ)) := by
  have hm := compact_signed_moment_bound ell hell v hv hsupp j
  have hmass : 0 ≤ ∫ t, |v t| := integral_nonneg (fun _ => abs_nonneg _)
  have hsq : (∫ t, t^j*v t)^2 ≤ (ell^j * ∫ t, |v t|)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg (pow_nonneg hell j) hmass)).mpr hm
  calc
    _ ≤ (ell^j * ∫ t, |v t|)^2 / (sigma^(2*j)*(j.factorial : ℝ)) :=
      div_le_div_of_nonneg_right hsq (by positivity)
    _ = _ := by
      rw [div_pow, pow_mul, mul_pow]
      ring

/-- The Gaussian squared-moment series converges by comparison with the exponential series. [Under the stated conditions](hyp:hsigma,hell,hv,hsupp). [This is the stated conclusion](goal). -/
-- @node: compact_signed_moment_summable
lemma compact_signed_moment_summable (sigma ell : ℝ)
    (hsigma : 0 < sigma) (hell : 0 ≤ ell) (v : ℝ → ℝ) (hv : Integrable v)
    (hsupp : ∀ t, t ∉ Icc (-ell) ell → v t = 0) :
    Summable (fun j : ℕ => (∫ t, t^j*v t)^2 / (sigma^(2*j)*(j.factorial : ℝ))) := by
  apply Summable.of_nonneg_of_le (fun j => by positivity)
    (compact_signed_moment_coefficient_bound sigma ell hsigma hell v hv hsupp)
    ((Real.summable_pow_div_factorial (ell^2/sigma^2)).mul_left ((∫ t, |v t|)^2))
/-- The factorial tail is summable for every real scale and radius. [This is the stated conclusion](goal). -/
-- @node: momentTail_summable
lemma momentTail_summable (sigma ell : ℝ) (J : ℕ) :
    Summable (fun j : ℕ => if J ≤ j then (ell^2/sigma^2)^j/(j.factorial : ℝ) else 0) := by
  apply Summable.of_nonneg_of_le (fun j => by split_ifs <;> positivity)
    (fun j => by split_ifs <;> first | exact le_rfl | positivity)
    (Real.summable_pow_div_factorial (ell^2/sigma^2))

/-- The unmatched squared-moment sum is bounded by absolute mass squared times the public factorial tail. [Under the stated conditions](hyp:hsigma,hell,hv,hsupp). [This is the stated conclusion](goal). -/
-- @node: compact_signed_moment_tail_bound
lemma compact_signed_moment_tail_bound (sigma ell : ℝ)
    (hsigma : 0 < sigma) (hell : 0 ≤ ell) (J : ℕ) (v : ℝ → ℝ) (hv : Integrable v)
    (hsupp : ∀ t, t ∉ Icc (-ell) ell → v t = 0) :
    (∑' j : ℕ, if J ≤ j then (∫ t, t^j*v t)^2 / (sigma^(2*j)*(j.factorial : ℝ)) else 0) ≤
      (∫ t, |v t|)^2 * momentTail sigma ell J := by
  have hs : Summable (fun j : ℕ => if J ≤ j then
      (∫ t, t^j*v t)^2 / (sigma^(2*j)*(j.factorial : ℝ)) else 0) := by
    apply Summable.of_nonneg_of_le (fun j => by split_ifs <;> positivity)
      (fun j => by split_ifs <;> first | exact le_rfl | positivity)
      (compact_signed_moment_summable sigma ell hsigma hell v hv hsupp)
  unfold momentTail
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum _ hs ((momentTail_summable sigma ell J).mul_left _)
  intro j
  split_ifs with hj
  · exact compact_signed_moment_coefficient_bound sigma ell hsigma hell v hv hsupp j
  · simp
/-- Completing the square expresses the Gaussian kernel quotient as a translated Gaussian times an exponential. [Under the stated conditions](hyp:hsigma). [This is the stated conclusion](goal). -/
-- @node: phiDensity_product_div
lemma phiDensity_product_div (sigma w t s : ℝ) (hsigma : 0 < sigma) :
    phiDensity sigma (w-t) * phiDensity sigma (w-s) / phiDensity sigma w =
      Real.exp (t*s/sigma^2) * phiDensity sigma (w-t-s) := by
  have hd : Real.sqrt (2*Real.pi)*sigma ≠ 0 :=
    ne_of_gt (mul_pos (Real.sqrt_pos.mpr (by positivity)) hsigma)
  have he : -(w-t)^2/(2*sigma^2) + -(w-s)^2/(2*sigma^2) - (-w^2/(2*sigma^2)) =
      t*s/sigma^2 + -(w-t-s)^2/(2*sigma^2) := by
    field_simp
    <;> ring
  unfold phiDensity
  rw [div_mul_div_comm, div_div_div_comm, ← Real.exp_add, ← Real.exp_sub, he, Real.exp_add]
  field_simp

/-- The centered density agrees with Mathlib’s Gaussian density at variance sigma squared. [Under the stated conditions](hyp:hsigma). [This is the stated conclusion](goal). -/
-- @node: phiDensity_eq_gaussianPDFReal
lemma phiDensity_eq_gaussianPDFReal (sigma w : ℝ) (hsigma : 0 < sigma) :
    phiDensity sigma w = gaussianPDFReal 0 ⟨sigma^2, sq_nonneg sigma⟩ w := by
  unfold phiDensity gaussianPDFReal
  change Real.exp (-w^2/(2*sigma^2)) / (Real.sqrt (2*Real.pi)*sigma) =
    (Real.sqrt (2*Real.pi*sigma^2))⁻¹ * Real.exp (-(w-0)^2/(2*sigma^2))
  simp only [sub_zero]
  rw [show 2*Real.pi*sigma^2 = (2*Real.pi)*(sigma^2) by ring,
    Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi), Real.sqrt_sq hsigma.le]
  ring

/-- The positive-scale centered Gaussian density integrates to one. [Under the stated conditions](hyp:hsigma). [This is the stated conclusion](goal). -/
-- @node: phiDensity_integral
lemma phiDensity_integral (sigma : ℝ) (hsigma : 0 < sigma) :
    (∫ w, phiDensity sigma w) = 1 := by
  simp_rw [phiDensity_eq_gaussianPDFReal sigma _ hsigma]
  exact integral_gaussianPDFReal_eq_one 0 (by
    intro h
    have hreal := congrArg (fun z : ℝ≥0 => (z : ℝ)) h
    change sigma^2 = 0 at hreal
    exact (ne_of_gt (sq_pos_of_pos hsigma)) hreal)

/-- The Gaussian kernel quotient integrates to the exponential interaction kernel. [Under the stated conditions](hyp:hsigma). [This is the stated conclusion](goal). -/
-- @node: phiDensity_product_integral
lemma phiDensity_product_integral (sigma t s : ℝ) (hsigma : 0 < sigma) :
    (∫ w, phiDensity sigma (w-t) * phiDensity sigma (w-s) / phiDensity sigma w) =
      Real.exp (t*s/sigma^2) := by
  simp_rw [phiDensity_product_div sigma _ t s hsigma]
  rw [integral_const_mul]
  have hshift : (fun w => phiDensity sigma (w-t-s)) =
      (fun w => phiDensity sigma (w-(t+s))) := by
    funext w
    congr 1
    ring
  rw [hshift, integral_sub_right_eq_self, phiDensity_integral sigma hsigma, mul_one]

end CausalSmith.Stat.NoisydoseWeakdesignTransition

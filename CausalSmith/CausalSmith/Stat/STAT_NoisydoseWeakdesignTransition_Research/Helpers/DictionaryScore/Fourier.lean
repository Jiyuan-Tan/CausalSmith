module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.Estimator
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! Helpers — DictionaryScore — Fourier -/
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


/-- The declared continuous extension agrees with Mathlib's sinc sixth power. [This is the stated conclusion](goal). -/
-- @node: sincSix_eq_sinc_pow
lemma sincSix_eq_sinc_pow (u : ℝ) : sincSix u = Real.sinc u ^ 6 := by
  by_cases hu : u = 0 <;> simp [sincSix, Real.sinc, hu]

/-- Fourier latent weights are continuous at the target as well as away from it. [This is the stated conclusion](goal). -/
-- @node: qF_continuous
@[fun_prop] lemma qF_continuous (h : ℝ) : Continuous (qF h) := by
  have heq : qF h = fun t => Real.sinc (t/h)^6 := by
    funext t
    exact sincSix_eq_sinc_pow (t/h)
  rw [heq]
  fun_prop

/-- The sixth power gives a nonnegative latent weight on the entire line. [Under the stated conditions](hyp:h). [This is the stated conclusion](goal). -/
-- @node: qF_nonneg
lemma qF_nonneg (h t : ℝ) : 0 ≤ qF h t := by
  rw [qF, sincSix_eq_sinc_pow]
  positivity

/-- Sinc's unit bound bounds every latent Fourier weight by one. [Under the stated conditions](hyp:h). [This is the stated conclusion](goal). -/
-- @node: qF_le_one
lemma qF_le_one (h t : ℝ) : qF h t ≤ 1 := by
  rw [qF, sincSix_eq_sinc_pow]
  have habs : |Real.sinc (t/h)| ^ 6 = Real.sinc (t/h) ^ 6 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, sq_abs, ← pow_mul]
  rw [← habs]
  exact (pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sinc_le_one _ ) 6).trans_eq (by norm_num)

/-- Away from zero, the sine unit bound gives the sixth-order localization tail. [Under the stated conditions](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: sincSix_tail_bound
lemma sincSix_tail_bound (u : ℝ) (hu : u ≠ 0) :
    sincSix u ≤ (1 / |u|)^6 := by
  rw [sincSix_eq_sinc_pow, Real.sinc_of_ne_zero hu]
  have habs : |Real.sin u / u|^6 = (Real.sin u / u)^6 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, sq_abs, ← pow_mul]
  rw [← habs, abs_div]
  exact pow_le_pow_left₀ (div_nonneg (abs_nonneg _) (abs_nonneg _))
    (div_le_div_of_nonneg_right (Real.abs_sin_le_one u) (abs_nonneg u)) 6

/-- The localization weight is even about the causal target. [Under the stated conditions](hyp:h). [This is the stated conclusion](goal). -/
-- @node: qF_even
lemma qF_even (h t : ℝ) : qF h (-t) = qF h t := by
  simp only [qF, neg_div, sincSix_eq_sinc_pow, Real.sinc_neg]

/-- Nonnegative design exponents give continuous weighted Fourier moments. [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: qF_weighted_continuous
@[fun_prop] lemma qF_weighted_continuous (kappa : ℝ) (hkappa : 0 ≤ kappa) (h : ℝ) :
    Continuous (fun t => |t| ^ kappa * qF h t) := by
  exact (continuous_abs.rpow_const (fun _ => Or.inr hkappa)).mul (qF_continuous h)

/-- Each weighted latent moment is finite on the compact dose support. [Under the stated conditions](hyp:hkappa,h). [This is the stated conclusion](goal). -/
-- @node: qF_weighted_integrable
lemma qF_weighted_integrable (kappa : ℝ) (hkappa : 0 ≤ kappa) (h : ℝ) :
    Integrable (fun t => |t| ^ kappa * qF h t)
      (volume.restrict (Icc (-1/2 : ℝ) (1/2))) := by
  exact (qF_weighted_continuous kappa hkappa h).integrableOn_Icc

/-- The continuous weight equals one at zero and stays positive nearby. [Under the stated conditions](hyp:h). [This is the stated conclusion](goal). -/
-- @node: qF_positive_near_zero
lemma qF_positive_near_zero (h : ℝ) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t, |t| < delta → 0 < qF h t := by
  have hzero : qF h 0 = 1 := by simp [qF, sincSix]
  have hn : ∀ᶠ t in nhds (0 : ℝ), 0 < qF h t :=
    (qF_continuous h).continuousAt.eventually
      (lt_mem_nhds (show (0 : ℝ) < qF h 0 by rw [hzero]; norm_num))
  obtain ⟨delta, hdelta, hball⟩ := Metric.eventually_nhds_iff.mp hn
  refine ⟨delta, hdelta, ?_⟩
  intro t ht
  exact hball (by simpa [Real.dist_eq] using ht)

/-- Positive mass near the target gives a strictly positive public denominator. [Under the stated conditions](hyp:hkappa,h). [This is the stated conclusion](goal). -/
-- @node: qF_weightMoment_pos
lemma qF_weightMoment_pos (kappa : ℝ) (hkappa : 0 ≤ kappa) (h : ℝ) :
    0 < weightMoment kappa (qF h) := by
  obtain ⟨delta, hdelta, hpos⟩ := qF_positive_near_zero h
  let t : ℝ := min delta 1 / 4
  have htpos : 0 < t := by dsimp [t]; positivity
  have htdelta : |t| < delta := by
    rw [abs_of_pos htpos]
    dsimp [t]
    have := min_le_left delta 1
    linarith
  have htupper : t ≤ 1/2 := by
    dsimp [t]
    have := min_le_right delta 1
    linarith
  have hint : 0 < ∫ t in (-1/2 : ℝ)..(1/2), |t| ^ kappa * qF h t := by
    apply intervalIntegral.integral_pos (by norm_num)
      (qF_weighted_continuous kappa hkappa h).continuousOn
    · intro x hx
      exact mul_nonneg (Real.rpow_nonneg (abs_nonneg x) _) (qF_nonneg h x)
    · exact ⟨t, ⟨by linarith, htupper⟩,
        mul_pos (Real.rpow_pos_of_pos (abs_pos.mpr (ne_of_gt htpos)) _) (hpos t htdelta)⟩
  simpa only [weightMoment, intervalIntegral.integral_of_le (by norm_num : (-1/2 : ℝ) ≤ 1/2),
    integral_Icc_eq_integral_Ioc] using hint

/-- The sixth-order sinc tail dominates every design moment needed in S1 by an integrable cubic tail. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hs). -/
-- @node: qF_unit_weighted_tail_bound
lemma qF_unit_weighted_tail_bound (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 3) (t : ℝ) :
    |t| ^ s * qF 1 t ≤ 8 / (1 + |t|)^3 := by
  have ha : 0 ≤ |t| := abs_nonneg t
  have hp : 0 < 1 + |t| := by positivity
  by_cases ht : |t| ≤ 1
  · have hw := Real.rpow_le_one ha ht hs.1
    have hq := qF_le_one 1 t
    have hprod : |t| ^ s * qF 1 t ≤ 1 := by
      nlinarith [Real.rpow_nonneg ha s, qF_nonneg 1 t]
    apply hprod.trans
    apply (le_div_iff₀ (pow_pos hp 3)).mpr
    have := pow_le_pow_left₀ hp.le (show 1 + |t| ≤ 2 by linarith) 3
    norm_num at this ⊢
    exact this
  · have ht1 : 1 ≤ |t| := (lt_of_not_ge ht).le
    have htpos : 0 < |t| := by linarith
    have hw : |t| ^ s ≤ |t| ^ (3 : ℕ) := by
      simpa using
        Real.rpow_le_rpow_of_exponent_le ht1 hs.2
    have hq : qF 1 t ≤ (1 / |t|)^6 := by
      simpa only [qF, div_one] using sincSix_tail_bound t (abs_pos.mp htpos)
    calc
      |t| ^ s * qF 1 t ≤ |t|^3 * (1 / |t|)^6 :=
        mul_le_mul hw hq (qF_nonneg 1 t) (by positivity)
      _ = 1 / |t|^3 := by field_simp
      _ ≤ 8 / (1 + |t|)^3 := by
        apply (div_le_div_iff₀ (pow_pos htpos 3) (pow_pos hp 3)).mpr
        have hh := pow_le_pow_left₀ hp.le (show 1 + |t| ≤ 2*|t| by linarith) 3
        nlinarith [hh]

/-- The unscaled Fourier kernel has finite whole-line moments for all exponents used in S1. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hs). -/
-- @node: qF_unit_weighted_integrable
lemma qF_unit_weighted_integrable (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 3) :
    Integrable (fun t => |t| ^ s * qF 1 t) := by
  have hi : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm (by norm_num)
  have hd : Integrable (fun t : ℝ => 8 / (1 + |t|)^3) := by
    simpa [Real.norm_eq_abs, Real.rpow_neg, div_eq_mul_inv]
      using hi.const_mul 8
  have hs0 : 0 ≤ s := hs.1
  apply hd.mono' (by fun_prop)
  apply Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (qF_nonneg 1 t))]
  exact qF_unit_weighted_tail_bound s hs t

/-- Scaling a Fourier weight scales its weighted integrand by the bandwidth power. [Under the stated conditions](hyp:h,hh). [This is the stated conclusion](goal). -/
-- @node: qF_weighted_scaling
lemma qF_weighted_scaling (s h t : ℝ) (hh : 0 < h) :
    |t| ^ s * qF h t = h ^ s * (|t/h| ^ s * qF 1 (t/h)) := by
  have habs : |t| = h * |t/h| := by
    rw [abs_div, abs_of_pos hh]
    field_simp
  rw [habs, Real.mul_rpow hh.le (abs_nonneg _)]
  simp only [qF, div_one, mul_assoc]

/-- The exact whole-line change of variables gives the upper moment's bandwidth exponent in S1. [Under the stated conditions](hyp:h,hh). [This is the stated conclusion](goal). -/
-- @node: qF_whole_moment_scaling
lemma qF_whole_moment_scaling (s h : ℝ) (hh : 0 < h) :
    (∫ t : ℝ, |t| ^ s * qF h t) =
      h ^ (s+1) * (∫ u : ℝ, |u| ^ s * qF 1 u) := by
  simp_rw [qF_weighted_scaling s h _ hh]
  rw [integral_const_mul]
  have hc := Measure.integral_comp_mul_left (fun u : ℝ => |u| ^ s * qF 1 u) h⁻¹
  simp only [inv_inv, abs_of_pos hh, smul_eq_mul, ← div_eq_inv_mul] at hc
  rw [hc, Real.rpow_add hh, Real.rpow_one]
  ring

/-- The weighted Fourier kernel is integrable on the entire line at every positive bandwidth. [Under the stated conditions](hyp:h,hh,hs). [This is the stated conclusion](goal). -/
-- @node: qF_whole_weighted_integrable
lemma qF_whole_weighted_integrable (s h : ℝ) (hs : s ∈ Icc (0 : ℝ) 3) (hh : 0 < h) :
    Integrable (fun t => |t| ^ s * qF h t) := by
  have hi := (integrable_comp_mul_left_iff
    (fun u : ℝ => |u| ^ s * qF 1 u) (inv_ne_zero hh.ne')).mpr
      (qF_unit_weighted_integrable s hs)
  convert hi.const_mul (h ^ s) using 1
  funext t
  simpa only [← div_eq_inv_mul] using qF_weighted_scaling s h t hh

/-- Restricting a nonnegative whole-line moment gives the S1 upper bound with a fixed constant. [Under the stated conditions](hyp:h,hh,hs). [This is the stated conclusion](goal). -/
-- @node: qF_weightMoment_upper
lemma qF_weightMoment_upper (s h : ℝ) (hs : s ∈ Icc (0 : ℝ) 3) (hh : 0 < h) :
    weightMoment s (qF h) ≤ h ^ (s+1) * (∫ u : ℝ, |u| ^ s * qF 1 u) := by
  rw [← qF_whole_moment_scaling s h hh]
  exact integral_mono_measure Measure.restrict_le_self
    (Eventually.of_forall (fun t =>
      mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (qF_nonneg h t)))
    (qF_whole_weighted_integrable s h hs hh)

/-- Changing variables on the latent dose interval gives the exact truncated S1 moment. [Under the stated conditions](hyp:h,hh). [This is the stated conclusion](goal). -/
-- @node: qF_weightMoment_scaling
lemma qF_weightMoment_scaling (s h : ℝ) (hh : 0 < h) :
    weightMoment s (qF h) = h ^ (s+1) *
      (∫ u in Icc ((-1/2 : ℝ)/h) ((1/2 : ℝ)/h), |u| ^ s * qF 1 u) := by
  have hab : (-1/2 : ℝ) ≤ 1/2 := by norm_num
  have habh : (-1/2 : ℝ)/h ≤ (1/2 : ℝ)/h := div_le_div_of_nonneg_right hab hh.le
  rw [weightMoment, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]
  simp_rw [qF_weighted_scaling s h _ hh]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div (fun u : ℝ => |u| ^ s * qF 1 u) hh.ne', smul_eq_mul,
    intervalIntegral.integral_of_le habh, ← integral_Icc_eq_integral_Ioc,
    Real.rpow_add hh, Real.rpow_one]
  ring

/-- The fixed positive central moment supplies a bandwidth-independent lower constant in S1. [Under the stated conditions](hyp:h,hs,hh). [This is the stated conclusion](goal). -/
-- @node: qF_weightMoment_lower
lemma qF_weightMoment_lower (s h : ℝ) (hs : s ∈ Icc (0 : ℝ) 3)
    (hh : h ∈ Ioc (0 : ℝ) 1) :
    h ^ (s+1) * weightMoment s (qF 1) ≤ weightMoment s (qF h) := by
  rw [qF_weightMoment_scaling s h hh.1]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hh.1.le _)
  apply setIntegral_mono_set (qF_unit_weighted_integrable s hs).integrableOn
    (Eventually.of_forall (fun t =>
      mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (qF_nonneg 1 t)))
  apply Eventually.of_forall
  intro t ht
  constructor
  · apply (div_le_iff₀ hh.1).mpr
    nlinarith [mul_le_mul_of_nonneg_right ht.1 hh.1.le, hh.2]
  · apply (le_div_iff₀ hh.1).mpr
    nlinarith [mul_le_mul_of_nonneg_right ht.2 hh.1.le, hh.2]

/-- Both constants in the Fourier localization moment comparison are positive and independent of bandwidth. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hs). -/
-- @node: qF_weightMoment_bounds
lemma qF_weightMoment_bounds (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 3) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ h ∈ Ioc (0 : ℝ) (1/4),
      c * h ^ (s+1) ≤ weightMoment s (qF h) ∧
      weightMoment s (qF h) ≤ C * h ^ (s+1) := by
  let c := weightMoment s (qF 1)
  let C := ∫ u : ℝ, |u| ^ s * qF 1 u
  have hc : 0 < c := qF_weightMoment_pos s hs.1 1
  have hC : 0 < C := hc.trans_le (by
    simpa [c, C] using qF_weightMoment_upper s 1 hs (by norm_num))
  refine ⟨c, C, hc, hC, ?_⟩
  intro h hh
  constructor
  · simpa [c, mul_comm] using qF_weightMoment_lower s h hs ⟨hh.1, by linarith [hh.2]⟩
  · simpa [C, mul_comm] using qF_weightMoment_upper s h hs hh.1

/-- The numerator and denominator moment comparisons assemble the S1 public bias bound. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hbeta,hkappa). -/
-- @node: qF_bias_bound
lemma qF_bias_bound (beta kappa : ℝ) (hbeta : beta ∈ Ioc (0 : ℝ) 1)
    (hkappa : kappa ∈ Icc (0 : ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ h ∈ Ioc (0 : ℝ) (1/4),
      unitBq beta kappa (qF h) ≤ C * h ^ beta := by
  have hs : kappa + beta ∈ Icc (0 : ℝ) 3 := by
    constructor <;> linarith [hkappa.1, hkappa.2, hbeta.1, hbeta.2]
  let c := weightMoment kappa (qF 1)
  let K := ∫ u : ℝ, |u| ^ (kappa+beta) * qF 1 u
  have hc : 0 < c := qF_weightMoment_pos kappa hkappa.1 1
  have hK : 0 < K := (qF_weightMoment_pos (kappa+beta) hs.1 1).trans_le (by
    simpa [K] using qF_weightMoment_upper (kappa+beta) 1 hs (by norm_num))
  refine ⟨64*K/c, by positivity, ?_⟩
  intro h hh
  have hlo := qF_weightMoment_lower kappa h
    ⟨hkappa.1, by linarith [hkappa.2]⟩ ⟨hh.1, by linarith [hh.2]⟩
  have hhi := qF_weightMoment_upper (kappa+beta) h hs hh.1
  have hpow : 0 < h ^ (kappa+1) := Real.rpow_pos_of_pos hh.1 _
  have hden : 0 < h ^ (kappa+1) * c := mul_pos hpow hc
  calc
    unitBq beta kappa (qF h) = 64 * weightMoment (kappa+beta) (qF h) /
      weightMoment kappa (qF h) := rfl
    _ ≤ (64 * (h ^ (kappa+beta+1) * K)) / (h ^ (kappa+1) * c) := by
      exact div_le_div₀ (mul_nonneg (by norm_num)
        (mul_nonneg (Real.rpow_nonneg hh.1.le _) hK.le))
        (mul_le_mul_of_nonneg_left hhi (by norm_num)) hden hlo
    _ = (64*K/c) * h ^ beta := by
      rw [show kappa+beta+1 = beta+(kappa+1) by ring, Real.rpow_add hh.1]
      field_simp [hpow.ne']

/-- The inverse Fourier integral is continuous in the observed dose. [This is the stated conclusion](goal). -/
-- @node: ellF_continuous
@[fun_prop] lemma ellF_continuous (sigma h : ℝ) : Continuous (ellF sigma h) := by
  unfold ellF
  exact Complex.continuous_re.comp
    ((realFourierIntegral_continuous (fun xi : ℝ =>
      Fourier.fourierIntegral Real.fourierChar volume (fun t : ℝ => (qF h t : ℂ)) xi *
        (Real.exp (sigma^2 * (2*Real.pi*xi)^2 / 2) : ℂ))).comp continuous_neg)

/-- The inverse Fourier integral has a finite uniform bound given by its multiplier norm. [Under the stated conditions](hyp:h). [This is the stated conclusion](goal). -/
-- @node: ellF_uniform_bound
lemma ellF_uniform_bound (sigma h : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v, |ellF sigma h v| ≤ C := by
  let F : ℝ → ℂ := fun xi =>
    Fourier.fourierIntegral Real.fourierChar volume (fun t : ℝ => (qF h t : ℂ)) xi *
      (Real.exp (sigma^2 * (2*Real.pi*xi)^2 / 2) : ℂ)
  refine ⟨∫ xi, ‖F xi‖, integral_nonneg (fun _ => norm_nonneg _), ?_⟩
  intro v
  exact (Complex.abs_re_le_norm _).trans
    (Fourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume F (-v))

/-- A bounded observable Fourier weight is integrable under each shifted Gaussian channel. [Under the stated conditions](hyp:h). [This is the stated conclusion](goal). -/
-- @node: ellF_gaussian_integrable
lemma ellF_gaussian_integrable (sigma h t : ℝ) :
    Integrable (fun z => ellF sigma h (t+sigma*z)) (gaussianReal 0 1) := by
  obtain ⟨C, hC, hbound⟩ := ellF_uniform_bound sigma h
  apply (integrable_const C).mono' (by fun_prop)
  exact Eventually.of_forall (fun z => by
    simpa only [Real.norm_eq_abs] using hbound (t+sigma*z))

/-- Squaring preserves the uniform inverse-weight bound. [Under the stated conditions](hyp:h). [This is the stated conclusion](goal). -/
-- @node: ellF_square_bound
lemma ellF_square_bound (sigma h : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v, (ellF sigma h v)^2 ≤ C := by
  obtain ⟨C, hC, hbound⟩ := ellF_uniform_bound sigma h
  refine ⟨C^2, sq_nonneg _, ?_⟩
  intro v
  have hb := pow_le_pow_left₀ (abs_nonneg (ellF sigma h v)) (hbound v) 2
  simpa only [sq_abs] using hb

/-- Compact dose support and a bounded inverse weight give finite weighted joint second moments. [Under the stated conditions](hyp:h,hkappa). [This is the stated conclusion](goal). -/
-- @node: ellF_weighted_sq_integrable
lemma ellF_weighted_sq_integrable (kappa sigma h : ℝ) (hkappa : 0 ≤ kappa) :
    Integrable (fun x : ℝ × ℝ => |x.1| ^ kappa * (ellF sigma h (x.1+sigma*x.2))^2)
      ((volume.restrict (Icc (-1/2 : ℝ) (1/2))).prod (gaussianReal 0 1)) := by
  obtain ⟨C, hC, hbound⟩ := ellF_square_bound sigma h
  have ht : Integrable (fun t : ℝ => |t| ^ kappa)
      (volume.restrict (Icc (-1/2 : ℝ) (1/2))) :=
    (continuous_abs.rpow_const (fun _ => Or.inr hkappa)).integrableOn_Icc
  have hdom := ht.mul_prod (integrable_const C (μ := gaussianReal 0 1))
  apply hdom.mono' (by fun_prop)
  apply Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_left (hbound _) (Real.rpow_nonneg (abs_nonneg _) _)

/-- The extended Fourier second moment is finite for every nonnegative design exponent. [Under the stated conditions](hyp:h,hkappa). [This is the stated conclusion](goal). -/
-- @node: ellF_VqENN_lt_top
lemma ellF_VqENN_lt_top (kappa sigma h : ℝ) (hkappa : 0 ≤ kappa) :
    VqENN kappa sigma (ellF sigma h) < ⊤ := by
  have hi := ellF_weighted_sq_integrable kappa sigma h hkappa
  have hn : ∀ x : ℝ × ℝ, 0 ≤ |x.1| ^ kappa * (ellF sigma h (x.1+sigma*x.2))^2 :=
    fun x => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _)
  have hf := (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hn)).mp hi.hasFiniteIntegral
  rw [lintegral_prod _ (by fun_prop)] at hf
  simp_rw [ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _)] at hf
  have hm : ∀ t : ℝ, Measurable (fun z => ENNReal.ofReal ((ellF sigma h (t+sigma*z))^2)) := by
    intro t
    fun_prop
  simp_rw [lintegral_const_mul _ (hm _)] at hf
  exact ENNReal.mul_lt_top (by norm_num : (16 : ℝ≥0∞) < ⊤) hf


end CausalSmith.Stat.NoisydoseWeakdesignTransition

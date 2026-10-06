module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.GaussianConvolution
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Absolute Fubini and exponential-series integration for compact signed densities. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- A translated positive-scale Gaussian density is integrable. [Under the stated conditions](hyp:hsigma). [This is the stated conclusion](goal). -/
-- @node: phiDensity_shift_integrable
@[fun_prop] lemma phiDensity_shift_integrable (sigma c : ℝ) (hsigma : 0 < sigma) :
    Integrable (fun w => phiDensity sigma (w-c)) := by
  have hi : Integrable (phiDensity sigma) := by
    have he : phiDensity sigma = gaussianPDFReal 0 ⟨sigma^2, sq_nonneg sigma⟩ :=
      funext (fun w => phiDensity_eq_gaussianPDFReal sigma w hsigma)
    rw [he]
    exact
      (integrable_gaussianPDFReal 0 ⟨sigma^2, sq_nonneg sigma⟩)
  exact hi.comp_sub_right c

/-- The interaction exponential is bounded on the support square. [Under the stated conditions](hyp:hsigma,ht,hs). [This is the stated conclusion](goal). -/
-- @node: compact_exponential_bound
lemma compact_exponential_bound (sigma ell t s : ℝ) (hsigma : 0 < sigma)
    (ht : t ∈ Icc (-ell) ell) (hs : s ∈ Icc (-ell) ell) :
    Real.exp (t*s/sigma^2) ≤ Real.exp (ell^2/sigma^2) := by
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (sq_nonneg sigma)
  calc
    t*s ≤ |t*s| := le_abs_self _
    _ = |t| * |s| := abs_mul _ _
    _ ≤ ell*ell := mul_le_mul (abs_le.mpr ht) (abs_le.mpr hs) (abs_nonneg _) (by linarith [ht.1, ht.2])
    _ = ell^2 := by ring

/-- Absolute mass controls the compact exponential interaction. [Under the stated conditions](hyp:hsigma,hv,hsupp). [This is the stated conclusion](goal). -/
-- @node: compact_exponential_integrable
lemma compact_exponential_integrable (sigma ell : ℝ) (hsigma : 0 < sigma)
    (v : ℝ → ℝ) (hv : Integrable v)
    (hsupp : ∀ t, t ∉ Icc (-ell) ell → v t = 0) :
    Integrable (fun p : ℝ × ℝ => v p.1*v p.2*Real.exp (p.1*p.2/sigma^2))
      (volume.prod volume) := by
  have hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => v p.1*v p.2*Real.exp (p.1*p.2/sigma^2)) (volume.prod volume) :=
    (hv.mul_prod hv).aestronglyMeasurable.mul (by fun_prop)
  apply ((hv.norm.mul_prod hv.norm).mul_const (Real.exp (ell^2/sigma^2))).mono' hm
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  by_cases ht : p.1 ∈ Icc (-ell) ell
  · by_cases hs : p.2 ∈ Icc (-ell) ell
    · exact mul_le_mul_of_nonneg_left (compact_exponential_bound sigma ell _ _ hsigma ht hs)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    · simp [hsupp _ hs]
  · simp [hsupp _ ht]

/-- Absolute Fubini converts the squared Gaussian convolution into exponential energy. [Under the stated conditions](hyp:hsigma,hv,hsupp). [This is the stated conclusion](goal). -/
-- @node: gaussian_convolution_energy
lemma gaussian_convolution_energy (sigma ell : ℝ) (hsigma : 0 < sigma)
    (v : ℝ → ℝ) (hv : Integrable v)
    (hsupp : ∀ t, t ∉ Icc (-ell) ell → v t = 0) :
    (∫ w, (smoothSigned sigma v w)^2 / phiDensity sigma w) =
      ∫ p : ℝ × ℝ, v p.1*v p.2*Real.exp (p.1*p.2/sigma^2) ∂(volume.prod volume) := by
  let K := fun (p : ℝ × ℝ) (w : ℝ) =>
    v p.1*v p.2*Real.exp (p.1*p.2/sigma^2)*phiDensity sigma (w-(p.1+p.2))
  have hKi (p : ℝ × ℝ) : Integrable (K p) :=
    (phiDensity_shift_integrable sigma (p.1+p.2) hsigma).const_mul _
  have hg : AEStronglyMeasurable
      (fun q : (ℝ × ℝ) × ℝ =>
        Real.exp (q.1.1*q.1.2/sigma^2)*phiDensity sigma (q.2-(q.1.1+q.1.2)))
      ((volume.prod volume).prod volume) := by
    unfold phiDensity
    fun_prop
  have hKm : AEStronglyMeasurable (Function.uncurry K) ((volume.prod volume).prod volume) := by
    have hh := (hv.mul_prod hv).aestronglyMeasurable.comp_fst.mul hg
    change AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ =>
      (v q.1.1*v q.1.2)*(Real.exp (q.1.1*q.1.2/sigma^2)*
        phiDensity sigma (q.2-(q.1.1+q.1.2)))) _ at hh
    simpa only [K, Function.uncurry_def, mul_assoc] using hh
  have hKn (p : ℝ × ℝ) : (∫ w, ‖K p w‖) =
      ‖v p.1*v p.2*Real.exp (p.1*p.2/sigma^2)‖ := by
    simp only [K, norm_mul, Real.norm_eq_abs, abs_of_pos (phiDensity_pos sigma _ hsigma)]
    rw [integral_const_mul, integral_sub_right_eq_self, phiDensity_integral sigma hsigma, mul_one]
  have hK : Integrable (Function.uncurry K) ((volume.prod volume).prod volume) := by
    apply (integrable_prod_iff hKm).mpr
    refine ⟨ae_of_all _ hKi, ?_⟩
    simpa only [Function.uncurry, hKn] using (compact_exponential_integrable sigma ell hsigma v hv hsupp).norm
  have hpoint (w : ℝ) : (∫ p : ℝ × ℝ, K p w ∂(volume.prod volume)) =
      (smoothSigned sigma v w)^2 / phiDensity sigma w := by
    calc
      _ = ∫ p : ℝ × ℝ,
          (v p.1*phiDensity sigma (w-p.1))*(v p.2*phiDensity sigma (w-p.2)) /
            phiDensity sigma w ∂(volume.prod volume) := by
        apply integral_congr_ae
        filter_upwards with p
        dsimp [K]
        rw [mul_assoc (v p.1*v p.2), show w-(p.1+p.2) = w-p.1-p.2 by ring,
          ← phiDensity_product_div sigma w p.1 p.2 hsigma]
        ring
      _ = _ := by
        rw [integral_div, integral_prod_mul (fun t => v t*phiDensity sigma (w-t))
          (fun t => v t*phiDensity sigma (w-t))]
        simp only [smoothSigned, pow_two]
  calc
    _ = ∫ w, ∫ p : ℝ × ℝ, K p w ∂(volume.prod volume) := by simp_rw [hpoint]
    _ = ∫ p : ℝ × ℝ, (∫ w : ℝ, K p w) ∂(volume.prod volume) :=
      (integral_integral_swap hK).symm
    _ = _ := by
      simp only [K, integral_const_mul, integral_sub_right_eq_self,
        phiDensity_integral sigma hsigma, mul_one]

/-- Compact signed moments justify termwise integration of the exponential interaction. [Under the stated conditions](hyp:hsigma,hell,hv,hsupp). [This is the stated conclusion](goal). -/
-- @node: compact_exponential_energy_series
lemma compact_exponential_energy_series (sigma ell : ℝ) (hsigma : 0 < sigma)
    (hell : 0 ≤ ell) (v : ℝ → ℝ) (hv : Integrable v)
    (hsupp : ∀ t, t ∉ Icc (-ell) ell → v t = 0) :
    (∫ p : ℝ × ℝ, v p.1*v p.2*Real.exp (p.1*p.2/sigma^2) ∂(volume.prod volume)) =
      ∑' j : ℕ, (∫ t, t^j*v t)^2 / (sigma^(2*j)*(j.factorial : ℝ)) := by
  let F := fun (j : ℕ) (p : ℝ × ℝ) =>
    (p.1^j*v p.1)*(p.2^j*v p.2)/(sigma^(2*j)*(j.factorial : ℝ))
  have hFi (j : ℕ) : Integrable (F j) (volume.prod volume) :=
    ((compact_signed_moment_integrable ell hell v hv hsupp j).mul_prod
      (compact_signed_moment_integrable ell hell v hv hsupp j)).div_const _
  have hFbound (j : ℕ) : (∫ p : ℝ × ℝ, ‖F j p‖ ∂(volume.prod volume)) ≤
      (∫ t, |v t|)^2*((ell^2/sigma^2)^j/(j.factorial : ℝ)) := by
    have hp (p : ℝ × ℝ) : ‖F j p‖ ≤
        (ell^2/sigma^2)^j/(j.factorial : ℝ)*(|v p.1| * |v p.2|) := by
      dsimp [F]
      rw [abs_div, abs_mul, abs_mul, abs_mul, abs_pow, abs_pow,
        abs_of_pos (by positivity : 0 < sigma^(2*j)*(j.factorial : ℝ))]
      by_cases ht : p.1 ∈ Icc (-ell) ell
      · by_cases hs : p.2 ∈ Icc (-ell) ell
        · calc
            _ ≤ (ell^j*|v p.1|)*(ell^j*|v p.2|)/(sigma^(2*j)*(j.factorial : ℝ)) := by
              gcongr
              · exact abs_le.mpr ht
              · exact abs_le.mpr hs
            _ = _ := by rw [div_pow]; ring
        · simp [hsupp _ hs]
      · simp [hsupp _ ht]
    calc
      _ ≤ ∫ p : ℝ × ℝ,
          (ell^2/sigma^2)^j/(j.factorial : ℝ)*(|v p.1| * |v p.2|) ∂(volume.prod volume) :=
        integral_mono_ae (hFi j).norm ((hv.norm.mul_prod hv.norm).const_mul _)
          (ae_of_all _ hp)
      _ = _ := by
        rw [integral_const_mul, integral_prod_mul (fun t => |v t|) (fun t => |v t|)]
        ring
  have hFs : Summable (fun j : ℕ => ∫ p : ℝ × ℝ, ‖F j p‖ ∂(volume.prod volume)) :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg (fun _ => norm_nonneg _)) hFbound
      ((Real.summable_pow_div_factorial (ell^2/sigma^2)).mul_left ((∫ t, |v t|)^2))
  have hFsum (p : ℝ × ℝ) : (∑' j : ℕ, F j p) =
      v p.1*v p.2*Real.exp (p.1*p.2/sigma^2) := by
    have he : (∑' j : ℕ, (p.1*p.2/sigma^2)^j/(j.factorial : ℝ)) =
        Real.exp (p.1*p.2/sigma^2) := by
      rw [Real.exp_eq_exp_ℝ]
      exact (NormedSpace.expSeries_div_hasSum_exp _).tsum_eq
    calc
      _ = ∑' j : ℕ, (p.1*p.2/sigma^2)^j/(j.factorial : ℝ)*(v p.1*v p.2) := by
        apply tsum_congr
        intro j
        dsimp [F]
        rw [div_pow, mul_pow, pow_mul]
        ring
      _ = _ := by rw [tsum_mul_right, he]; ring
  have hFint (j : ℕ) : (∫ p : ℝ × ℝ, F j p ∂(volume.prod volume)) =
      (∫ t, t^j*v t)^2/(sigma^(2*j)*(j.factorial : ℝ)) := by
    dsimp [F]
    rw [integral_div, integral_prod_mul (fun t => t^j*v t) (fun t => t^j*v t), pow_two]
  calc
    _ = ∫ p : ℝ × ℝ, ∑' j : ℕ, F j p ∂(volume.prod volume) := by simp_rw [hFsum]
    _ = ∑' j : ℕ, ∫ p : ℝ × ℝ, F j p ∂(volume.prod volume) :=
      (integral_tsum_of_summable_integral_norm hFi hFs).symm
    _ = _ := by simp_rw [hFint]

/-- Vanishing low-order moments remove exactly the initial terms of the Gaussian energy series. [Under the stated conditions](hyp:hsigma,hell,hv,hmom,hsupp). [This is the stated conclusion](goal). -/
-- @node: gaussian_compact_energy_tail_identity
lemma gaussian_compact_energy_tail_identity (sigma ell : ℝ) (hsigma : 0 < sigma)
    (hell : 0 ≤ ell) (J : ℕ) (v : ℝ → ℝ) (hv : Integrable v)
    (hsupp : ∀ t, t ∉ Icc (-ell) ell → v t = 0)
    (hmom : ∀ j < J, ∫ t, t^j*v t = 0) :
    (∫ w, (smoothSigned sigma v w)^2 / phiDensity sigma w) =
      (∑' j : ℕ, if J ≤ j then
        (∫ t, t^j*v t)^2 / (sigma^(2*j)*(j.factorial : ℝ)) else 0) := by
  rw [gaussian_convolution_energy sigma ell hsigma v hv hsupp,
    compact_exponential_energy_series sigma ell hsigma hell v hv hsupp]
  apply tsum_congr
  intro j
  by_cases hj : J ≤ j
  · rw [if_pos hj]
  · rw [if_neg hj, hmom j (lt_of_not_ge hj)]
    simp

/-- Absolute Fubini also supplies integrability of the Gaussian-weighted energy. [Under the stated conditions](hyp:hsigma,hv,hsupp). [This is the stated conclusion](goal). -/
-- @node: gaussian_convolution_energy_integrable
@[fun_prop] lemma gaussian_convolution_energy_integrable (sigma ell : ℝ) (hsigma : 0 < sigma)
    (v : ℝ → ℝ) (hv : Integrable v)
    (hsupp : ∀ t, t ∉ Icc (-ell) ell → v t = 0) :
    Integrable (fun w => (smoothSigned sigma v w)^2 / phiDensity sigma w) := by
  let K := fun (p : ℝ × ℝ) (w : ℝ) =>
    v p.1*v p.2*Real.exp (p.1*p.2/sigma^2)*phiDensity sigma (w-(p.1+p.2))
  have hKi (p : ℝ × ℝ) : Integrable (K p) :=
    (phiDensity_shift_integrable sigma (p.1+p.2) hsigma).const_mul _
  have hg : AEStronglyMeasurable
      (fun q : (ℝ × ℝ) × ℝ =>
        Real.exp (q.1.1*q.1.2/sigma^2)*phiDensity sigma (q.2-(q.1.1+q.1.2)))
      ((volume.prod volume).prod volume) := by
    unfold phiDensity
    fun_prop
  have hKm : AEStronglyMeasurable (Function.uncurry K) ((volume.prod volume).prod volume) := by
    have hh := (hv.mul_prod hv).aestronglyMeasurable.comp_fst.mul hg
    change AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ =>
      (v q.1.1*v q.1.2)*(Real.exp (q.1.1*q.1.2/sigma^2)*
        phiDensity sigma (q.2-(q.1.1+q.1.2)))) _ at hh
    simpa only [K, Function.uncurry_def, mul_assoc] using hh
  have hKn (p : ℝ × ℝ) : (∫ w, ‖K p w‖) =
      ‖v p.1*v p.2*Real.exp (p.1*p.2/sigma^2)‖ := by
    simp only [K, norm_mul, Real.norm_eq_abs, abs_of_pos (phiDensity_pos sigma _ hsigma)]
    rw [integral_const_mul, integral_sub_right_eq_self, phiDensity_integral sigma hsigma, mul_one]
  have hK : Integrable (Function.uncurry K) ((volume.prod volume).prod volume) := by
    apply (integrable_prod_iff hKm).mpr
    refine ⟨ae_of_all _ hKi, ?_⟩
    simpa only [Function.uncurry, hKn] using (compact_exponential_integrable sigma ell hsigma v hv hsupp).norm
  have hpoint (w : ℝ) : (∫ p : ℝ × ℝ, K p w ∂(volume.prod volume)) =
      (smoothSigned sigma v w)^2 / phiDensity sigma w := by
    calc
      _ = ∫ p : ℝ × ℝ,
          (v p.1*phiDensity sigma (w-p.1))*(v p.2*phiDensity sigma (w-p.2)) /
            phiDensity sigma w ∂(volume.prod volume) := by
        apply integral_congr_ae
        filter_upwards with p
        dsimp [K]
        rw [mul_assoc (v p.1*v p.2), show w-(p.1+p.2) = w-p.1-p.2 by ring,
          ← phiDensity_product_div sigma w p.1 p.2 hsigma]
        ring
      _ = _ := by
        rw [integral_div, integral_prod_mul (fun t => v t*phiDensity sigma (w-t))
          (fun t => v t*phiDensity sigma (w-t))]
        simp only [smoothSigned, pow_two]
  exact hK.integral_prod_right.congr (ae_of_all _ hpoint)

end CausalSmith.Stat.NoisydoseWeakdesignTransition

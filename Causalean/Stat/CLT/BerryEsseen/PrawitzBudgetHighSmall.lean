module
public import Causalean.Stat.CLT.BerryEsseen.GaussianWeightedTail
public import Causalean.Stat.CLT.BerryEsseen.PrawitzBudgetCutoffs
public import Causalean.Stat.CLT.BerryEsseen.PrawitzFarGaussianTail

/-! # High-frequency Prawitz allocation at small moment ratios

This assembly lemma splits at the reciprocal-ratio cutoff and applies the
two independently proved weighted Gaussian tails. The complementary ratio
interval and the unchanged full high-frequency budget are separate modules.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

private theorem weighted_tail_integrable (a b c : ℝ) (ha : 0 < a)
    (hb : 0 < b) (hc : 0 ≤ c) :
    IntegrableOn (fun t : ℝ => (1 / (Real.pi * t) + c) *
      Real.exp (-(b * t ^ 2))) (Set.Ioi a) := by
  have hg := ((integrable_exp_neg_mul_sq hb).const_mul
    (1 / (Real.pi * a) + c)).integrableOn (s := Set.Ioi a)
  refine hg.mono' ?_ ?_
  · have hm : Measurable (fun t : ℝ => (1 / (Real.pi * t) + c) *
        Real.exp (-(b * t ^ 2))) := by fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := ha.trans ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hw : 1 / (Real.pi * t) + c ≤ 1 / (Real.pi * a) + c := by
      gcongr
      exact ht.le
    simpa only [neg_mul] using mul_le_mul_of_nonneg_right hw
      (Real.exp_nonneg (-(b * t ^ 2)))

private theorem scaled_kernel_majorant (ρ U t b : ℝ)
    (hρ : 0 < ρ) (hU : U = 12 / (5 * ρ)) (ht : 0 < t) (htU : t ≤ U)
    (hd : -(t ^ 2 / 2) + ρ * t ^ 3 / 5 ≤ -(b * t ^ 2)) :
    (2 / U) * (‖prawitzKernel (t / U)‖ * prawitzMomentEnvelope ρ t) ≤
      (1 / (Real.pi * t) + 5 * ρ / 12) * Real.exp (-(b * t ^ 2)) := by
  have hUp : 0 < U := by rw [hU]; positivity
  have hx : 0 < t / U := div_pos ht hUp
  have hxb : t / U ≤ 1 := (div_le_one hUp).2 htU
  have hk := prawitzKernel_norm_le (t / U)
    (by simpa [abs_of_pos hx] using hx) (by simpa [abs_of_pos hx] using hxb)
  rw [abs_of_pos hx] at hk
  have hscale : (2 / U) * ‖prawitzKernel (t / U)‖ ≤
      1 / (Real.pi * t) + 5 * ρ / 12 := by
    have hm := mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ 2 / U)
    calc
      _ ≤ (2 / U) * (1 / (2 * Real.pi * (t / U)) + 1 / 2) := hm
      _ = _ := by rw [hU]; field_simp
  have he : prawitzMomentEnvelope ρ t ≤ Real.exp (-(b * t ^ 2)) := by
    exact (min_le_right _ _).trans (Real.exp_le_exp.mpr (by
      simpa [abs_of_pos ht] using hd))
  have hn : 0 ≤ prawitzMomentEnvelope ρ t := by
    unfold prawitzMomentEnvelope
    positivity
  simpa only [mul_assoc] using mul_le_mul hscale he hn (by positivity)

private theorem scaled_integral_comparison (ρ U a z b : ℝ)
    (hρ : 0 < ρ) (hU : U = 12 / (5 * ρ)) (ha : 0 < a) (haz : a ≤ z)
    (hzU : z ≤ U) (_hb : 0 < b)
    (hd : ∀ t ∈ Set.Icc a z,
      -(t ^ 2 / 2) + ρ * t ^ 3 / 5 ≤ -(b * t ^ 2)) :
    IntervalIntegrable (fun t => (2 / U) *
      (‖prawitzKernel (t / U)‖ * prawitzMomentEnvelope ρ t)) volume a z ∧
    (∫ t in a..z, (2 / U) *
      (‖prawitzKernel (t / U)‖ * prawitzMomentEnvelope ρ t)) ≤
    (∫ t in a..z, (1 / (Real.pi * t) + 5 * ρ / 12) *
      Real.exp (-(b * t ^ 2))) := by
  have hg : IntervalIntegrable (fun t : ℝ =>
      (1 / (Real.pi * t) + 5 * ρ / 12) * Real.exp (-(b * t ^ 2))) volume a z := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le haz]
    apply ContinuousOn.mul
    · apply ContinuousOn.add
      · exact continuousOn_const.div (continuous_const.mul continuous_id).continuousOn
          (fun t ht => ne_of_gt (mul_pos Real.pi_pos (ha.trans_le ht.1)))
      · exact continuousOn_const
    · fun_prop
  have hp := fun t (ht : t ∈ Set.Icc a z) =>
    scaled_kernel_majorant ρ U t b hρ hU (ha.trans_le ht.1)
      (ht.2.trans hzU) (hd t ht)
  have hm : Measurable (fun t => (2 / U) *
      (‖prawitzKernel (t / U)‖ * prawitzMomentEnvelope ρ t)) := by
    have hs : Measurable (fun t : ℝ => (t / U).sign) := by
      unfold Real.sign
      apply Measurable.ite
      · exact measurableSet_lt (by fun_prop) measurable_const
      · fun_prop
      · apply Measurable.ite
        · exact measurableSet_lt measurable_const (by fun_prop)
        · fun_prop
        · fun_prop
    have hk : Measurable (fun t : ℝ => prawitzKernel (t / U)) := by
      unfold prawitzKernel
      apply Measurable.ite
      · have hzero : MeasurableSet {t : ℝ | t / U = 0} :=
          measurableSet_eq_fun (by fun_prop) measurable_const
        have hband : MeasurableSet {t : ℝ | 1 < |t / U|} :=
          measurableSet_lt measurable_const (by fun_prop)
        exact hzero.union hband
      · fun_prop
      · fun_prop
    unfold prawitzMomentEnvelope
    fun_prop
  have hf : IntervalIntegrable (fun t => (2 / U) *
      (‖prawitzKernel (t / U)‖ * prawitzMomentEnvelope ρ t)) volume a z := by
    refine hg.mono_fun hm.aestronglyMeasurable ?_
    rw [Set.uIoc_of_le haz]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htpos : 0 < t := ha.trans ht.1
    have hUp : 0 < U := by rw [hU]; positivity
    have hen : 0 ≤ prawitzMomentEnvelope ρ t := by
      unfold prawitzMomentEnvelope
      positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact hp t ⟨ht.1.le, ht.2⟩
  exact ⟨hf, intervalIntegral.integral_mono_on haz hf hg hp⟩

/-- For [a positive moment ratio ρ at most one hundredth](hyp:ρ,hρ,hsmall), with
the logarithmic inner cutoff U0 = max(3/2, √(4 log(1/ρ))) and the reciprocal
outer cutoff U = 12/(5ρ), [the high-frequency Prawitz contribution
(2/U)·∫ over [U0, U] of the Prawitz filter magnitude times the moment
envelope is at most three twentieths of ρ](goal). -/
theorem prawitz_budget_high_small
    (ρ : ℝ) (hρ : 0 < ρ) (hsmall : ρ ≤ 1 / 100) :
    let U0 := max (3 / 2 : ℝ) (Real.sqrt (4 * Real.log (1 / ρ)))
    let U := 12 / (5 * ρ)
    (2 / U) * (∫ t in U0..U,
      ‖prawitzKernel (t / U)‖ * prawitzMomentEnvelope ρ t) ≤ 3 * ρ / 20 := by
  /- All imported analytic leaves are closed. Prove U0<=A<=U for
  A=1/(2*rho), using the same log bound as the low small case. On the
  middle interval rho*t<=1/2 implies damping <=exp(-2*t^2/5).
  On the far interval t<=U implies damping <=exp(-t^2/50).
  The scaled kernel bound in both cases is 1/(pi*t)+5*rho/12.
  Integrability here follows from measurability and continuous majorants
  away from zero. Split the interval integral at A.

  Bound the middle integral by gaussian_reciprocal_linear_tail_bound
  at a=U0, b=2/5, c=5*rho/12, using nonnegative integral restriction.
  Since U0^2>=4*log(1/rho), its exponential is <=rho*sqrt(rho)
  (weaken the exponent -8log(1/rho)/5 to -3log(1/rho)/2).
  Combine U0>=3/2, sqrt(rho)<=1/10, pi>3 to obtain a middle
  allocation <=rho/20. The independently proved far bound is <=rho/20.
  These bounds leave slack inside the required 3*rho/20 allocation.
  Prove every tail/interval integrability premise before comparison. This
  module must not import either full or complementary high budget theorem. -/
  dsimp only
  let a := max (3 / 2 : ℝ) (Real.sqrt (4 * Real.log (1 / ρ)))
  let A := 1 / (2 * ρ)
  let U := 12 / (5 * ρ)
  let f := fun t => (2 / U) *
    (‖prawitzKernel (t / U)‖ * prawitzMomentEnvelope ρ t)
  have ha0 : (3 / 2 : ℝ) ≤ a := le_max_left _ _
  have ha : 0 < a := by linarith
  have hAp : 0 < A := by dsimp [A]; positivity
  have hUp : 0 < U := by dsimp [U]; positivity
  have hi100 : (100 : ℝ) ≤ 1 / ρ := (le_div_iff₀ hρ).2 (by linarith)
  have hlog : 0 ≤ Real.log (1 / ρ) := Real.log_nonneg (by linarith)
  have haA : a ≤ A := by
    apply max_le
    · dsimp [A]
      apply (le_div_iff₀ (by positivity : 0 < 2 * ρ)).2
      linarith
    · apply (Real.sqrt_le_left hAp.le).2
      have hl := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 / ρ)
      have he : A ^ 2 = (1 / ρ) ^ 2 / 4 := by dsimp [A]; field_simp; norm_num
      rw [he]
      have hq := mul_nonneg (show 0 ≤ 1 / ρ by positivity)
        (show 0 ≤ 1 / ρ - 100 by linarith)
      nlinarith
  have hAU : A ≤ U := by
    dsimp [A, U]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  have hasq : 4 * Real.log (1 / ρ) ≤ a ^ 2 := by
    have hs : Real.sqrt (4 * Real.log (1 / ρ)) ≤ a := le_max_right _ _
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
    rw [Real.sq_sqrt (by positivity)] at hsq
    exact hsq
  have hdmid : ∀ t ∈ Set.Icc a A,
      -(t ^ 2 / 2) + ρ * t ^ 3 / 5 ≤ -((2 / 5 : ℝ) * t ^ 2) := by
    intro t ht
    have hrt : ρ * t ≤ 1 / 2 := by
      have hh := (le_div_iff₀ (by positivity : 0 < 2 * ρ)).1 ht.2
      nlinarith
    have hh := mul_le_mul_of_nonneg_right hrt (sq_nonneg t)
    nlinarith
  have hdfar : ∀ t ∈ Set.Icc A U,
      -(t ^ 2 / 2) + ρ * t ^ 3 / 5 ≤ -((1 / 50 : ℝ) * t ^ 2) := by
    intro t ht
    have hrt : ρ * t ≤ 12 / 5 := by
      have hh := (le_div_iff₀ (by positivity : 0 < 5 * ρ)).1 ht.2
      nlinarith
    have hh := mul_le_mul_of_nonneg_right hrt (sq_nonneg t)
    nlinarith
  obtain ⟨hfmid, hmid⟩ := scaled_integral_comparison ρ U a A (2 / 5)
    hρ rfl ha haA hAU (by norm_num) hdmid
  obtain ⟨hffar, hfar⟩ := scaled_integral_comparison ρ U A U (1 / 50)
    hρ rfl hAp hAU le_rfl (by norm_num) hdfar
  have hgi := weighted_tail_integrable a (2 / 5) (5 * ρ / 12)
    ha (by norm_num) (by positivity)
  have hrestrict : (∫ t in a..A,
      (1 / (Real.pi * t) + 5 * ρ / 12) * Real.exp (-((2 / 5 : ℝ) * t ^ 2))) ≤
      (∫ t in Set.Ioi a,
      (1 / (Real.pi * t) + 5 * ρ / 12) * Real.exp (-((2 / 5 : ℝ) * t ^ 2))) := by
    rw [intervalIntegral.integral_of_le haA]
    refine setIntegral_mono_set hgi ?_ (Filter.Eventually.of_forall ?_)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := ha.trans ht
      positivity
    · intro t ht
      exact ht.1
  have htail := gaussian_reciprocal_linear_tail_bound a (2 / 5) (5 * ρ / 12)
    ha (by norm_num) (by positivity)
  have hexp : Real.exp (-((2 / 5 : ℝ) * a ^ 2)) ≤ ρ * Real.sqrt ρ := by
    have hle : -((2 / 5 : ℝ) * a ^ 2) ≤
        Real.log ρ + Real.log ρ / 2 := by
      have hl : Real.log (1 / ρ) = -Real.log ρ := by rw [one_div, Real.log_inv]
      rw [hl] at hasq hlog
      nlinarith
    calc
      _ ≤ Real.exp (Real.log ρ + Real.log ρ / 2) := Real.exp_le_exp.mpr hle
      _ = ρ * Real.sqrt ρ := by rw [Real.exp_add, Real.exp_half, Real.exp_log hρ]
  have hcoef : 1 / (2 * Real.pi * (2 / 5) * a ^ 2) +
      (5 * ρ / 12) / (2 * (2 / 5) * a) ≤ 1 / 2 := by
    have hrec : 1 / (2 * Real.pi * (2 / 5) * a ^ 2) ≤ (1 / 4 : ℝ) := by
      apply (div_le_iff₀ (by positivity)).2
      have hsq : (9 / 4 : ℝ) ≤ a ^ 2 := by nlinarith
      have hh := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (sq_nonneg a)
      nlinarith
    have hc : (5 * ρ / 12) / (2 * (2 / 5) * a) ≤ (1 / 4 : ℝ) := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith
    linarith
  have hsqrt : Real.sqrt ρ ≤ (1 / 10 : ℝ) :=
    (Real.sqrt_le_left (by norm_num)).2 (by nlinarith)
  have hmidalloc : (∫ t in a..A, f t) ≤ ρ / 20 := by
    have hh := hmid.trans (hrestrict.trans htail)
    have hcpos : 0 ≤ 1 / (2 * Real.pi * (2 / 5) * a ^ 2) +
        (5 * ρ / 12) / (2 * (2 / 5) * a) := by positivity
    have hp := mul_le_mul hcoef hexp (Real.exp_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hs := mul_le_mul_of_nonneg_left hsqrt hρ.le
    change (∫ t in a..A, f t) ≤ _ at hh
    nlinarith
  have hfaralloc : (∫ t in A..U, f t) ≤ ρ / 20 := by
    have hh := prawitz_far_gaussian_tail_budget ρ hρ hsmall
    have he : ∀ t : ℝ, Real.exp (-((1 / 50 : ℝ) * t ^ 2)) =
        Real.exp (-(t ^ 2 / 50)) := by
      intro t
      congr 1
      ring
    simp_rw [he] at hfar
    exact hfar.trans hh
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hfmid hffar
  change (∫ t in a..A, f t) + (∫ t in A..U, f t) = (∫ t in a..U, f t) at hsplit
  change (2 / U) * (∫ t in a..U,
    ‖prawitzKernel (t / U)‖ * prawitzMomentEnvelope ρ t) ≤ 3 * ρ / 20
  rw [← intervalIntegral.integral_const_mul]
  change (∫ t in a..U, f t) ≤ _
  rw [← hsplit]
  linarith

end Causalean.Stat.CLT.BerryEsseen

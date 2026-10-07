module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzBudgetCutoffs
public import Causalean.Stat.CLT.BerryEsseen.PrawitzLowGaussianMoments

/-! # Low-frequency Prawitz allocation at small moment ratios

This assembly lemma connects the spectral kernel and discrepancy envelope to
the independently proved polynomial Gaussian moment bound. The complementary
ratio interval is handled separately; the full budget retains all ratios.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- For [a positive moment ratio ρ at most one hundredth](hyp:ρ,hρ,hsmall), with
the logarithmic inner cutoff U0 = max(3/2, √(4 log(1/ρ))) and the reciprocal
outer cutoff U = 12/(5ρ), [the low-frequency Prawitz contribution
(2/U)·∫ over [0, U0] of the Prawitz filter magnitude at t/U times the discrepancy
envelope is at most one quarter of ρ](goal). -/
theorem prawitz_budget_low_small
    (ρ : ℝ) (hρ : 0 < ρ) (hsmall : ρ ≤ 1 / 100) :
    let U0 := max (3 / 2 : ℝ) (Real.sqrt (4 * Real.log (1 / ρ)))
    let U := 12 / (5 * ρ)
    (2 / U) * (∫ t in (0 : ℝ)..U0,
      ‖prawitzKernel (t / U)‖ * prawitzDiscrepancyEnvelope ρ t) ≤ ρ / 4 := by
  /- All imported analytic leaves are closed. Establish rho*U0 <= 1/5:
  log(1/rho) <= 1/rho-1 and rho <= 1/100 give
  rho^2 * 4*log(1/rho) <= 4*rho*(1-rho) <= 1/25.
  Handle the max's 3/2 branch separately. For 0<t<=U0, use the
  kernel norm bound and U0<=U to obtain
    (2/U)*norm(K(t/U)) <= 1/(pi*t)+5*rho/12.
  The first member of the discrepancy min is at most
    (rho*t^3/6+rho^2*t^4/8)*exp(-23*t^2/100)
  since rho*t<=1/5. Multiplication cancels the apparent 1/t
  singularity and gives exactly the polynomial in
  prawitz_low_gaussian_moment_budget.

  Prove measurability and interval integrability using domination by that
  nonsingular polynomial Gaussian (the assigned kernel value at t=0 is
  harmless). Move 2/U inside the interval integral, rewrite as an Ioc set
  integral, compare, and extend the nonnegative majorant to Ioi 0. Reuse
  the Gaussian moment leaf without redoing its Gamma calculation. This
  module must not import either full or complementary budget theorem. -/
  dsimp only
  let U0 := max (3 / 2 : ℝ) (Real.sqrt (4 * Real.log (1 / ρ)))
  let U := 12 / (5 * ρ)
  let g := fun t : ℝ =>
    (ρ * t ^ 2 / (6 * Real.pi) + ρ ^ 2 * t ^ 3 / (8 * Real.pi) +
      5 * ρ ^ 2 * t ^ 3 / 72 + 5 * ρ ^ 3 * t ^ 4 / 96) *
      Real.exp (-(23 * t ^ 2 / 100))
  let f := fun t : ℝ =>
    (2 / U) * (‖prawitzKernel (t / U)‖ * prawitzDiscrepancyEnvelope ρ t)
  have hρ1 : ρ < 1 := by linarith
  have hcut := prawitz_budget_cutoffs ρ hρ hρ1
  change 0 < U0 ∧ U0 ≤ U at hcut
  have hU : 0 < U := by dsimp [U]; positivity
  have hlog0 : 0 ≤ 4 * Real.log (1 / ρ) := by
    have hinv : 1 ≤ 1 / ρ := (le_div_iff₀ hρ).2 (by linarith)
    positivity [Real.log_nonneg hinv]
  have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 / ρ)
  have hrlog : ρ * Real.log (1 / ρ) ≤ 1 - ρ := by
    have hm := mul_le_mul_of_nonneg_left hlog hρ.le
    have he : ρ * (1 / ρ - 1) = 1 - ρ := by field_simp
    rwa [he] at hm
  have hsquare : ρ ^ 2 * (4 * Real.log (1 / ρ)) ≤ 1 / 25 := by
    have hm := mul_le_mul_of_nonneg_left hrlog hρ.le
    nlinarith [sq_nonneg ρ]
  have hroot : ρ * Real.sqrt (4 * Real.log (1 / ρ)) ≤ 1 / 5 := by
    have hs : (ρ * Real.sqrt (4 * Real.log (1 / ρ))) ^ 2 ≤ 1 / 25 := by
      rw [mul_pow, Real.sq_sqrt hlog0]
      exact hsquare
    nlinarith [Real.sqrt_nonneg (4 * Real.log (1 / ρ))]
  have hsmallcut : ρ * U0 ≤ 1 / 5 := by
    dsimp [U0]
    rw [mul_max_of_nonneg _ _ hρ.le]
    exact max_le (by nlinarith) hroot
  have hnonneg (t : ℝ) (ht : 0 ≤ t) :
      0 ≤ prawitzDiscrepancyEnvelope ρ t := by
    unfold prawitzDiscrepancyEnvelope prawitzMomentEnvelope
    positivity
  have hg0 (t : ℝ) (ht : 0 ≤ t) : 0 ≤ g t := by
    dsimp [g]
    positivity
  have hbound (t : ℝ) (ht : t ∈ Set.Ioc 0 U0) : f t ≤ g t := by
    have ht0 : 0 < t := ht.1
    have htU : t ≤ U := ht.2.trans hcut.2
    have hrt : ρ * t ≤ 1 / 5 :=
      (mul_le_mul_of_nonneg_left ht.2 hρ.le).trans hsmallcut
    have hquot : 0 < t / U := div_pos ht0 hU
    have hk := prawitzKernel_norm_le (t / U)
      (by simpa only [abs_of_pos hquot] using hquot)
      (by rw [abs_of_pos hquot]; exact (div_le_one hU).2 htU)
    have hk' : (2 / U) * ‖prawitzKernel (t / U)‖ ≤
        1 / (Real.pi * t) + 5 * ρ / 12 := by
      have hm := mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ 2 / U)
      rw [abs_of_pos hquot] at hm
      have he : (2 / U) * (1 / (2 * Real.pi * (t / U)) + 1 / 2) =
          1 / (Real.pi * t) + 5 * ρ / 12 := by
        dsimp [U]
        field_simp
      exact hm.trans_eq he
    have hexp : -(t ^ 2 / 4) + ρ * t ^ 3 / 10 ≤ -(23 * t ^ 2 / 100) := by
      have hm := mul_le_mul_of_nonneg_right hrt (sq_nonneg t)
      nlinarith
    have hd : prawitzDiscrepancyEnvelope ρ t ≤
        (ρ * t ^ 3 / 6 + ρ ^ 2 * t ^ 4 / 8) * Real.exp (-(23 * t ^ 2 / 100)) := by
      unfold prawitzDiscrepancyEnvelope
      refine (min_le_left _ _).trans ?_
      rw [abs_of_pos ht0]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
    calc
      f t = ((2 / U) * ‖prawitzKernel (t / U)‖) *
          prawitzDiscrepancyEnvelope ρ t := by dsimp [f]; ring
      _ ≤ (1 / (Real.pi * t) + 5 * ρ / 12) *
          ((ρ * t ^ 3 / 6 + ρ ^ 2 * t ^ 4 / 8) *
            Real.exp (-(23 * t ^ 2 / 100))) :=
        mul_le_mul hk' hd (hnonneg t ht0.le) (by positivity)
      _ = g t := by dsimp [g]; field_simp; ring
  have hmeasK : Measurable prawitzKernel := by
    have hs : Measurable Real.sign := by
      unfold Real.sign
      exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
        measurable_const (Measurable.ite (measurableSet_lt measurable_const measurable_id)
          measurable_const measurable_const)
    have hab : Measurable (fun t : ℝ => |t|) := by fun_prop
    unfold prawitzKernel
    apply Measurable.ite
    · exact (measurableSet_eq_fun measurable_id measurable_const).union
        (measurableSet_lt measurable_const hab)
    · fun_prop
    · fun_prop
  have hmeasD : Measurable (prawitzDiscrepancyEnvelope ρ) := by
    unfold prawitzDiscrepancyEnvelope prawitzMomentEnvelope
    fun_prop
  have hmeasf : Measurable f := by dsimp [f]; fun_prop
  have hint (n : ℕ) : IntegrableOn
      (fun t : ℝ => t ^ n * Real.exp (-(23 / 100 : ℝ) * t ^ 2)) (Set.Ioi 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_two] using
      (integrableOn_rpow_mul_exp_neg_mul_sq (s := (n : ℝ)) (by norm_num : (0 : ℝ) < 23 / 100)
        (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith))
  have hgi : IntegrableOn g (Set.Ioi 0) := by
    have hi := (((hint 2).const_mul (ρ / (6 * Real.pi))).add
      ((hint 3).const_mul (ρ ^ 2 / (8 * Real.pi)))).add
      ((hint 3).const_mul (5 * ρ ^ 2 / 72))
    have hi' := hi.add ((hint 4).const_mul (5 * ρ ^ 3 / 96))
    change Integrable g (volume.restrict (Set.Ioi 0))
    apply hi'.congr
    filter_upwards [] with t
    dsimp [g]
    rw [show -(23 * t ^ 2 / 100) = -(23 / 100 : ℝ) * t ^ 2 by ring]
    ring
  have hsub : Set.Ioc 0 U0 ⊆ Set.Ioi (0 : ℝ) := fun _ ht => ht.1
  have hgi' := hgi.mono_set hsub
  have hfi : IntegrableOn f (Set.Ioc 0 U0) := by
    apply hgi'.mono' hmeasf.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      dsimp [f]
      exact mul_nonneg (by positivity) (mul_nonneg (norm_nonneg _) (hnonneg t ht.1.le)))]
    exact hbound t ht
  calc
    (2 / U) * (∫ t in (0 : ℝ)..U0,
        ‖prawitzKernel (t / U)‖ * prawitzDiscrepancyEnvelope ρ t) =
        ∫ t in Set.Ioc 0 U0, f t := by
      rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hcut.1.le]
    _ ≤ ∫ t in Set.Ioc 0 U0, g t :=
      setIntegral_mono_on hfi hgi' measurableSet_Ioc hbound
    _ ≤ ∫ t in Set.Ioi (0 : ℝ), g t := by
      apply setIntegral_mono_set hgi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hg0 t ht.le
      · exact Filter.Eventually.of_forall hsub
    _ ≤ ρ / 4 := prawitz_low_gaussian_moment_budget ρ hρ hsmall

end Causalean.Stat.CLT.BerryEsseen

module
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.PowerL1Core

/-!
# Curvature control of the Bernstein power approximation

This module integrates the adjacent-order-statistic hinge error and proves the
finite Bernstein L1 approximation for real power weights.
-/

public section

namespace Causalean.Stat.OrderStatistic.WeightedConcomitant

open MeasureTheory
open Causalean.Stat.OrderStatistic

noncomputable section

/-- For a power above one, the curvature times the
absolute error of the Bernstein hinge approximation is integrable on the
unit square. This is the Fubini prerequisite for the power-density bound. -/
theorem power_curvature_hinge_error_integrable {N : ℕ}
    {s : ℝ} (hs : 1 < s) :
    Integrable
      (fun p : ℝ × ℝ => powerCurvature s p.1 *
        |bernsteinCell N (hingeCell N p.1) p.2 -
          (if p.1 ≤ p.2 then (1 : ℝ) else 0)|)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
        (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
  -- Bound the hinge kernel and the step by one; curvature is integrable
  -- even when 1 < s < 2 and it is singular at the right endpoint.
  let I : Set ℝ := Set.Icc 0 1
  let μ : Measure ℝ := volume.restrict I
  have hq : Integrable (powerCurvature s) μ := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)).mp
    have hr : IntervalIntegrable (fun x : ℝ => x ^ (s - 2)) volume 0 1 :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    have hr' : IntervalIntegrable (fun t : ℝ => (1 - t) ^ (s - 2))
        volume 0 1 := by
      convert (hr.comp_sub_left 1).symm using 1 <;> norm_num
    change IntervalIntegrable (fun t : ℝ =>
      s * (s - 1) * (1 - t) ^ (s - 2)) volume 0 1
    exact hr'.const_mul (s * (s - 1))
  have hc : Continuous (fun p : ℝ × ℝ =>
      bernsteinCell N (hingeCell N p.1) p.2) := by
    unfold bernsteinCell hingeCell
    fun_prop
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hc.continuousOn : ContinuousOn
      (fun p : ℝ × ℝ => bernsteinCell N (hingeCell N p.1) p.2) (I ×ˢ I))
  have he : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      |bernsteinCell N (hingeCell N p.1) p.2 -
        (if p.1 ≤ p.2 then (1 : ℝ) else 0)|) (μ.prod μ) := by
    apply Measurable.aestronglyMeasurable
    apply Measurable.abs
    apply Measurable.sub
    · exact hc.measurable
    · exact Measurable.ite
        (measurableSet_le measurable_fst measurable_snd) measurable_const measurable_const
  have hbound : ∀ᵐ p : ℝ × ℝ ∂μ.prod μ,
      ‖bernsteinCell N (hingeCell N p.1) p.2 -
        (if p.1 ≤ p.2 then (1 : ℝ) else 0)‖ ≤ C + 1 := by
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    calc
      _ ≤ ‖bernsteinCell N (hingeCell N p.1) p.2‖ +
            ‖(if p.1 ≤ p.2 then (1 : ℝ) else 0)‖ := norm_sub_le _ _
      _ ≤ C + 1 := by
        apply add_le_add (hC p hp)
        split_ifs <;> norm_num
  have hqprod : Integrable (fun p : ℝ × ℝ => powerCurvature s p.1)
      (μ.prod μ) := hq.comp_fst μ
  have hbound' : ∀ᵐ p : ℝ × ℝ ∂μ.prod μ,
      ‖|bernsteinCell N (hingeCell N p.1) p.2 -
        (if p.1 ≤ p.2 then (1 : ℝ) else 0)|‖ ≤ C + 1 := by
    simpa only [Real.norm_eq_abs, abs_abs] using hbound
  have hint := hqprod.mul_bdd he hbound'
  simpa only [μ, I] using hint

/-- The L1 norm of the integrated, curvature-weighted hinge error is at
most the curvature-weighted integral of its pointwise L1 norms. -/
theorem power_curvature_hinge_error_integral_le {N : ℕ}
    {s : ℝ} (hs : 1 < s) :
    (∫ u in Set.Icc (0 : ℝ) 1,
      |∫ t in Set.Icc (0 : ℝ) 1, powerCurvature s t *
        (bernsteinCell N (hingeCell N t) u -
          (if t ≤ u then (1 : ℝ) else 0)) ∂volume| ∂volume) ≤
      ∫ t in Set.Icc (0 : ℝ) 1, powerCurvature s t *
        (∫ u in Set.Icc (0 : ℝ) 1,
          |bernsteinCell N (hingeCell N t) u -
            (if t ≤ u then (1 : ℝ) else 0)| ∂volume) ∂volume := by
  -- Apply abs_integral_le_integral_abs for each u and integral_prod_symm
  -- using power_curvature_hinge_error_integrable.
  let I : Set ℝ := Set.Icc 0 1
  let μ : Measure ℝ := volume.restrict I
  let F : ℝ × ℝ → ℝ := fun p => powerCurvature s p.1 *
    (bernsteinCell N (hingeCell N p.1) p.2 -
      (if p.1 ≤ p.2 then (1 : ℝ) else 0))
  let G : ℝ × ℝ → ℝ := fun p => powerCurvature s p.1 *
    |bernsteinCell N (hingeCell N p.1) p.2 -
      (if p.1 ≤ p.2 then (1 : ℝ) else 0)|
  have hG : Integrable G (μ.prod μ) :=
    power_curvature_hinge_error_integrable hs
  have hFmeas : AEStronglyMeasurable F (μ.prod μ) := by
    apply Measurable.aestronglyMeasurable
    dsimp [F, powerCurvature, bernsteinCell, hingeCell]
    apply Measurable.mul
    · fun_prop
    · apply Measurable.sub
      · fun_prop
      · exact Measurable.ite
          (measurableSet_le measurable_fst measurable_snd)
          measurable_const measurable_const
  have hqnonneg : ∀ t ∈ I, 0 ≤ powerCurvature s t := by
    intro t ht
    unfold powerCurvature
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith))
      (Real.rpow_nonneg (by have := ht.2; dsimp [I] at ht; linarith) _)
  have hnorm : ∀ᵐ p : ℝ × ℝ ∂μ.prod μ, ‖F p‖ = G p := by
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    dsimp [F, G]
    rw [abs_mul, abs_of_nonneg (hqnonneg p.1 hp.1)]
  have hF : Integrable F (μ.prod μ) := by
    apply (integrable_norm_iff hFmeas).1
    exact hG.congr (by filter_upwards [hnorm] with p hp; exact hp.symm)
  have houterF : Integrable (fun u => ∫ t, F (t, u) ∂μ) μ :=
    hF.swap.integral_prod_left
  have houterG : Integrable (fun u => ∫ t, G (t, u) ∂μ) μ :=
    hG.swap.integral_prod_left
  have hpoint (u : ℝ) : |∫ t, F (t, u) ∂μ| ≤ ∫ t, G (t, u) ∂μ := by
    calc
      _ ≤ ∫ t, |F (t, u)| ∂μ := abs_integral_le_integral_abs
      _ = ∫ t, G (t, u) ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        dsimp [F, G]
        rw [abs_mul, abs_of_nonneg (hqnonneg t ht)]
  have hle : (∫ u, |∫ t, F (t, u) ∂μ| ∂μ) ≤
      ∫ u, (∫ t, G (t, u) ∂μ) ∂μ :=
    integral_mono houterF.abs houterG hpoint
  have hswap : (∫ u, (∫ t, G (t, u) ∂μ) ∂μ) =
      ∫ t, (∫ u, G (t, u) ∂μ) ∂μ :=
    (integral_integral_swap hG).symm
  calc
    _ = ∫ u, |∫ t, F (t, u) ∂μ| ∂μ := rfl
    _ ≤ ∫ u, (∫ t, G (t, u) ∂μ) ∂μ := hle
    _ = ∫ t, (∫ u, G (t, u) ∂μ) ∂μ := hswap
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t
      dsimp [G]
      rw [integral_const_mul]

/-- For a real power above one, the L1 error of its finite Bernstein cell
density is bounded by the curvature-weighted adjacent-threshold error. -/
theorem power_bernstein_L1_le_curvature_error {N : ℕ}
    (hN : 0 < N) {s : ℝ} (hs : 1 < s) :
    (∫ u in Set.Icc (0 : ℝ) 1,
      |bernsteinCell N (powerCell N s) u - powerDensity s u| ∂volume) ≤
      ∫ t in Set.Icc (0 : ℝ) 1,
        powerCurvature s t * Real.sqrt (2 * t / N) ∂volume := by
  let I : Set ℝ := Set.Icc 0 1
  let μ : Measure ℝ := volume.restrict I
  have hr : IntervalIntegrable (fun x : ℝ => x ^ (s - 2)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hr' : IntervalIntegrable (fun t : ℝ => (1 - t) ^ (s - 2)) volume 0 1 := by
    convert (hr.comp_sub_left 1).symm using 1 <;> norm_num
  have hq : Integrable (powerCurvature s) μ := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)).mp
    change IntervalIntegrable (fun t : ℝ =>
      s * (s - 1) * (1 - t) ^ (s - 2)) volume 0 1
    exact hr'.const_mul (s * (s - 1))
  have hstep (u : ℝ) : Integrable
      (fun t => powerCurvature s t * (if t ≤ u then (1 : ℝ) else 0)) μ := by
    apply hq.mul_bdd (c := 1)
    · exact (Measurable.ite (measurableSet_le measurable_id measurable_const)
        measurable_const measurable_const).aestronglyMeasurable
    · filter_upwards [] with t
      split_ifs <;> simp
  have hhinge (u : ℝ) : Integrable
      (fun t => powerCurvature s t * bernsteinCell N (hingeCell N t) u) μ := by
    have hc : Continuous (fun t : ℝ => bernsteinCell N (hingeCell N t) u) := by
      unfold bernsteinCell hingeCell
      fun_prop
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hc.continuousOn : ContinuousOn
        (fun t : ℝ => bernsteinCell N (hingeCell N t) u) I)
    apply hq.mul_bdd (c := C)
    · exact hc.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hC t ht
  have heq (u : ℝ) (hu : u ∈ I) :
      bernsteinCell N (powerCell N s) u - powerDensity s u =
      - ∫ t in I, powerCurvature s t *
        (bernsteinCell N (hingeCell N t) u -
          (if t ≤ u then (1 : ℝ) else 0)) ∂volume := by
    rw [bernsteinCell_power_eq_sub_curvature_hinge_integral hN hs u,
      powerDensity_eq_sub_curvature_integral hs hu]
    calc
      _ = -((∫ t in I, powerCurvature s t *
              bernsteinCell N (hingeCell N t) u ∂volume) -
            (∫ t in I, powerCurvature s t *
              (if t ≤ u then (1 : ℝ) else 0) ∂volume)) := by ring
      _ = _ := by
        rw [← integral_sub (hhinge u) (hstep u)]
        congr 1
        apply integral_congr_ae
        filter_upwards [] with t
        ring
  calc
    (∫ u in I, |bernsteinCell N (powerCell N s) u - powerDensity s u| ∂volume) =
        ∫ u in I, |∫ t in I, powerCurvature s t *
          (bernsteinCell N (hingeCell N t) u -
            (if t ≤ u then (1 : ℝ) else 0)) ∂volume| ∂volume := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro u hu
      dsimp
      rw [heq u hu, abs_neg]
    _ ≤ ∫ t in I, powerCurvature s t *
          (∫ u in I, |bernsteinCell N (hingeCell N t) u -
            (if t ≤ u then (1 : ℝ) else 0)| ∂volume) ∂volume :=
      power_curvature_hinge_error_integral_le hs
    _ ≤ ∫ t in I, powerCurvature s t * Real.sqrt (2 * t / N) ∂volume := by
      have hG := power_curvature_hinge_error_integrable (N := N) hs
      have hleft : Integrable (fun t => powerCurvature s t *
          (∫ u in I, |bernsteinCell N (hingeCell N t) u -
            (if t ≤ u then (1 : ℝ) else 0)| ∂volume)) μ := by
        have hG' := hG.integral_prod_left
        simp only [integral_const_mul] at hG'
        exact hG'
      have hroot : Integrable (fun t => Real.sqrt (2 * t / N)) μ := by
        apply Continuous.integrableOn_Icc
        fun_prop
      have hright : Integrable (fun t =>
          powerCurvature s t * Real.sqrt (2 * t / N)) μ := by
        apply hq.mul_bdd (c := 2) hroot.aestronglyMeasurable
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        have hNr : (0 : ℝ) < N := by exact_mod_cast hN
        have harg : 2 * t / (N : ℝ) ≤ 4 := by
          apply (div_le_iff₀ hNr).mpr
          have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
          nlinarith [ht.2]
        calc
          _ ≤ Real.sqrt 4 := Real.sqrt_le_sqrt harg
          _ = 2 := by norm_num
      apply integral_mono_ae hleft hright
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact mul_le_mul_of_nonneg_left
        (bernsteinCell_hinge_indicator_L1 hN ht)
        (by
          unfold powerCurvature
          exact mul_nonneg (mul_nonneg (by linarith) (by linarith))
            (Real.rpow_nonneg (by linarith [ht.2]) _))

/-- For a [positive sample size](hyp:hN),
 [the Bernstein kernel of first-power cells agrees with the constant unit density in L1](goal). -/
theorem power_bernstein_L1_one {N : ℕ} (hN : 0 < N) :
    (∫ u in Set.Icc (0 : ℝ) 1,
      |bernsteinCell N (powerCell N 1) u - powerDensity 1 u| ∂volume) = 0 := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hcell (j : Fin N) : powerCell N 1 j = 1 / N := by
    unfold powerCell
    simp only [Real.rpow_one]
    field_simp
    ring
  have hbern (u : ℝ) : bernsteinCell N (powerCell N 1) u = 1 := by
    simp_rw [bernsteinCell, hcell]
    have hsum :
        (∑ j : Fin N, (Nat.choose (N - 1) (j : ℕ) : ℝ) *
          u ^ (j : ℕ) * (1 - u) ^ (N - 1 - (j : ℕ))) = 1 := by
      have hpow := add_pow u (1 - u) (N - 1)
      rw [show N - 1 + 1 = N by omega, ← Fin.sum_univ_eq_sum_range] at hpow
      convert hpow.symm using 1
      · apply Finset.sum_congr rfl
        intro j hj
        ring
      · ring
    calc
      (N : ℝ) * ∑ j : Fin N, (1 / N) * (Nat.choose (N - 1) (j : ℕ) : ℝ) *
          u ^ (j : ℕ) * (1 - u) ^ (N - 1 - (j : ℕ)) =
          N * ((1 / N) * ∑ j : Fin N, (Nat.choose (N - 1) (j : ℕ) : ℝ) *
            u ^ (j : ℕ) * (1 - u) ^ (N - 1 - (j : ℕ))) := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = N * (1 / N) * ∑ j : Fin N, (Nat.choose (N - 1) (j : ℕ) : ℝ) *
            u ^ (j : ℕ) * (1 - u) ^ (N - 1 - (j : ℕ)) := by
        ring
      _ = 1 := by rw [hsum]; field_simp
  have hdens (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) : powerDensity 1 u = 1 := by
    simp [powerDensity, Real.rpow_zero]
  have hzero : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |bernsteinCell N (powerCell N 1) u - powerDensity 1 u| = 0 := by
    intro u hu
    rw [hbern u, hdens u hu]
    norm_num
  rw [setIntegral_congr_fun measurableSet_Icc hzero]
  simp

/-- For a [positive sample size](hyp:hN) and [power](hyp:hs) greater than the sample size,
 [the unit-density bound gives the claimed L1 estimate](goal). -/
theorem power_bernstein_L1_large {N : ℕ} (hN : 0 < N) {s : ℝ}
    (hs : (N : ℝ) < s) :
    (∫ u in Set.Icc (0 : ℝ) 1,
      |bernsteinCell N (powerCell N s) u - powerDensity s u| ∂volume) ≤
      2 * Real.sqrt (s / N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs1 : 1 ≤ s := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hb : Continuous (bernsteinCell N (powerCell N s)) := by
    unfold bernsteinCell
    fun_prop
  have hd : Continuous (powerDensity s) := by
    unfold powerDensity
    exact continuous_const.mul ((Real.continuous_rpow_const (by linarith : 0 ≤ s - 1)).comp
      (continuous_const.sub continuous_id))
  have hib : IntegrableOn (bernsteinCell N (powerCell N s)) (Set.Icc (0 : ℝ) 1) volume :=
    hb.integrableOn_Icc
  have hid : IntegrableOn (powerDensity s) (Set.Icc (0 : ℝ) 1) volume :=
    hd.integrableOn_Icc
  have hiabs : IntegrableOn
      (fun u => |bernsteinCell N (powerCell N s) u - powerDensity s u|)
      (Set.Icc (0 : ℝ) 1) volume := by
    apply Continuous.integrableOn_Icc
    exact (hb.sub hd).abs
  have hiadd : IntegrableOn
      (fun u => bernsteinCell N (powerCell N s) u + powerDensity s u)
      (Set.Icc (0 : ℝ) 1) volume := hib.add hid
  have hbound :
      (∫ u in Set.Icc (0 : ℝ) 1,
        |bernsteinCell N (powerCell N s) u - powerDensity s u| ∂volume) ≤ 2 := by
    calc
      (∫ u in Set.Icc (0 : ℝ) 1,
        |bernsteinCell N (powerCell N s) u - powerDensity s u| ∂volume) ≤
          ∫ u in Set.Icc (0 : ℝ) 1,
            (bernsteinCell N (powerCell N s) u + powerDensity s u) ∂volume := by
        apply setIntegral_mono_on hiabs hiadd measurableSet_Icc
        intro u hu
        have hbu := bernsteinCell_nonneg (N := N) (a := powerCell N s)
          (fun j => powerCell_nonneg hs1 j) hu
        have hdu : 0 ≤ powerDensity s u := by
          unfold powerDensity
          exact mul_nonneg (by linarith) (Real.rpow_nonneg (by linarith [hu.2]) _)
        rw [abs_le]
        constructor <;> linarith
      _ = 2 := by
        rw [integral_add hib hid,
          integral_bernsteinCell hN (powerCell N s) (sum_powerCell hN hs1),
          integral_powerDensity hs1]
        norm_num
  have hratio : 1 ≤ s / N := (le_div_iff₀ hNr).2 (by nlinarith)
  have hsqrt : 1 ≤ Real.sqrt (s / N) := by
    simpa using Real.sqrt_le_sqrt hratio
  nlinarith

/-- For a [positive sample size](hyp:hN) and [power](hyp:hs,hsmall) between one and the sample
 size, [the adjacent-order-statistic coupling gives the claimed L1 estimate](goal). -/
theorem power_bernstein_L1_small {N : ℕ} (hN : 0 < N) {s : ℝ}
    (hs : 1 ≤ s) (hsmall : s ≤ N) :
    (∫ u in Set.Icc (0 : ℝ) 1,
      |bernsteinCell N (powerCell N s) u - powerDensity s u| ∂volume) ≤
      2 * Real.sqrt (s / N) := by
  rcases eq_or_lt_of_le hs with rfl | hs'
  · rw [power_bernstein_L1_one hN]
    positivity
  · have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    calc
      (∫ u in Set.Icc (0 : ℝ) 1,
        |bernsteinCell N (powerCell N s) u - powerDensity s u| ∂volume) ≤
          ∫ t in Set.Icc (0 : ℝ) 1,
            powerCurvature s t * Real.sqrt (2 * t / N) ∂volume :=
        power_bernstein_L1_le_curvature_error hN hs'
      _ = Real.sqrt (2 / N) *
          (∫ t in Set.Icc (0 : ℝ) 1,
            powerCurvature s t * Real.sqrt t ∂volume) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with t
        rw [show 2 * t / (N : ℝ) = (2 / N) * t by ring,
          Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ) / N)]
        ring
      _ ≤ Real.sqrt (2 / N) * Real.sqrt s :=
        mul_le_mul_of_nonneg_left (integral_powerCurvature_mul_sqrt_le hs')
          (Real.sqrt_nonneg _)
      _ ≤ 2 * Real.sqrt (s / N) := by
        calc
          Real.sqrt (2 / N) * Real.sqrt s = Real.sqrt (2 * s / N) := by
            rw [show 2 * s / (N : ℝ) = (2 / N) * s by ring,
              Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ) / N)]
          _ ≤ Real.sqrt (4 * s / N) := by
            apply Real.sqrt_le_sqrt
            apply (div_le_div_iff_of_pos_right hNr).mpr
            nlinarith
          _ = 2 * Real.sqrt (s / N) := by
            rw [show 4 * s / (N : ℝ) = 4 * (s / N) by ring,
              Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
            norm_num

/-- For a [positive sample size](hyp:hN) and [real power](hyp:hs) at least one,
 [the Bernstein power kernel has L1 error at most `2 sqrt(s/N)`](goal). -/
theorem power_bernstein_L1 {N : ℕ} (hN : 0 < N) {s : ℝ} (hs : 1 ≤ s) :
    (∫ u in Set.Icc (0 : ℝ) 1,
      |bernsteinCell N (powerCell N s) u - powerDensity s u| ∂volume) ≤
      2 * Real.sqrt (s / N) := by
  by_cases hlarge : (N : ℝ) < s
  · exact power_bernstein_L1_large hN hlarge
  · exact power_bernstein_L1_small hN hs (le_of_not_gt hlarge)


end
end Causalean.Stat.OrderStatistic.WeightedConcomitant

module
public import Causalean.Stat.CLT.BerryEsseen.CscSquaredSeries
public import Causalean.Stat.CLT.BerryEsseen.PrawitzAbelLimit
public import Causalean.Stat.CLT.BerryEsseen.PrawitzAbelSeries
public import Causalean.Stat.CLT.BerryEsseen.PrawitzKernel
public import Causalean.Stat.CLT.BerryEsseen.PrawitzSineCoefficient
public import Causalean.Stat.CLT.BerryEsseen.TriangularCosineIntegral
public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

/-! # The Prawitz sine integral as a reciprocal-square series

This exact deterministic identity isolates the harmonic-analysis bridge
from the endpoint integrability and the elementary reciprocal-tail bounds.
It uses radians y=2πx, and includes positive integer x without an exclusion.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory Filter Topology

/-- For [a positive spatial coordinate x](hyp:x,hx), [the Prawitz sign
approximation error, one minus the approximation at 2πx, equals
(sin(πx)/π)² times the reciprocal-square series correction
1/x² + 2·Σ_{n≥0} 1/(x+n+1)² − 2/x](goal). -/
theorem prawitzSignApprox_reciprocal_sq_identity (x : ℝ) (hx : 0 < x) :
    1 - prawitzSignApprox (2 * Real.pi * x) =
      (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
        (1 / x ^ 2 + 2 * (∑' n : ℕ, 1 / (x + (n : ℝ) + 1) ^ 2) - 2 / x) := by
  classical
  let c : ℕ → ℝ := fun n => ∫ t in (0 : ℝ)..1, (1 - t) *
    Real.sin (2 * Real.pi * ((n : ℝ) + 1) * t) *
    Real.sin (2 * Real.pi * x * t)
  let S : ℝ := (Real.sin (Real.pi * x) / Real.pi) ^ 2
  have hc (n : ℕ) : c n =
      (Real.sinc (Real.pi * ((n : ℝ) + 1 - x)) ^ 2 -
        Real.sinc (Real.pi * ((n : ℝ) + 1 + x)) ^ 2) / 4 :=
    triangular_sine_product_integral _ _
  -- Undamp the coefficient series and add the constant part of the sine weight.
  have hbridge (hs : Summable c) :
      prawitzSignApprox (2 * Real.pi * x) = 4 * (∑' n, c n) + 2 * S / x := by
    have hlim := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hs.hasSum.tendsto_sum_nat
    have hlim' : Filter.Tendsto (fun r : ℝ => 2 * (∑' n, r ^ (n + 1) * c n))
        (nhdsWithin 1 (Set.Iio 1)) (nhds (2 * ∑' n, c n)) := by
      have ht := (tendsto_const_nhds (x := (2 : ℝ))).mul
        ((continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds).mul hlim)
      simp only [id_eq, one_mul] at ht
      convert ht using 1
      · funext r
        congr 1
        rw [← tsum_mul_left]
        apply tsum_congr
        intro n
        rw [pow_succ]
        ring
    have heq : (fun r : ℝ => ∫ t in (0 : ℝ)..1, (1 - t) *
        (2 * r * Real.sin (2 * Real.pi * t) /
          (1 - 2 * r * Real.cos (2 * Real.pi * t) + r ^ 2)) *
        Real.sin (2 * Real.pi * x * t)) =ᶠ[nhdsWithin 1 (Set.Iio 1)]
        (fun r => 2 * ∑' n, r ^ (n + 1) * c n) := by
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds
        (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)),
        self_mem_nhdsWithin] with r hr hr1
      exact (prawitz_abel_weighted_integral_series x r hr hr1).2
    have hi := tendsto_nhds_unique (prawitz_abel_weighted_integral_tendsto x)
      (hlim'.congr' heq.symm)
    have hconst : (∫ t in (0 : ℝ)..1,
        Real.sin (t * (2 * Real.pi * x)) / Real.pi) = S / x := by
      rw [intervalIntegral.integral_div,
        intervalIntegral.integral_comp_mul_right Real.sin (by positivity), integral_sin]
      simp only [zero_mul, one_mul, Real.cos_zero, smul_eq_mul]
      have hcos := Real.sin_sq_eq_half_sub (Real.pi * x)
      dsimp [S]
      rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring]
      field_simp
      rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring]
      nlinarith
    have hcont : IntervalIntegrable (fun t : ℝ =>
        Real.sin (t * (2 * Real.pi * x)) / Real.pi) MeasureTheory.volume 0 1 :=
      (show Continuous (fun t : ℝ => Real.sin (t * (2 * Real.pi * x)) / Real.pi)
        by fun_prop).intervalIntegrable _ _
    have hw := (prawitz_sine_intervalIntegrable (2 * Real.pi * x)).sub hcont
    have hw' : IntervalIntegrable (fun t : ℝ =>
        (1 - t) * Real.cos (Real.pi * t) / Real.sin (Real.pi * t) *
          Real.sin (t * (2 * Real.pi * x))) MeasureTheory.volume 0 1 := by
      convert hw using 1
      funext t
      dsimp [prawitzSineWeight]
      ring
    unfold prawitzSignApprox
    rw [show (fun t : ℝ => prawitzSineWeight t * Real.sin (t * (2 * Real.pi * x))) =
        (fun t => (1 - t) * Real.cos (Real.pi * t) / Real.sin (Real.pi * t) *
          Real.sin (t * (2 * Real.pi * x)) + Real.sin (t * (2 * Real.pi * x)) / Real.pi)
        by funext t; dsimp [prawitzSineWeight]; ring,
      intervalIntegral.integral_add hw' hcont, hconst]
    have hi' : (∫ t in (0 : ℝ)..1, (1 - t) * Real.cos (Real.pi * t) /
        Real.sin (Real.pi * t) * Real.sin (t * (2 * Real.pi * x))) = 2 * ∑' n, c n := by
      simpa only [mul_comm (2 * Real.pi * x)] using hi
    rw [hi']
    ring
  -- At an integer, precisely one squared-sinc coefficient survives.
  by_cases hsin : Real.sin (Real.pi * x) = 0
  · obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hsin
    have hmx : (m : ℝ) = x := by nlinarith [Real.pi_pos]
    have hmpos : 0 ≤ m := by exact_mod_cast (show (0 : ℝ) ≤ m by linarith)
    lift m to ℕ using hmpos
    have hmne : m ≠ 0 := by intro h; simp [h] at hmx; linarith
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hmne
    have hxc : x = (k : ℝ) + 1 := by simpa using hmx.symm
    have hcoef (n : ℕ) : c n = if n = k then 1 / 4 else 0 := by
      rw [hc]
      have hp : Real.sinc (Real.pi * ((n : ℝ) + 1 + x)) = 0 := by
        rw [Real.sinc_of_ne_zero (by positivity)]
        rw [show Real.pi * ((n : ℝ) + 1 + x) =
          Real.pi * x + (n + 1 : ℕ) * Real.pi by push_cast; ring,
          Real.sin_add_nat_mul_pi, hsin]
        simp
      rw [hp]
      by_cases hn : n = k
      · simp [hn, hxc]
      · have hn' : (n : ℝ) + 1 - x ≠ 0 := by
          rw [hxc]
          intro h
          apply hn
          exact_mod_cast (show (n : ℝ) = k by linarith)
        rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hn')]
        rw [show Real.pi * ((n : ℝ) + 1 - x) =
          (n + 1 : ℕ) * Real.pi - Real.pi * x by push_cast; ring,
          Real.sin_nat_mul_pi_sub, hsin]
        simp [hn]
    have hs : Summable c := by
      change Summable (fun n => c n)
      simp_rw [hcoef]
      exact (hasSum_ite_eq k (1 / 4 : ℝ)).summable
    have hsum : (∑' n, c n) = 1 / 4 := by simp_rw [hcoef]; simp
    rw [hbridge hs, hsum]
    simp [S, hsin]
  -- Away from integers, the csc identity eliminates the negative-shift tail.
  · have hsym := csc_squared_reciprocal_series x hsin
    let f : ℕ → ℝ := fun n => 1 / (x - ((n : ℝ) + 1)) ^ 2
    let g : ℕ → ℝ := fun n => 1 / (x + ((n : ℝ) + 1)) ^ 2
    have hf : Summable f := Summable.of_nonneg_of_le (fun n => by dsimp [f]; positivity)
      (fun n => by dsimp [f]; exact le_add_of_nonneg_right (by positivity)) hsym.1
    have hg : Summable g := Summable.of_nonneg_of_le (fun n => by dsimp [g]; positivity)
      (fun n => by dsimp [g]; exact le_add_of_nonneg_left (by positivity)) hsym.1
    have hcoef (n : ℕ) : c n = S / 4 * (f n - g n) := by
      have hm : (n : ℝ) + 1 - x ≠ 0 := by
        intro h
        apply hsin
        have he : x = (n + 1 : ℕ) := by push_cast; linarith
        rw [he, mul_comm]
        exact Real.sin_nat_mul_pi _
      have hp : (n : ℝ) + 1 + x ≠ 0 := by positivity
      rw [hc, Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hm),
        Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hp)]
      rw [show Real.pi * ((n : ℝ) + 1 - x) =
          (n + 1 : ℕ) * Real.pi - Real.pi * x by push_cast; ring,
        Real.sin_nat_mul_pi_sub,
        show Real.pi * ((n : ℝ) + 1 + x) =
          Real.pi * x + (n + 1 : ℕ) * Real.pi by push_cast; ring,
        Real.sin_add_nat_mul_pi]
      dsimp [S, f, g]
      have hpow : ((-1 : ℝ) ^ (n + 1)) ^ 2 = 1 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
      simp only [div_pow, neg_sq, mul_pow, hpow, one_mul]
      push_cast
      have hm' : x - ((n : ℝ) + 1) ≠ 0 := by intro h; apply hm; linarith
      field_simp [Real.pi_ne_zero, hm, hp, hm']
      ring
    have hs : Summable c := by
      change Summable (fun n => c n)
      simp_rw [hcoef]
      exact (hf.sub hg).mul_left _
    have hsum : (∑' n, c n) = S / 4 * ((∑' n, f n) - ∑' n, g n) := by
      simp_rw [hcoef]
      rw [tsum_mul_left, hf.tsum_sub hg]
    have hid : S * (1 / x ^ 2 + ((∑' n, f n) + ∑' n, g n)) = 1 := by
      simpa only [S, f, g, hf.tsum_add hg] using hsym.2
    have hg' : (∑' n, g n) = ∑' n : ℕ, 1 / (x + (n : ℝ) + 1) ^ 2 := by
      apply tsum_congr
      intro n
      dsimp [g]
      rw [add_assoc]
    rw [hbridge hs, hsum, ← hg']
    change 1 - (4 * (S / 4 * _) + 2 * S / x) = S * _
    linear_combination -hid

end Causalean.Stat.CLT.BerryEsseen

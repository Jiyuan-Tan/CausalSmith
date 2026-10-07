module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzBudgetCutoffs
public import Causalean.Stat.CLT.BerryEsseen.PrawitzCompactCellIntegrals
public import Causalean.Stat.CLT.BerryEsseen.PrawitzCompactIntegrability
public import Causalean.Stat.CLT.BerryEsseen.PrawitzCompactRealCutoffs
public import Causalean.Stat.CLT.BerryEsseen.PrawitzCutoffRationalCertificate
public import Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate
public import Causalean.Stat.CLT.BerryEsseen.PrawitzLowRealEnclosures
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Low-frequency Prawitz allocation on the complementary ratio interval

This independent deterministic certificate retains the actual minimum
discrepancy envelope and kernel on ratios above one hundredth. Together with
the small-ratio assembly it proves the unchanged full low-frequency budget.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- On [a positive parameter cell](hyp:ρ,r,s,hr,hrρ,hρs) and
[a positive frequency cell inside the original kernel band](hyp:t,a,b,ha,hat,htb,htU),
the [normalized low-frequency integrand is bounded by the better of the
Taylor and modulus-sum cell bounds](goal). -/
theorem prawitz_low_compact_cell_bound
    (ρ r s t a b : ℝ) (hr : 0 < r) (hrρ : r ≤ ρ) (hρs : ρ ≤ s)
    (ha : 0 < a) (hat : a ≤ t) (htb : t ≤ b) (htU : t ≤ 12 / (5 * ρ)) :
    (5 / 6 : ℝ) * ‖prawitzKernel (t / (12 / (5 * ρ)))‖ *
        prawitzDiscrepancyEnvelope ρ t ≤
      (1 / (Real.pi * a) + 5 * s / 12) *
        min ((b ^ 3 / 6 + s * b ^ 4 / 8) *
          Real.exp (-(a ^ 2 / 4) + s * b ^ 3 / 10))
          ((min 1 (Real.exp (-(a ^ 2 / 2) + s * b ^ 3 / 5)) +
            Real.exp (-(a ^ 2 / 2))) / r) := by
  have hρ : 0 < ρ := hr.trans_le hrρ
  have hs : 0 < s := hρ.trans_le hρs
  have ht : 0 < t := ha.trans_le hat
  have hb : 0 < b := ht.trans_le htb
  have hU : 0 < 12 / (5 * ρ) := by positivity
  have hfreq : 0 < t / (12 / (5 * ρ)) := div_pos ht hU
  have hfreq1 : t / (12 / (5 * ρ)) ≤ 1 := (div_le_one hU).2 htU
  have hk := prawitzKernel_norm_le (t / (12 / (5 * ρ)))
    (by simpa only [abs_of_pos hfreq] using hfreq)
    (by simpa only [abs_of_pos hfreq] using hfreq1)
  rw [abs_of_pos hfreq] at hk
  have hk' : (5 / 6 : ℝ) * ‖prawitzKernel (t / (12 / (5 * ρ)))‖ * ρ ≤
      1 / (Real.pi * a) + 5 * s / 12 := by
    calc
      _ ≤ (5 / 6 : ℝ) * (1 / (2 * Real.pi * (t / (12 / (5 * ρ)))) +
          1 / 2) * ρ := by gcongr
      _ = 1 / (Real.pi * t) + 5 * ρ / 12 := by field_simp; norm_num
      _ ≤ _ := by gcongr
  let T := (b ^ 3 / 6 + s * b ^ 4 / 8) *
    Real.exp (-(a ^ 2 / 4) + s * b ^ 3 / 10)
  let S := (min 1 (Real.exp (-(a ^ 2 / 2) + s * b ^ 3 / 5)) +
    Real.exp (-(a ^ 2 / 2))) / r
  have hT : (t ^ 3 / 6 + ρ * t ^ 4 / 8) *
      Real.exp (-(t ^ 2 / 4) + ρ * t ^ 3 / 10) ≤ T := by
    dsimp [T]
    gcongr
  have hM : prawitzMomentEnvelope ρ t + Real.exp (-(t ^ 2 / 2)) ≤
      min 1 (Real.exp (-(a ^ 2 / 2) + s * b ^ 3 / 5)) +
        Real.exp (-(a ^ 2 / 2)) := by
    unfold prawitzMomentEnvelope
    rw [abs_of_pos ht]
    gcongr
  have hd : prawitzDiscrepancyEnvelope ρ t / ρ ≤ min T S := by
    apply le_min
    · apply (div_le_iff₀ hρ).2
      calc
        _ ≤ (ρ * t ^ 3 / 6 + ρ ^ 2 * t ^ 4 / 8) *
            Real.exp (-(t ^ 2 / 4) + ρ * t ^ 3 / 10) := by
          unfold prawitzDiscrepancyEnvelope
          rw [abs_of_pos ht]
          exact min_le_left _ _
        _ = ((t ^ 3 / 6 + ρ * t ^ 4 / 8) *
            Real.exp (-(t ^ 2 / 4) + ρ * t ^ 3 / 10)) * ρ := by ring
        _ ≤ T * ρ := mul_le_mul_of_nonneg_right hT hρ.le
    · calc
        _ ≤ (prawitzMomentEnvelope ρ t + Real.exp (-(t ^ 2 / 2))) / ρ :=
          div_le_div_of_nonneg_right (min_le_right _ _) hρ.le
        _ ≤ S := by dsimp [S]; gcongr
  have hd0 : 0 ≤ prawitzDiscrepancyEnvelope ρ t / ρ := by
    unfold prawitzDiscrepancyEnvelope prawitzMomentEnvelope
    positivity
  calc
    _ = ((5 / 6 : ℝ) * ‖prawitzKernel (t / (12 / (5 * ρ)))‖ * ρ) *
        (prawitzDiscrepancyEnvelope ρ t / ρ) := by field_simp
    _ ≤ (1 / (Real.pi * a) + 5 * s / 12) * min T S :=
      mul_le_mul hk' hd hd0 (by positivity)

/-- On [an initial frequency interval inside the kernel band](hyp:a,ha,haU)
and [a positive parameter cell with nonpositive Taylor exponent](hyp:ρ,s,hρ,hρs,hsa),
the [normalized integral has a polynomial bound at its singular endpoint](goal). -/
theorem prawitz_low_compact_initial_integral_bound
    (ρ s a : ℝ) (hρ : 0 < ρ) (hρs : ρ ≤ s) (ha : 0 ≤ a)
    (haU : a ≤ 12 / (5 * ρ)) (hsa : s * a ≤ 5 / 2) :
    (5 / 6 : ℝ) * (∫ t in (0 : ℝ)..a,
      ‖prawitzKernel (t / (12 / (5 * ρ)))‖ * prawitzDiscrepancyEnvelope ρ t) ≤
      (1 / Real.pi + 5 * s * a / 12) * (1 / 6 + s * a / 8) * a ^ 3 / 3 := by
  have hs : 0 ≤ s := hρ.le.trans hρs
  have hU : 0 < 12 / (5 * ρ) := by positivity
  let C : ℝ := (1 / Real.pi + 5 * s * a / 12) * (1 / 6 + s * a / 8)
  have hi := prawitz_low_compact_intervalIntegrable ρ (12 / (5 * ρ)) a
    hρ.le hU ha haU
  have hpoly : IntervalIntegrable (fun t : ℝ => C * t ^ 2) volume 0 a :=
    (by fun_prop : Continuous (fun t : ℝ => C * t ^ 2)).intervalIntegrable 0 a
  rw [← intervalIntegral.integral_const_mul]
  calc
    _ ≤ ∫ t in (0 : ℝ)..a, C * t ^ 2 := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo ha (hi.const_mul _) hpoly
      intro t ht
      have ht0 : 0 < t := ht.1
      have hta : t ≤ a := ht.2.le
      have htU : t ≤ 12 / (5 * ρ) := hta.trans haU
      have hf : 0 < t / (12 / (5 * ρ)) := div_pos ht0 hU
      have hf1 : t / (12 / (5 * ρ)) ≤ 1 := (div_le_one hU).2 htU
      have hk := prawitzKernel_norm_le (t / (12 / (5 * ρ)))
        (by simpa only [abs_of_pos hf] using hf)
        (by simpa only [abs_of_pos hf] using hf1)
      rw [abs_of_pos hf] at hk
      have hρt : ρ * t ≤ 5 / 2 :=
        (mul_le_mul hρs hta ht0.le hs).trans hsa
      have he : Real.exp (-(t ^ 2 / 4) + ρ * t ^ 3 / 10) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        have hp := mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hρt)
        nlinarith
      have hd0 : 0 ≤ prawitzDiscrepancyEnvelope ρ t := by
        unfold prawitzDiscrepancyEnvelope prawitzMomentEnvelope
        positivity
      have hd : prawitzDiscrepancyEnvelope ρ t ≤
          ρ * t ^ 3 / 6 + ρ ^ 2 * t ^ 4 / 8 := by
        calc
          _ ≤ (ρ * t ^ 3 / 6 + ρ ^ 2 * t ^ 4 / 8) *
              Real.exp (-(t ^ 2 / 4) + ρ * t ^ 3 / 10) := by
            simpa only [prawitzDiscrepancyEnvelope, abs_of_pos ht0] using
              min_le_left
                ((ρ * |t| ^ 3 / 6 + ρ ^ 2 * t ^ 4 / 8) *
                  Real.exp (-(t ^ 2 / 4) + ρ * |t| ^ 3 / 10))
                (prawitzMomentEnvelope ρ t + Real.exp (-(t ^ 2 / 2)))
          _ ≤ _ := mul_le_of_le_one_right (by positivity) he
      calc
        _ ≤ (5 / 6 : ℝ) *
            (1 / (2 * Real.pi * (t / (12 / (5 * ρ)))) + 1 / 2) *
            (ρ * t ^ 3 / 6 + ρ ^ 2 * t ^ 4 / 8) := by
          simpa only [mul_assoc] using
            mul_le_mul (mul_le_mul_of_nonneg_left hk (by norm_num : (0 : ℝ) ≤ 5 / 6))
              hd hd0 (by positivity)
        _ = (1 / Real.pi + 5 * ρ * t / 12) *
            (1 / 6 + ρ * t / 8) * t ^ 2 := by
          field_simp
          ring
        _ ≤ C * t ^ 2 := by dsimp [C]; gcongr
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      dsimp [C]
      norm_num
      ring

/-- On [positive parameter and frequency cells inside the kernel
band](hyp:ρ,r,s,a,b,hr,hrρ,hρs,ha,hab,hbU),
the [normalized cell integral is bounded using the better envelope branch](goal). -/
theorem prawitz_low_compact_cell_integral_bound
    (ρ r s a b : ℝ) (hr : 0 < r) (hrρ : r ≤ ρ) (hρs : ρ ≤ s)
    (ha : 0 < a) (hab : a ≤ b) (hbU : b ≤ 12 / (5 * ρ)) :
    (5 / 6 : ℝ) * (∫ t in a..b,
      ‖prawitzKernel (t / (12 / (5 * ρ)))‖ * prawitzDiscrepancyEnvelope ρ t) ≤
      (b - a) * (1 / (Real.pi * a) + 5 * s / 12) *
        min ((b ^ 3 / 6 + s * b ^ 4 / 8) *
          Real.exp (-(a ^ 2 / 4) + s * b ^ 3 / 10))
          ((min 1 (Real.exp (-(a ^ 2 / 2) + s * b ^ 3 / 5)) +
            Real.exp (-(a ^ 2 / 2))) / r) := by
  have hρ : 0 < ρ := hr.trans_le hrρ
  have hU : 0 < 12 / (5 * ρ) := by positivity
  have hib := prawitz_low_compact_intervalIntegrable ρ (12 / (5 * ρ)) b
    hρ.le hU (ha.le.trans hab) hbU
  have hia := prawitz_low_compact_intervalIntegrable ρ (12 / (5 * ρ)) a
    hρ.le hU ha.le (hab.trans hbU)
  have hi := hia.symm.trans hib
  rw [← intervalIntegral.integral_const_mul]
  calc
    _ ≤ ∫ _t in a..b,
        (1 / (Real.pi * a) + 5 * s / 12) *
          min ((b ^ 3 / 6 + s * b ^ 4 / 8) *
            Real.exp (-(a ^ 2 / 4) + s * b ^ 3 / 10))
            ((min 1 (Real.exp (-(a ^ 2 / 2) + s * b ^ 3 / 5)) +
              Real.exp (-(a ^ 2 / 2))) / r) := by
      apply intervalIntegral.integral_mono_on hab (hi.const_mul _)
        intervalIntegrable_const
      intro t ht
      simpa only [mul_assoc] using
        prawitz_low_compact_cell_bound ρ r s t a b hr hrρ hρs ha
          ht.1 ht.2 (ht.2.trans hbU)
    _ = _ := by rw [intervalIntegral.integral_const]; ring

set_option maxRecDepth 4096 in
/-- For [a moment ratio ρ above one hundredth and below one](hyp:ρ,hlarge,hρ1),
with cutoffs U0 = max(3/2, √(4 log(1/ρ))) and U = 12/(5ρ),
[the low-frequency Prawitz contribution (2/U)·∫ over [0, U0] of the Prawitz
filter magnitude at t/U times the minimum discrepancy envelope is at most one
quarter of ρ](goal). -/
theorem prawitz_budget_low_compact
    (ρ : ℝ) (hlarge : 1 / 100 < ρ) (hρ1 : ρ < 1) :
    let U0 := max (3 / 2 : ℝ) (Real.sqrt (4 * Real.log (1 / ρ)))
    let U := 12 / (5 * ρ)
    (2 / U) * (∫ t in (0 : ℝ)..U0,
      ‖prawitzKernel (t / U)‖ * prawitzDiscrepancyEnvelope ρ t) ≤ ρ / 4 := by
  /- Round 9 ground truth: every analytic and rational prerequisite below
  is proved. This is now an integral assembly, not a new numerical search.

  Locate rho with prawitz_compact_parameter_cell_exists and write
  r=left(j), s=right(j), K=lowCutoffIndex(j), B=K/200, U=12/(5*rho).
  The cutoff certificate gives 0<r<s<=1 and 300<=K<=859. The real cutoff
  adapter gives U0<=B<=U. Use the low interval-integrability helper on
  [0,B]; nonnegativity of the discrepancy envelope justifies extending
  the integral from U0 to B (integral_mono_interval or adjacent integrals).

  Split [0,B] into [0,1/200] and the cells indexed by Finset.Ico 1 K,
  using intervalIntegral.sum_integral_adjacent_intervals_Ico with
  endpoints a(i)=(i:Real)/200. Integrability for each cell follows by
  restricting the proved integrability on [0,B]. The initial integral
  bound and prawitz_low_real_initial_enclosure compare the normalized
  (5/6)*integral to prawitzRationalLowInitial. For positive cells use
  prawitz_low_compact_endpoint_cell_integral_bound, then the CLOSED
  prawitz_low_real_cell_enclosure; the older independent-endpoint cell
  bound above is too loose for the unchanged table. Keep the maximum
  endpoint cubic exponent and the minimum discrepancy branch.

  Enclose each rational entry by prawitzRoundUp via Int.le_ceil, cast
  the sum, and apply prawitz_low_rational_sum_certificate j (<=1/4).
  Finally 2/U=5*rho/6 converts the normalized integral bound to rho/4.
  Do not modify tables, cutoffs, constants, rates, or hypotheses; do not
  import either full budget or BerryEsseenUnit. This file is independent
  of the high compact assembly. New private proof helpers may live here.
  -/
  dsimp only
  have hρ : 0 < ρ := by linarith
  obtain ⟨j, hrρ, hρs⟩ :=
    prawitz_compact_parameter_cell_exists ρ hlarge.le hρ1.le
  rcases prawitz_compact_cutoff_rational_certificate j with
    ⟨hrQ, hrsQ, hsQ, hK, _, _, _, _, _, _⟩
  let r : ℝ := prawitzCompactLeft j.val
  let s : ℝ := prawitzCompactRight j.val
  let K := prawitzLowCutoffIndex j.val
  let a : ℕ → ℝ := fun i => (i : ℝ) / 200
  let U := 12 / (5 * ρ)
  let U0 := max (3 / 2 : ℝ) (Real.sqrt (4 * Real.log (1 / ρ)))
  let f : ℝ → ℝ := fun t =>
    ‖prawitzKernel (t / U)‖ * prawitzDiscrepancyEnvelope ρ t
  have hr : 0 < r := by
    dsimp only [r]
    exact_mod_cast hrQ
  have hs : s ≤ 1 := by
    dsimp only [s]
    exact_mod_cast hsQ
  have hK1 : 1 ≤ K := by dsimp [K]; omega
  have hU : 0 < U := by dsimp [U]; positivity
  have hU00 : 0 ≤ U0 := by
    dsimp [U0]
    exact le_trans (by norm_num) (le_max_left _ _)
  obtain ⟨hU0B, hBU, _⟩ := prawitz_compact_real_cutoff_enclosures j ρ hrρ hρs
  change U0 ≤ a K at hU0B
  change a K ≤ U at hBU
  have ha0 (i : ℕ) : 0 ≤ a i := by dsimp [a]; positivity
  have hamono {i k : ℕ} (hik : i ≤ k) : a i ≤ a k := by
    dsimp [a]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hik) (by norm_num)
  have hiB : IntervalIntegrable f volume 0 (a K) :=
    prawitz_low_compact_intervalIntegrable ρ U (a K) hρ.le hU (ha0 K) hBU
  have higrid (i : ℕ) (hi : i ≤ K) : IntervalIntegrable f volume 0 (a i) :=
    prawitz_low_compact_intervalIntegrable ρ U (a i) hρ.le hU (ha0 i)
      ((hamono hi).trans hBU)
  have hf0 (t : ℝ) : 0 ≤ f t := by
    dsimp [f]
    apply mul_nonneg (norm_nonneg _)
    unfold prawitzDiscrepancyEnvelope prawitzMomentEnvelope
    positivity
  have hext : (∫ t in (0 : ℝ)..U0, f t) ≤ ∫ t in (0 : ℝ)..a K, f t :=
    intervalIntegral.integral_mono_interval le_rfl hU00 hU0B
      (Filter.Eventually.of_forall hf0) hiB
  have hinitial : (5 / 6 : ℝ) * (∫ t in (0 : ℝ)..a 1, f t) ≤
      (prawitzRoundUp (prawitzRationalLowInitial j.val) : ℝ) := by
    have haU : (1 / 200 : ℝ) ≤ U := by
      simpa only [a, Nat.cast_one] using (hamono hK1).trans hBU
    have hsa : s * (1 / 200 : ℝ) ≤ 5 / 2 := by nlinarith [hs]
    simpa only [a, Nat.cast_one, f, U] using
      (prawitz_low_compact_initial_integral_bound ρ s (1 / 200)
      hρ hρs (by norm_num) haU hsa).trans
      ((prawitz_low_real_initial_enclosure j).trans
        (Rat.cast_le.mpr (prawitz_le_roundUp _)))
  have hcells (i : ℕ) (hi : i ∈ Finset.Ico 1 K) :
      (5 / 6 : ℝ) * (∫ t in a i..a (i + 1), f t) ≤
        (prawitzRoundUp (prawitzRationalLowCell j.val i) : ℝ) := by
    have hi1 := (Finset.mem_Ico.mp hi).1
    have hiK : i + 1 ≤ K := by have := (Finset.mem_Ico.mp hi).2; omega
    have hai : 0 < a i := by dsimp [a]; positivity
    exact (prawitz_low_compact_endpoint_cell_integral_bound ρ r s (a i) (a (i + 1))
      hr hrρ hρs hai (hamono (by omega)) ((hamono hiK).trans hBU)).trans
      ((prawitz_low_real_cell_enclosure j i hi).trans
        (Rat.cast_le.mpr (prawitz_le_roundUp _)))
  have htel : (∑ i ∈ Finset.Ico 1 K, ∫ t in a i..a (i + 1), f t) =
      ∫ t in a 1..a K, f t := by
    apply intervalIntegral.sum_integral_adjacent_intervals_Ico hK1
    intro i hi
    have hiK : i + 1 ≤ K := by have := hi.2; omega
    exact (higrid i (by omega)).symm.trans (higrid (i + 1) hiK)
  have hsplit : (∫ t in (0 : ℝ)..a K, f t) =
      (∫ t in (0 : ℝ)..a 1, f t) +
        ∑ i ∈ Finset.Ico 1 K, ∫ t in a i..a (i + 1), f t := by
    rw [htel]
    exact (intervalIntegral.integral_add_adjacent_intervals
      (higrid 1 hK1) ((higrid 1 hK1).symm.trans hiB)).symm
  have hnormalized : (5 / 6 : ℝ) * (∫ t in (0 : ℝ)..a K, f t) ≤ 1 / 4 := by
    calc
      _ = (5 / 6 : ℝ) * (∫ t in (0 : ℝ)..a 1, f t) +
          ∑ i ∈ Finset.Ico 1 K, (5 / 6 : ℝ) * (∫ t in a i..a (i + 1), f t) := by
        rw [hsplit, mul_add, Finset.mul_sum]
      _ ≤ (prawitzRoundUp (prawitzRationalLowInitial j.val) : ℝ) +
          ∑ i ∈ Finset.Ico 1 K,
            (prawitzRoundUp (prawitzRationalLowCell j.val i) : ℝ) :=
        add_le_add hinitial (Finset.sum_le_sum hcells)
      _ = (prawitzRationalLowSum j.val : ℝ) := by
        simp only [prawitzRationalLowSum, Rat.cast_add, Rat.cast_sum, K]
      _ ≤ 1 / 4 := by
        simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using
          (show (prawitzRationalLowSum j.val : ℝ) ≤ ((1 / 4 : ℚ) : ℝ) from
            Rat.cast_le.mpr (prawitz_low_rational_sum_certificate j))
  have hnormalized0 : (5 / 6 : ℝ) * (∫ t in (0 : ℝ)..U0, f t) ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_left hext (by norm_num)).trans hnormalized
  change (2 / U) * (∫ t in (0 : ℝ)..U0, f t) ≤ ρ / 4
  have hscale : 2 / U = ρ * (5 / 6) := by dsimp [U]; field_simp; ring
  rw [hscale, mul_assoc]
  calc
    _ ≤ ρ * (1 / 4) := mul_le_mul_of_nonneg_left hnormalized0 hρ.le
    _ = ρ / 4 := by ring

end Causalean.Stat.CLT.BerryEsseen

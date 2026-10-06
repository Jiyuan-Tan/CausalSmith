module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzBudgetCutoffs
public import Causalean.Stat.CLT.BerryEsseen.PrawitzCompactIntegrability
public import Causalean.Stat.CLT.BerryEsseen.PrawitzCompactKernelCells
public import Causalean.Stat.CLT.BerryEsseen.PrawitzCompactRealCutoffs
public import Causalean.Stat.CLT.BerryEsseen.PrawitzCutoffRationalCertificate
public import Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate
public import Causalean.Stat.CLT.BerryEsseen.PrawitzHighRealEnclosures
public import Causalean.Stat.CLT.BerryEsseen.PrawitzRescaledCells

/-! # High-frequency Prawitz allocation on the complementary ratio interval

This independent deterministic certificate keeps the cubic damping and the
actual kernel above ratio one hundredth. Combining it with the small-ratio
assembly proves the unchanged full high-frequency allocation.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- For [a moment ratio ρ above one hundredth and below one](hyp:ρ,hlarge,hρ1),
with cutoffs U0 = max(3/2, √(4 log(1/ρ))) and U = 12/(5ρ),
[the high-frequency Prawitz contribution (2/U)·∫ over [U0, U] of the Prawitz
filter magnitude times the moment envelope is at most three twentieths of
ρ](goal). -/
theorem prawitz_budget_high_compact
    (ρ : ℝ) (hlarge : 1 / 100 < ρ) (hρ1 : ρ < 1) :
    let U0 := max (3 / 2 : ℝ) (Real.sqrt (4 * Real.log (1 / ρ)))
    let U := 12 / (5 * ρ)
    (2 / U) * (∫ t in U0..U,
      ‖prawitzKernel (t / U)‖ * prawitzMomentEnvelope ρ t) ≤ 3 * ρ / 20 := by
  /- Round 9 ground truth: all real adapters and finite arithmetic
  certificates are CLOSED. Assemble the actual moving-band integral.

  Locate rho with prawitz_compact_parameter_cell_exists and set
  r=left(j), s=right(j), I=highCutoffIndex(j), A=I/1000, U=12/(5*rho).
  The cutoff certificate gives 0<r<s<=1 and 1<=I<1000; the real cutoff
  adapter gives U*A<=U0. prawitz_budget_cutoffs supplies U0<=U.
  The high interval-integrability helper applies on [U*A,U]. Extend
  the original integral down to U*A using nonnegativity. Telescope
  using intervalIntegral.sum_integral_adjacent_intervals_Ico with
  endpoints a(i)=U*((i:Real)/1000) and indices Finset.Ico I 1000.

  For each i use prawitz_high_rescaled_lower_cell_integral_bound if
  i<500 and prawitz_high_rescaled_upper_cell_integral_bound otherwise.
  The half-band is exactly the i=500 grid endpoint. Compose
  prawitz_high_real_kernel_square_enclosure with the CLOSED
  prawitz_kernel_rational_square_certificate, cast to Real, and use
  Real.sqrt_le_iff or Real.sqrt_le_sqrt to enclose sqrt(Q) by
  kernelMagnitudeIndex(i)/1000000 (nonnegative by its Nat type).
  Compose min_le_right with prawitz_high_real_exponential_enclosure.
  Since b-a=1/1000, the product casts exactly to prawitzRationalHighCell.

  Apply Int.le_ceil to outward-round every cell, cast and sum, then
  use prawitz_high_rational_sum_certificate j (raw integral <=9/50).
  Multiply by 2/U=5*rho/6 to obtain 3*rho/20. Retain cubic damping
  and the original assigned outer kernel value: the upper-cell proof
  already excludes t=U only almost everywhere. Do not modify tables,
  constants, cutoffs, or hypotheses; do not import either full budget
  or BerryEsseenUnit. This file is independent of the low assembly.
  New private proof helpers may live here.
  -/
  classical
  dsimp only
  let U := 12 / (5 * ρ)
  let U0 := max (3 / 2 : ℝ) (Real.sqrt (4 * Real.log (1 / ρ)))
  have hρ : 0 < ρ := by linarith
  have hU : 0 < U := by dsimp [U]; positivity
  obtain ⟨j, hrρ, hρs⟩ := prawitz_compact_parameter_cell_exists ρ hlarge.le hρ1.le
  let r : ℝ := prawitzCompactLeft j.val
  let s : ℝ := prawitzCompactRight j.val
  let I := prawitzHighCutoffIndex j.val
  let a (i : ℕ) : ℝ := (i : ℝ) / 1000
  let f (t : ℝ) := ‖prawitzKernel (t / U)‖ * prawitzMomentEnvelope ρ t
  have hc := prawitz_compact_cutoff_rational_certificate j
  have hr : 0 < r := by
    exact Rat.cast_pos.mpr hc.1
  have hI : 1 ≤ I := hc.2.2.2.2.2.1
  have hIlt : I < 1000 := hc.2.2.2.2.2.2.1
  have ha_pos (i : ℕ) (hi : 1 ≤ i) : 0 < a i := by
    dsimp [a]
    exact div_pos (by exact_mod_cast hi) (by norm_num)
  have ha_mono (i : ℕ) : a i ≤ a (i + 1) := by dsimp [a]; push_cast; linarith
  have ha_one (i : ℕ) (hi : i < 1000) : a (i + 1) ≤ 1 := by
    have hn : (i : ℝ) + 1 ≤ 1000 := by exact_mod_cast (by omega : i + 1 ≤ 1000)
    dsimp [a]; push_cast; linarith
  have hstart : U * a I ≤ U0 :=
    (prawitz_compact_real_cutoff_enclosures j ρ hrρ hρs).2.2
  have hend : U0 ≤ U := (prawitz_budget_cutoffs ρ hρ hρ1).2
  have hi_full := prawitz_high_compact_intervalIntegrable ρ U (U * a I) U hU
    (mul_pos hU (ha_pos I hI)) (hstart.trans hend) le_rfl
  have hi_cell (i : ℕ) (hi : i ∈ Finset.Ico I 1000) :
      IntervalIntegrable f volume (U * a i) (U * a (i + 1)) := by
    obtain ⟨hil, hiu⟩ := Finset.mem_Ico.mp hi
    exact prawitz_high_compact_intervalIntegrable ρ U _ _ hU
      (mul_pos hU (ha_pos i (hI.trans hil)))
      (mul_le_mul_of_nonneg_left (ha_mono i) hU.le)
      (by simpa using mul_le_mul_of_nonneg_left (ha_one i hiu) hU.le)
  have cell_bound (i : ℕ) (hi : i ∈ Finset.Ico I 1000) :
      (∫ t in (U * a i)..(U * a (i + 1)), f t) ≤
        (prawitzRationalHighCell j.val i : ℝ) := by
    obtain ⟨hil, hiu⟩ := Finset.mem_Ico.mp hi
    have hi' : i ∈ Finset.Ico 1 1000 := Finset.mem_Ico.mpr ⟨hI.trans hil, hiu⟩
    let Q := if i < 500 then
      (1 - a i) ^ 2 / 4 +
        (((1 - a i) * (1 - (Real.pi * a i) ^ 2 / 2 + (Real.pi * a (i + 1)) ^ 4 / 24) /
          (Real.pi * a i * (1 - (Real.pi * a (i + 1)) ^ 2 / 6)) + 1 / Real.pi) / 2) ^ 2
      else (1 - a i) ^ 2 / 4 + Real.pi ^ 2 * (1 - a i) ^ 4 / 16
    let E := max ((-72 * a i ^ 2 / 25 + 1728 * a i ^ 3 / 625) / s ^ 2)
      ((-72 * a (i + 1) ^ 2 / 25 + 1728 * a (i + 1) ^ 3 / 625) / s ^ 2)
    have hmag : 0 ≤ (prawitzKernelMagnitudeIndex i : ℝ) / 1000000 :=
      div_nonneg (Nat.cast_nonneg _) (by norm_num)
    have hk : Real.sqrt Q ≤ (prawitzKernelMagnitudeIndex i : ℝ) / 1000000 := by
      apply (Real.sqrt_le_left hmag).2
      have hsquare : (prawitzRationalKernelSq i : ℝ) ≤
          ((prawitzKernelMagnitudeIndex i : ℝ) / 1000000) ^ 2 := by
        have hh := Rat.cast_le (K := ℝ) |>.mpr (prawitz_kernel_rational_square_certificate i hi')
        simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hh
      exact (prawitz_high_real_kernel_square_enclosure i hi').trans hsquare
    let e : ℚ := min
      (72 * ((i : ℚ) / 1000) ^ 2 / 25 - 1728 * ((i : ℚ) / 1000) ^ 3 / 625)
      (72 * (((i + 1 : ℕ) : ℚ) / 1000) ^ 2 / 25 -
        1728 * (((i + 1 : ℕ) : ℚ) / 1000) ^ 3 / 625) /
      (prawitzCompactRight j.val) ^ 2
    have he : min 1 (Real.exp E) ≤ ((1 / prawitzTaylor16 e : ℚ) : ℝ) :=
      (min_le_right _ _).trans (prawitz_high_real_exponential_enclosure j i hi')
    have hraw : (∫ t in (U * a i)..(U * a (i + 1)), f t) ≤
        (12 / (5 * r)) * (a (i + 1) - a i) * Real.sqrt Q * min 1 (Real.exp E) := by
      by_cases hhalf : i < 500
      · have hb : a (i + 1) ≤ 1 / 2 := by
          have hn : (i : ℝ) + 1 ≤ 500 := by exact_mod_cast (by omega : i + 1 ≤ 500)
          dsimp [a]; push_cast; linarith
        simpa only [Q, if_pos hhalf] using
          prawitz_high_rescaled_lower_cell_integral_bound ρ r s (a i) (a (i + 1))
            hr hrρ hρs (ha_pos i (hI.trans hil)) (ha_mono i) hb
      · have ha : 1 / 2 ≤ a i := by
          have hn : (500 : ℝ) ≤ i := by exact_mod_cast (by omega : 500 ≤ i)
          dsimp [a]; linarith
        simpa only [Q, if_neg hhalf] using
          prawitz_high_rescaled_upper_cell_integral_bound ρ r s (a i) (a (i + 1))
            hr hrρ hρs ha (ha_mono i) (ha_one i hiu)
    have hwidth : a (i + 1) - a i = 1 / 1000 := by dsimp [a]; push_cast; ring
    calc
      _ ≤ _ := hraw
      _ ≤ (12 / (5 * r)) * (a (i + 1) - a i) *
          ((prawitzKernelMagnitudeIndex i : ℝ) / 1000000) *
          ((1 / prawitzTaylor16 e : ℚ) : ℝ) := by
        have hcoeff : 0 ≤ (12 / (5 * r)) * (a (i + 1) - a i) := by
          rw [hwidth]
          positivity
        apply mul_le_mul _ he (le_min (by norm_num) (Real.exp_pos E).le)
          (mul_nonneg hcoeff hmag)
        exact mul_le_mul_of_nonneg_left hk hcoeff
      _ = _ := by
        rw [hwidth]
        change (12 / (5 * r)) * (1 / 1000) *
          ((prawitzKernelMagnitudeIndex i : ℝ) / 1000000) *
          ((1 / prawitzTaylor16 e : ℚ) : ℝ) =
          (((12 / (5 * prawitzCompactLeft j.val)) * (1 / 1000) *
            ((prawitzKernelMagnitudeIndex i : ℚ) / 1000000) / prawitzTaylor16 e : ℚ) : ℝ)
        simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one]
        dsimp only [r]
        ring
  have hround (i : ℕ) : (prawitzRationalHighCell j.val i : ℝ) ≤
      (prawitzRoundUp (prawitzRationalHighCell j.val i) : ℝ) := by
    exact Rat.cast_le.mpr (prawitz_le_roundUp _)
  have hraw_total : (∫ t in U0..U, f t) ≤ 9 / 50 := by
    calc
      _ ≤ ∫ t in (U * a I)..U, f t := by
        apply intervalIntegral.integral_mono_interval hstart hend le_rfl _ hi_full
        exact Filter.Eventually.of_forall (fun t => mul_nonneg (norm_nonneg _)
          (by unfold prawitzMomentEnvelope; positivity))
      _ = ∑ i ∈ Finset.Ico I 1000, ∫ t in (U * a i)..(U * a (i + 1)), f t := by
        simpa only [a, Nat.cast_ofNat, div_self (by norm_num : (1000 : ℝ) ≠ 0), mul_one]
          using (intervalIntegral.sum_integral_adjacent_intervals_Ico
          (a := fun i => U * a i) hIlt.le
          (fun i hi => hi_cell i (Finset.mem_Ico.mpr hi))).symm
      _ ≤ ∑ i ∈ Finset.Ico I 1000,
          (prawitzRoundUp (prawitzRationalHighCell j.val i) : ℝ) :=
        Finset.sum_le_sum (fun i hi => (cell_bound i hi).trans (hround i))
      _ = (prawitzRationalHighSum j.val : ℝ) := by
        simp [prawitzRationalHighSum, I]
      _ ≤ 9 / 50 := by
        have hh := Rat.cast_le (K := ℝ) |>.mpr (prawitz_high_rational_sum_certificate j)
        simpa only [Rat.cast_div, Rat.cast_ofNat] using hh
  have hfactor : 2 / U = 5 * ρ / 6 := by dsimp [U]; field_simp; ring
  change (2 / U) * (∫ t in U0..U, f t) ≤ 3 * ρ / 20
  rw [hfactor]
  calc
    _ ≤ (5 * ρ / 6) * (9 / 50) := mul_le_mul_of_nonneg_left hraw_total (by positivity)
    _ = _ := by ring

end Causalean.Stat.CLT.BerryEsseen

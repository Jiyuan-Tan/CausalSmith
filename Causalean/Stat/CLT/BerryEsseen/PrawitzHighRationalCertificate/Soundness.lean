module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.Core
public import Mathlib.Tactic.FinCases

/-! # High Prawitz certificate: soundness of the integer cells

Identifies the integer cell arithmetic with the outward-rounded rational
high-frequency cells and the suffix recursion with the finite sum.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open Finset

private theorem highTaylor_fraction (n d : ℤ) (hd : d ≠ 0) :
    prawitzTaylor16 ((n : ℚ) / (d : ℚ)) =
      (highTaylorNum n d : ℚ) / ((1307674368000 * d ^ 15 : ℤ) : ℚ) := by
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  unfold highTaylorNum
  push_cast
  norm_num [prawitzTaylor16, Finset.sum_range_succ, Nat.factorial]
  field_simp
  ring

private def highExponent (j i : ℕ) : ℚ :=
  let a := (i : ℚ) / 1000
  let b := ((i + 1 : ℕ) : ℚ) / 1000
  min (72 * a ^ 2 / 25 - 1728 * a ^ 3 / 625)
    (72 * b ^ 2 / 25 - 1728 * b ^ 3 / 625) / (prawitzCompactRight j) ^ 2

private theorem highExponentDen_ne_zero (j : ℕ) : highExponentDen j ≠ 0 := by
  have hs : 0 < prawitzCompactRight j := by
    unfold prawitzCompactRight prawitzCompactLeft
    split_ifs <;> positivity
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ (Rat.num_ne_zero.mpr (ne_of_gt hs)))

private theorem highExponent_eq (j i : ℕ) :
    highExponent j i = (highExponentNum j i : ℚ) / (highExponentDen j : ℚ) := by
  have hc (k : ℕ) :
      72 * ((k : ℚ) / 1000) ^ 2 / 25 -
        1728 * ((k : ℚ) / 1000) ^ 3 / 625 = (highCubic k : ℚ) / 625000000000 := by
    unfold highCubic
    push_cast
    ring
  unfold highExponent
  dsimp only
  rw [hc, hc, min_div_div_right (by norm_num : (0 : ℚ) ≤ 625000000000)]
  unfold highExponentNum highExponentDen
  push_cast
  conv_lhs => rw [← Rat.num_div_den (prawitzCompactRight j)]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring_nf
  simp only [inv_inv]
  ring

private theorem highCeil_eq (n d : ℤ) :
    highCeil n d = ⌈(n : ℚ) / (d : ℚ)⌉ := by
  by_cases hd : 0 ≤ d
  · have ht := Int.toNat_of_nonneg hd
    have hc : (d.toNat : ℚ) = (d : ℚ) := by exact_mod_cast ht
    simpa only [highCeil, if_pos hd, ht, hc] using
      (Rat.ceil_intCast_div_natCast n d.toNat).symm
  · have ht := Int.toNat_of_nonneg (show 0 ≤ -d by omega)
    have hc : ((-d).toNat : ℚ) = (-d : ℤ) := by exact_mod_cast ht
    simpa only [highCeil, if_neg hd, ht, hc, Int.cast_neg,
      neg_neg, neg_div_neg_eq] using
      (Rat.ceil_intCast_div_natCast (-n) (-d).toNat).symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Checking this equality visits all 1,000 entries of the unchanged table.
private theorem highKernelFast_eq (i : ℕ) :
    highKernelFast i = prawitzKernelMagnitudeIndex i := by
  by_cases hi : i < 1000
  · have hblocks (b : Fin 32) (l : Fin 32) :
        highKernelFast (32 * b.val + l.val) =
          prawitzKernelMagnitudeIndex (32 * b.val + l.val) := by
      fin_cases b <;> fin_cases l <;> decide +kernel
    let b : Fin 32 := ⟨i / 32, by omega⟩
    let l : Fin 32 := ⟨i % 32, Nat.mod_lt _ (by decide)⟩
    have he : 32 * b.val + l.val = i := by
      dsimp [b, l]
      omega
    simpa only [he] using hblocks b l
  · simp only [highKernelFast, if_neg hi]

private theorem highCellInteger_eq (j i : ℕ) :
    highCellInteger j i = ⌈100000000 * prawitzRationalHighCell j i⌉ := by
  let r := prawitzCompactLeft j
  let e := highExponent j i
  let n := highExponentNum j i
  let d := highExponentDen j
  have he := highTaylor_fraction n d (highExponentDen_ne_zero j)
  rw [← highExponent_eq] at he
  unfold highCellInteger
  dsimp only
  rw [highKernelFast_eq, highCeil_eq]
  change ⌈((6 * (prawitzKernelMagnitudeIndex i : ℤ) * r.den *
    (1307674368000 * d ^ 15) : ℤ) : ℚ) / ((25 * r.num *
    highTaylorNum n d : ℤ) : ℚ)⌉ = _
  congr 1
  change _ = 100000000 * ((12 / (5 * r)) * (1 / 1000 : ℚ) *
    ((prawitzKernelMagnitudeIndex i : ℚ) / 1000000) / prawitzTaylor16 e)
  rw [he]
  conv_rhs => rw [← Rat.num_div_den r]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

private theorem highIntSuffix_sum (j n : ℕ) (hn : n ≤ 1000) :
    highIntSuffix j n = ∑ i ∈ Finset.Ico (1000 - n) 1000, highCellInteger j i := by
  induction n with
  | zero => simp [highIntSuffix]
  | succ n ih =>
    rw [highIntSuffix, ih (by omega),
      Finset.sum_eq_sum_Ico_succ_bot
        (a := 1000 - (n + 1)) (b := 1000) (by omega)]
    have hl : 1000 - (n + 1) = 999 - n := by omega
    have hu : 1000 - (n + 1) + 1 = 1000 - n := by omega
    rw [hl] at hu ⊢
    rw [hu, add_comm]

end Causalean.Stat.CLT.BerryEsseen

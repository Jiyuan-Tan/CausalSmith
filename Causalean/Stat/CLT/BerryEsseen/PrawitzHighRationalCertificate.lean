module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzCompactRationalData
public import Mathlib.Tactic.FinCases
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.IntegerPart00
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.IntegerPart01
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.IntegerPart02
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.IntegerPart03
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.IntegerPart04
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.IntegerPart05
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.IntegerPart06
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.IntegerPart07
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.IntegerPart08
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.IntegerPart09
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.IntegerPart10
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.IntegerPart11
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.IntegerPart12
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.IntegerPart13
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.IntegerPart14
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.IntegerPart15
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.IntegerPart16
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.IntegerPart17
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.IntegerPart18
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.KernelPart00
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.KernelPart01
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.KernelPart02
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.KernelPart03
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.Soundness

/-! # Finite rational certificates for the rescaled high Prawitz sum

The kernel square table is shared across parameter cells. The raw integral
sum retains endpoint cubic damping and the exact bandwidth proportional
to the lower parameter. Both obligations involve rational arithmetic only
and import neither compact allocation nor any open cutoff certificate.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open Finset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
/-- On [every positive kernel grid cell](hyp:i,hi),
[the rational squared kernel enclosure is bounded by the square of its
explicit outward integer magnitude enclosure](goal). -/
theorem prawitz_kernel_rational_square_certificate
    (i : ℕ) (hi : i ∈ Ico 1 1000) :
    prawitzRationalKernelSq i ≤
      ((prawitzKernelMagnitudeIndex i : ℚ) / 1000000) ^ 2 := by
  /- Finite rational arithmetic, no analytic norm calculation here. Unfold
  the explicit table and split indices below/above 500, then use checked
  norm_num/decide proofs. Every one of these 999 inequalities has passed
  an independent Python Fraction sanity check; that is NOT a Lean proof.
  Preserve the one-millionth magnitude rounding. At index 500 use the
  reflected upper polynomial, and leave the assigned outer kernel value
  unchanged: the later norm comparison excludes it only a.e. -/
  obtain ⟨hil, hiu⟩ := Finset.mem_Ico.mp hi
  have hblocks (b : Fin 20) (l : Fin 50) :
      prawitzRationalKernelSq (1 + 50 * b.val + l.val) ≤
        ((prawitzKernelMagnitudeIndex (1 + 50 * b.val + l.val) : ℚ) / 1000000) ^ 2 := by
    fin_cases b
    · exact kernelSquare_block00 l
    · exact kernelSquare_block01 l
    · exact kernelSquare_block02 l
    · exact kernelSquare_block03 l
    · exact kernelSquare_block04 l
    · exact kernelSquare_block05 l
    · exact kernelSquare_block06 l
    · exact kernelSquare_block07 l
    · exact kernelSquare_block08 l
    · exact kernelSquare_block09 l
    · exact kernelSquare_block10 l
    · exact kernelSquare_block11 l
    · exact kernelSquare_block12 l
    · exact kernelSquare_block13 l
    · exact kernelSquare_block14 l
    · exact kernelSquare_block15 l
    · exact kernelSquare_block16 l
    · exact kernelSquare_block17 l
    · exact kernelSquare_block18 l
    · exact kernelSquare_block19 l
  let b : Fin 20 := ⟨(i - 1) / 50, by omega⟩
  let l : Fin 50 := ⟨(i - 1) % 50, Nat.mod_lt _ (by decide)⟩
  have he : 1 + 50 * b.val + l.val = i := by
    dsimp [b, l]
    omega
  simpa only [he] using hblocks b l

/-- On [each of the 270 explicit compact parameter cells](hyp:j),
[the complete outward-rounded raw high-frequency rational sum is at most nine
fiftieths](goal), which gives the original three-twentieths allocation. -/
theorem prawitz_high_rational_sum_certificate (j : Fin 270) :
    prawitzRationalHighSum j.val ≤ (9 / 50 : ℚ) := by
  /- Lowest open layer: EXACT finite rational sums only. Rounding UP to
  a common denominator makes the total an integer bound. Generate checked
  blockwise certificates if computing a full row is expensive; do not use
  native_decide, new axioms, or assumptions asserting this total.
  Exploratory DOUBLE arithmetic found a maximum about 0.177099 near
  rho=0.565 before rounding. Up to 999 outward cell roundings add less
  than 0.00000999. This supplies a feasibility check, NOT a proof.

  Later assembly: the cutoff certificate gives U*I/1000<=U0. Extend
  the nonnegative integral down to U*I/1000 and partition through U.
  Apply the two proved PrawitzRescaledCells integrals, switching at
  i=500. Use the rational pi bounds and the square certificate to
  enclose their Real.sqrt factors by the integer table. The denominator
  in the lower kernel formula is positive throughout b<=1/2; compare
  its numerator using pi>=314159/100000 and pi<=314160/100000. The
  endpoint negative cubic exponent is exactly -e, so the reciprocal
  Taylor comparison gives each displayed rational cell. Summing and
  multiplying by 5*rho/6 gives <=3*rho/20. This numerical leaf is
  independent of the cutoff and integral adapters. -/
  have hblocks (b : Fin 27) (l : Fin 10) :
      highIntSuffix (10 * b.val + l.val)
        (1000 - prawitzHighCutoffIndex (10 * b.val + l.val)) ≤ 18000000 := by
    fin_cases b
    · exact highInteger_block00 l
    · exact highInteger_block01 l
    · exact highInteger_block02 l
    · exact highInteger_block03 l
    · exact highInteger_block04 l
    · exact highInteger_block05 l
    · exact highInteger_block06 l
    · exact highInteger_block07 l
    · exact highInteger_block08 l
    · exact highInteger_block09 l
    · exact highInteger_block10 l
    · exact highInteger_block11 l
    · exact highInteger_block12 l
    · exact highInteger_block13 l
    · exact highInteger_block14 l
    · exact highInteger_block15 l
    · exact highInteger_block16 l
    · exact highInteger_block17 l
    · exact highInteger_block18 l
    · exact highInteger_block19 l
    · exact highInteger_block20 l
    · exact highInteger_block21 l
    · exact highInteger_block22 l
    · exact highInteger_block23 l
    · exact highInteger_block24 l
    · exact highInteger_block25 l
    · exact highInteger_block26 l
  let b : Fin 27 := ⟨j.val / 10, by omega⟩
  let l : Fin 10 := ⟨j.val % 10, Nat.mod_lt _ (by decide)⟩
  have hj : 10 * b.val + l.val = j.val := by
    dsimp [b, l]
    omega
  have h := hblocks b l
  rw [hj] at h
  have hcut : ∀ k : Fin 270, prawitzHighCutoffIndex k.val ≤ 1000 := by
    decide +kernel
  have hk := hcut j
  rw [highIntSuffix_sum _ _ (by omega), Nat.sub_sub_self hk] at h
  simp only [highCellInteger_eq] at h
  have hc : ((∑ i ∈ Ico (prawitzHighCutoffIndex j.val) 1000,
      ⌈100000000 * prawitzRationalHighCell j.val i⌉ : ℤ) : ℚ) ≤ 18000000 := by
    exact_mod_cast h
  push_cast at hc
  unfold prawitzRationalHighSum prawitzRoundUp
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  linarith

end Causalean.Stat.CLT.BerryEsseen

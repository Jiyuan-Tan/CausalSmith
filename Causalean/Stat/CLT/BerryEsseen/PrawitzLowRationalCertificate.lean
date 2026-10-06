module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzCompactRationalData
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Core
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Part00
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Part01
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Part02
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Part03
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Part04
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Part05
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Part06
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Part07
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Part08

/-! # Finite rational certificate for the normalized low Prawitz sum

This arithmetic leaf certifies every parameter cell, including the switch
between the two discrepancy branches. It imports no admitted cutoff,
integral allocation, smoothing comparison, or Berry--Esseen theorem.
The sum includes the initial singularity enclosure and all adjacent cells;
its normalization is 5/6 times the raw low integral, so its target is 1/4.
Unreduced integer fractions avoid repeated normalization of large Taylor
numerators; proved evaluation identities preserve the exact rounded cells.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

set_option maxRecDepth 1000000

/-- On [each of the explicit compact parameter cells](hyp:j),
[the complete outward-rounded rational low-frequency sum is at most
one quarter](goal). -/
theorem prawitz_low_rational_sum_certificate (j : Fin 270) :
    prawitzRationalLowSum j.val ≤ (1 / 4 : ℚ) := by
  /- Lowest open layer: EXACT finite rational sums only. Every cell is
  rounded UP to a common denominator of 10^8, so the sum is an integer
  comparison after multiplying by that denominator. Generate checked
  upper integer bounds for blocks of cells if full reduction is expensive.
  Reuse the defined polynomial; no Real.exp/log/sqrt or integration is
  needed in this file. Kernel-checked norm_num/decide certificates are
  acceptable; native_decide and extra axioms are not. Exploratory DOUBLE
  arithmetic reported a maximum about 0.247515 near rho=0.235 before
  rounding (<=859 cells add less than 0.00000859). This is sanity guidance,
  not a proof. Preserve every table, term, minimum, and rounding direction.

  Later assembly: locate rho in one of the 270 contiguous parameter cells,
  use the cutoff certificate to extend the nonnegative low integral to
  B=K/200<=U, and split with sum_integral_adjacent_intervals. Apply
  prawitz_low_compact_initial_integral_bound to [0,1/200] and
  prawitz_low_compact_endpoint_cell_integral_bound thereafter. Replace
  1/pi by 100000/314159, exp(-e/2) and exp(-e) by reciprocal Taylor
  bounds, and each resulting rational by its outward rounding. This
  leaf proves its numerical total; it is never an assumption on a law. -/
  have hblocks (b : Fin 27) (l : Fin 10) :
      (⌈100000000 * prawitzRationalLowInitial (10 * b.val + l.val)⌉ +
        ∑ i ∈ Finset.Ico 1 (prawitzLowCutoffIndex (10 * b.val + l.val)),
          ⌈100000000 * prawitzRationalLowCell (10 * b.val + l.val) i⌉ : ℤ) ≤ 25000000 := by
    fin_cases b
    · simpa only [lowIntPrefix_cutoff, lowCellInteger_eq] using lowInteger_block00 l
    · simpa only [lowIntPrefix_cutoff, lowCellInteger_eq] using lowInteger_block01 l
    · simpa only [lowIntPrefix_cutoff, lowCellInteger_eq] using lowInteger_block02 l
    · simpa only [lowIntPrefix_cutoff, lowCellInteger_eq] using lowInteger_block03 l
    · simpa only [lowIntPrefix_cutoff, lowCellInteger_eq] using lowInteger_block04 l
    · simpa only [lowIntPrefix_cutoff, lowCellInteger_eq] using lowInteger_block05 l
    · simpa only [lowIntPrefix_cutoff, lowCellInteger_eq] using lowInteger_block06 l
    · simpa only [lowIntPrefix_cutoff, lowCellInteger_eq] using lowInteger_block07 l
    · simpa only [lowIntPrefix_cutoff, lowCellInteger_eq] using lowInteger_block08 l
    · simpa only [lowIntPrefix_cutoff, lowCellInteger_eq] using lowInteger_block09 l
    · simpa only [lowIntPrefix_cutoff, lowCellInteger_eq] using lowInteger_block10 l
    · simpa only [lowIntPrefix_cutoff, lowCellInteger_eq] using lowInteger_block11 l
    · simpa only [lowIntPrefix_cutoff, lowCellInteger_eq] using lowInteger_block12 l
    · simpa only [lowIntPrefix_cutoff, lowCellInteger_eq] using lowInteger_block13 l
    · simpa only [lowIntPrefix_cutoff, lowCellInteger_eq] using lowInteger_block14 l
    · simpa only [lowIntPrefix_cutoff, lowCellInteger_eq] using lowInteger_block15 l
    · simpa only [lowIntPrefix_cutoff, lowCellInteger_eq] using lowInteger_block16 l
    · simpa only [lowIntPrefix_cutoff, lowCellInteger_eq] using lowInteger_block17 l
    · simpa only [lowIntPrefix_cutoff, lowCellInteger_eq] using lowInteger_block18 l
    · simpa only [lowIntPrefix_cutoff, lowCellInteger_eq] using lowInteger_block19 l
    · simpa only [lowIntPrefix_cutoff, lowCellInteger_eq] using lowInteger_block20 l
    · simpa only [lowIntPrefix_cutoff, lowCellInteger_eq] using lowInteger_block21 l
    · simpa only [lowIntPrefix_cutoff, lowCellInteger_eq] using lowInteger_block22 l
    · simpa only [lowIntPrefix_cutoff, lowCellInteger_eq] using lowInteger_block23 l
    · simpa only [lowIntPrefix_cutoff, lowCellInteger_eq] using lowInteger_block24 l
    · simpa only [lowIntPrefix_cutoff, lowCellInteger_eq] using lowInteger_block25 l
    · simpa only [lowIntPrefix_cutoff, lowCellInteger_eq] using lowInteger_block26 l
  let b : Fin 27 := ⟨j.val / 10, by omega⟩
  let l : Fin 10 := ⟨j.val % 10, Nat.mod_lt _ (by decide)⟩
  have hj : 10 * b.val + l.val = j.val := by
    dsimp [b, l]
    omega
  have h := hblocks b l
  rw [hj] at h
  have hc : ((⌈100000000 * prawitzRationalLowInitial (j.val)⌉ +
      ∑ i ∈ Finset.Ico 1 (prawitzLowCutoffIndex (j.val)),
        ⌈100000000 * prawitzRationalLowCell (j.val) i⌉ : ℤ) : ℚ) ≤ 25000000 := by
    exact_mod_cast h
  push_cast at hc
  unfold prawitzRationalLowSum prawitzRoundUp
  simp only [div_eq_mul_inv, ← Finset.sum_mul, ← add_mul]
  linarith

end Causalean.Stat.CLT.BerryEsseen

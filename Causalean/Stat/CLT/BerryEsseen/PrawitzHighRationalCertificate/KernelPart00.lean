module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzCompactRationalData
public import Mathlib.Tactic.FinCases

/-! # High Prawitz certificate: checked kernel-square blocks 0 through 4

Kernel-checked squared-kernel enclosures for grid cells 1 through 250.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open Finset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem kernelSquare_block00 (l : Fin 50) :
    prawitzRationalKernelSq (1 + l.val) ≤
      ((prawitzKernelMagnitudeIndex (1 + l.val) : ℚ) / 1000000) ^ 2 := by
  fin_cases l <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem kernelSquare_block01 (l : Fin 50) :
    prawitzRationalKernelSq (51 + l.val) ≤
      ((prawitzKernelMagnitudeIndex (51 + l.val) : ℚ) / 1000000) ^ 2 := by
  fin_cases l <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem kernelSquare_block02 (l : Fin 50) :
    prawitzRationalKernelSq (101 + l.val) ≤
      ((prawitzKernelMagnitudeIndex (101 + l.val) : ℚ) / 1000000) ^ 2 := by
  fin_cases l <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem kernelSquare_block03 (l : Fin 50) :
    prawitzRationalKernelSq (151 + l.val) ≤
      ((prawitzKernelMagnitudeIndex (151 + l.val) : ℚ) / 1000000) ^ 2 := by
  fin_cases l <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem kernelSquare_block04 (l : Fin 50) :
    prawitzRationalKernelSq (201 + l.val) ≤
      ((prawitzKernelMagnitudeIndex (201 + l.val) : ℚ) / 1000000) ^ 2 := by
  fin_cases l <;> decide +kernel

end Causalean.Stat.CLT.BerryEsseen

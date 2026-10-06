module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzCompactRationalData
public import Mathlib.Tactic.FinCases

/-! # High Prawitz certificate: checked kernel-square blocks 15 through 19

Kernel-checked squared-kernel enclosures for grid cells 751 through 1000.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open Finset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem kernelSquare_block15 (l : Fin 50) :
    prawitzRationalKernelSq (751 + l.val) ≤
      ((prawitzKernelMagnitudeIndex (751 + l.val) : ℚ) / 1000000) ^ 2 := by
  fin_cases l <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem kernelSquare_block16 (l : Fin 50) :
    prawitzRationalKernelSq (801 + l.val) ≤
      ((prawitzKernelMagnitudeIndex (801 + l.val) : ℚ) / 1000000) ^ 2 := by
  fin_cases l <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem kernelSquare_block17 (l : Fin 50) :
    prawitzRationalKernelSq (851 + l.val) ≤
      ((prawitzKernelMagnitudeIndex (851 + l.val) : ℚ) / 1000000) ^ 2 := by
  fin_cases l <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem kernelSquare_block18 (l : Fin 50) :
    prawitzRationalKernelSq (901 + l.val) ≤
      ((prawitzKernelMagnitudeIndex (901 + l.val) : ℚ) / 1000000) ^ 2 := by
  fin_cases l <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem kernelSquare_block19 (l : Fin 50) :
    prawitzRationalKernelSq (951 + l.val) ≤
      ((prawitzKernelMagnitudeIndex (951 + l.val) : ℚ) / 1000000) ^ 2 := by
  fin_cases l <;> decide +kernel

end Causalean.Stat.CLT.BerryEsseen

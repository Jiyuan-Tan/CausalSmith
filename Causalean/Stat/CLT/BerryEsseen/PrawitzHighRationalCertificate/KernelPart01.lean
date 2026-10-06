module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzCompactRationalData
public import Mathlib.Tactic.FinCases

/-! # High Prawitz certificate: checked kernel-square blocks 5 through 9

Kernel-checked squared-kernel enclosures for grid cells 251 through 500.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open Finset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem kernelSquare_block05 (l : Fin 50) :
    prawitzRationalKernelSq (251 + l.val) ≤
      ((prawitzKernelMagnitudeIndex (251 + l.val) : ℚ) / 1000000) ^ 2 := by
  fin_cases l <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem kernelSquare_block06 (l : Fin 50) :
    prawitzRationalKernelSq (301 + l.val) ≤
      ((prawitzKernelMagnitudeIndex (301 + l.val) : ℚ) / 1000000) ^ 2 := by
  fin_cases l <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem kernelSquare_block07 (l : Fin 50) :
    prawitzRationalKernelSq (351 + l.val) ≤
      ((prawitzKernelMagnitudeIndex (351 + l.val) : ℚ) / 1000000) ^ 2 := by
  fin_cases l <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem kernelSquare_block08 (l : Fin 50) :
    prawitzRationalKernelSq (401 + l.val) ≤
      ((prawitzKernelMagnitudeIndex (401 + l.val) : ℚ) / 1000000) ^ 2 := by
  fin_cases l <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem kernelSquare_block09 (l : Fin 50) :
    prawitzRationalKernelSq (451 + l.val) ≤
      ((prawitzKernelMagnitudeIndex (451 + l.val) : ℚ) / 1000000) ^ 2 := by
  fin_cases l <;> decide +kernel

end Causalean.Stat.CLT.BerryEsseen

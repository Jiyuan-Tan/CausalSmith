module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzCompactRationalData
public import Mathlib.Tactic.FinCases

/-! # High Prawitz certificate: checked kernel-square blocks 10 through 14

Kernel-checked squared-kernel enclosures for grid cells 501 through 750.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open Finset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem kernelSquare_block10 (l : Fin 50) :
    prawitzRationalKernelSq (501 + l.val) ≤
      ((prawitzKernelMagnitudeIndex (501 + l.val) : ℚ) / 1000000) ^ 2 := by
  fin_cases l <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem kernelSquare_block11 (l : Fin 50) :
    prawitzRationalKernelSq (551 + l.val) ≤
      ((prawitzKernelMagnitudeIndex (551 + l.val) : ℚ) / 1000000) ^ 2 := by
  fin_cases l <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem kernelSquare_block12 (l : Fin 50) :
    prawitzRationalKernelSq (601 + l.val) ≤
      ((prawitzKernelMagnitudeIndex (601 + l.val) : ℚ) / 1000000) ^ 2 := by
  fin_cases l <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem kernelSquare_block13 (l : Fin 50) :
    prawitzRationalKernelSq (651 + l.val) ≤
      ((prawitzKernelMagnitudeIndex (651 + l.val) : ℚ) / 1000000) ^ 2 := by
  fin_cases l <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem kernelSquare_block14 (l : Fin 50) :
    prawitzRationalKernelSq (701 + l.val) ≤
      ((prawitzKernelMagnitudeIndex (701 + l.val) : ℚ) / 1000000) ^ 2 := by
  fin_cases l <;> decide +kernel

end Causalean.Stat.CLT.BerryEsseen

module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.Core
public import Mathlib.Tactic.FinCases

/-! # High Prawitz certificate: checked integer blocks 24 through 26

Kernel-checked integer suffix totals for parameter cells 240 through 269.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open Finset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem highInteger_block24 (l : Fin 10) :
    highIntSuffix (240 + l.val)
      (1000 - prawitzHighCutoffIndex (240 + l.val)) ≤ 18000000 := by
  fin_cases l <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem highInteger_block25 (l : Fin 10) :
    highIntSuffix (250 + l.val)
      (1000 - prawitzHighCutoffIndex (250 + l.val)) ≤ 18000000 := by
  fin_cases l <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem highInteger_block26 (l : Fin 10) :
    highIntSuffix (260 + l.val)
      (1000 - prawitzHighCutoffIndex (260 + l.val)) ≤ 18000000 := by
  fin_cases l <;> decide +kernel

end Causalean.Stat.CLT.BerryEsseen

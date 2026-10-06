module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.Core
public import Mathlib.Tactic.FinCases

/-! # High Prawitz certificate: checked integer blocks 21 through 23

Kernel-checked integer suffix totals for parameter cells 210 through 239.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open Finset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem highInteger_block21 (l : Fin 10) :
    highIntSuffix (210 + l.val)
      (1000 - prawitzHighCutoffIndex (210 + l.val)) ≤ 18000000 := by
  fin_cases l <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem highInteger_block22 (l : Fin 10) :
    highIntSuffix (220 + l.val)
      (1000 - prawitzHighCutoffIndex (220 + l.val)) ≤ 18000000 := by
  fin_cases l <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem highInteger_block23 (l : Fin 10) :
    highIntSuffix (230 + l.val)
      (1000 - prawitzHighCutoffIndex (230 + l.val)) ≤ 18000000 := by
  fin_cases l <;> decide +kernel

end Causalean.Stat.CLT.BerryEsseen

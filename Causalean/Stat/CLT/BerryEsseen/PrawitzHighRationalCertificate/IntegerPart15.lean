module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.Core
public import Mathlib.Tactic.FinCases

/-! # High Prawitz certificate: checked integer blocks 16 through 17

Kernel-checked integer suffix totals for parameter cells 160 through 179.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open Finset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem highInteger_block16 (l : Fin 10) :
    highIntSuffix (160 + l.val)
      (1000 - prawitzHighCutoffIndex (160 + l.val)) ≤ 18000000 := by
  fin_cases l <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem highInteger_block17 (l : Fin 10) :
    highIntSuffix (170 + l.val)
      (1000 - prawitzHighCutoffIndex (170 + l.val)) ≤ 18000000 := by
  fin_cases l <;> decide +kernel

end Causalean.Stat.CLT.BerryEsseen

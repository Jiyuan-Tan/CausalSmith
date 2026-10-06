module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.Core
public import Mathlib.Tactic.FinCases

/-! # High Prawitz certificate: checked integer blocks 14 through 15

Kernel-checked integer suffix totals for parameter cells 140 through 159.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open Finset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem highInteger_block14 (l : Fin 10) :
    highIntSuffix (140 + l.val)
      (1000 - prawitzHighCutoffIndex (140 + l.val)) ≤ 18000000 := by
  fin_cases l <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem highInteger_block15 (l : Fin 10) :
    highIntSuffix (150 + l.val)
      (1000 - prawitzHighCutoffIndex (150 + l.val)) ≤ 18000000 := by
  fin_cases l <;> decide +kernel

end Causalean.Stat.CLT.BerryEsseen

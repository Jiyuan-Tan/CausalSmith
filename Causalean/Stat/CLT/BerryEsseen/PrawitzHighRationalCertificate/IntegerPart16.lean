module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzHighRationalCertificate.Core
public import Mathlib.Tactic.FinCases

/-! # High Prawitz certificate: checked integer blocks 18 through 20

Kernel-checked integer suffix totals for parameter cells 180 through 209.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open Finset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem highInteger_block18 (l : Fin 10) :
    highIntSuffix (180 + l.val)
      (1000 - prawitzHighCutoffIndex (180 + l.val)) ≤ 18000000 := by
  fin_cases l <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem highInteger_block19 (l : Fin 10) :
    highIntSuffix (190 + l.val)
      (1000 - prawitzHighCutoffIndex (190 + l.val)) ≤ 18000000 := by
  fin_cases l <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction checks every finite entry in this block.
private theorem highInteger_block20 (l : Fin 10) :
    highIntSuffix (200 + l.val)
      (1000 - prawitzHighCutoffIndex (200 + l.val)) ≤ 18000000 := by
  fin_cases l <;> decide +kernel

end Causalean.Stat.CLT.BerryEsseen

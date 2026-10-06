module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Bounds
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Core

/-! # Low Prawitz certificate: checked blocks 6 through 7

Kernel-checked integer totals for parameter cells 60 through 79.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

set_option maxRecDepth 1000000

set_option maxHeartbeats 20000000 in
-- Each block checks ten complete sums, including every outward rounding.
set_option maxRecDepth 1000000 in
/-- Checked integer totals for parameter cells 60 through 69. -/
private theorem lowInteger_block06 :
    ∀ l : Fin 10, (⌈100000000 * prawitzRationalLowInitial (60 + l.val)⌉ +
      lowIntPrefix (60 + l.val) (prawitzLowCutoffIndex (60 + l.val) - 1) : ℤ) ≤ 25000000 := by
  intro l
  apply lowInteger_of_certificate _ (lowBounds (60 + l.val))
  all_goals fin_cases l <;> decide +kernel

set_option maxHeartbeats 20000000 in
-- Each block checks ten complete sums, including every outward rounding.
set_option maxRecDepth 1000000 in
/-- Checked integer totals for parameter cells 70 through 79. -/
private theorem lowInteger_block07 :
    ∀ l : Fin 10, (⌈100000000 * prawitzRationalLowInitial (70 + l.val)⌉ +
      lowIntPrefix (70 + l.val) (prawitzLowCutoffIndex (70 + l.val) - 1) : ℤ) ≤ 25000000 := by
  intro l
  apply lowInteger_of_certificate _ (lowBounds (70 + l.val))
  all_goals fin_cases l <;> decide +kernel

end Causalean.Stat.CLT.BerryEsseen

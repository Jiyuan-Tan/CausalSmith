module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Bounds
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Core

/-! # Low Prawitz certificate: checked blocks 4 through 5

Kernel-checked integer totals for parameter cells 40 through 59.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

set_option maxRecDepth 1000000

set_option maxHeartbeats 20000000 in
-- Each block checks ten complete sums, including every outward rounding.
set_option maxRecDepth 1000000 in
/-- Checked integer totals for parameter cells 40 through 49. -/
private theorem lowInteger_block04 :
    ∀ l : Fin 10, (⌈100000000 * prawitzRationalLowInitial (40 + l.val)⌉ +
      lowIntPrefix (40 + l.val) (prawitzLowCutoffIndex (40 + l.val) - 1) : ℤ) ≤ 25000000 := by
  intro l
  apply lowInteger_of_certificate _ (lowBounds (40 + l.val))
  all_goals fin_cases l <;> decide +kernel

set_option maxHeartbeats 20000000 in
-- Each block checks ten complete sums, including every outward rounding.
set_option maxRecDepth 1000000 in
/-- Checked integer totals for parameter cells 50 through 59. -/
private theorem lowInteger_block05 :
    ∀ l : Fin 10, (⌈100000000 * prawitzRationalLowInitial (50 + l.val)⌉ +
      lowIntPrefix (50 + l.val) (prawitzLowCutoffIndex (50 + l.val) - 1) : ℤ) ≤ 25000000 := by
  intro l
  apply lowInteger_of_certificate _ (lowBounds (50 + l.val))
  all_goals fin_cases l <;> decide +kernel

end Causalean.Stat.CLT.BerryEsseen

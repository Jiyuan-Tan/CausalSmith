module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Bounds
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Core

/-! # Low Prawitz certificate: checked blocks 8 through 9

Kernel-checked integer totals for parameter cells 80 through 99.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

set_option maxRecDepth 1000000

set_option maxHeartbeats 20000000 in
-- Each block checks ten complete sums, including every outward rounding.
set_option maxRecDepth 1000000 in
/-- Checked integer totals for parameter cells 80 through 89. -/
private theorem lowInteger_block08 :
    ∀ l : Fin 10, (⌈100000000 * prawitzRationalLowInitial (80 + l.val)⌉ +
      lowIntPrefix (80 + l.val) (prawitzLowCutoffIndex (80 + l.val) - 1) : ℤ) ≤ 25000000 := by
  intro l
  apply lowInteger_of_certificate _ (lowBounds (80 + l.val))
  all_goals fin_cases l <;> decide +kernel

set_option maxHeartbeats 20000000 in
-- Each block checks ten complete sums, including every outward rounding.
set_option maxRecDepth 1000000 in
/-- Checked integer totals for parameter cells 90 through 99. -/
private theorem lowInteger_block09 :
    ∀ l : Fin 10, (⌈100000000 * prawitzRationalLowInitial (90 + l.val)⌉ +
      lowIntPrefix (90 + l.val) (prawitzLowCutoffIndex (90 + l.val) - 1) : ℤ) ≤ 25000000 := by
  intro l
  apply lowInteger_of_certificate _ (lowBounds (90 + l.val))
  all_goals fin_cases l <;> decide +kernel

end Causalean.Stat.CLT.BerryEsseen

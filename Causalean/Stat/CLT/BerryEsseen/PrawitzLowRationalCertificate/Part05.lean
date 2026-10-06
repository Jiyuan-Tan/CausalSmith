module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Bounds
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Core

/-! # Low Prawitz certificate: checked blocks 10 through 12

Kernel-checked integer totals for parameter cells 100 through 129.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

set_option maxRecDepth 1000000

set_option maxHeartbeats 20000000 in
-- Each block checks ten complete sums, including every outward rounding.
set_option maxRecDepth 1000000 in
/-- Checked integer totals for parameter cells 100 through 109. -/
private theorem lowInteger_block10 :
    ∀ l : Fin 10, (⌈100000000 * prawitzRationalLowInitial (100 + l.val)⌉ +
      lowIntPrefix (100 + l.val) (prawitzLowCutoffIndex (100 + l.val) - 1) : ℤ) ≤ 25000000 := by
  intro l
  apply lowInteger_of_certificate _ (lowBounds (100 + l.val))
  all_goals fin_cases l <;> decide +kernel

set_option maxHeartbeats 20000000 in
-- Each block checks ten complete sums, including every outward rounding.
set_option maxRecDepth 1000000 in
/-- Checked integer totals for parameter cells 110 through 119. -/
private theorem lowInteger_block11 :
    ∀ l : Fin 10, (⌈100000000 * prawitzRationalLowInitial (110 + l.val)⌉ +
      lowIntPrefix (110 + l.val) (prawitzLowCutoffIndex (110 + l.val) - 1) : ℤ) ≤ 25000000 := by
  intro l
  apply lowInteger_of_certificate _ (lowBounds (110 + l.val))
  all_goals fin_cases l <;> decide +kernel

set_option maxHeartbeats 20000000 in
-- Each block checks ten complete sums, including every outward rounding.
set_option maxRecDepth 1000000 in
/-- Checked integer totals for parameter cells 120 through 129. -/
private theorem lowInteger_block12 :
    ∀ l : Fin 10, (⌈100000000 * prawitzRationalLowInitial (120 + l.val)⌉ +
      lowIntPrefix (120 + l.val) (prawitzLowCutoffIndex (120 + l.val) - 1) : ℤ) ≤ 25000000 := by
  intro l
  apply lowInteger_of_certificate _ (lowBounds (120 + l.val))
  all_goals fin_cases l <;> decide +kernel

end Causalean.Stat.CLT.BerryEsseen

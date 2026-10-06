module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Bounds
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Core

/-! # Low Prawitz certificate: checked blocks 2 through 3

Kernel-checked integer totals for parameter cells 20 through 39.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

set_option maxRecDepth 1000000

set_option maxHeartbeats 20000000 in
-- Each block checks ten complete sums, including every outward rounding.
set_option maxRecDepth 1000000 in
/-- Checked integer totals for parameter cells 20 through 29. -/
private theorem lowInteger_block02 :
    ∀ l : Fin 10, (⌈100000000 * prawitzRationalLowInitial (20 + l.val)⌉ +
      lowIntPrefix (20 + l.val) (prawitzLowCutoffIndex (20 + l.val) - 1) : ℤ) ≤ 25000000 := by
  intro l
  apply lowInteger_of_certificate _ (lowBounds (20 + l.val))
  all_goals fin_cases l <;> decide +kernel

set_option maxHeartbeats 20000000 in
-- Each block checks ten complete sums, including every outward rounding.
set_option maxRecDepth 1000000 in
/-- Checked integer totals for parameter cells 30 through 39. -/
private theorem lowInteger_block03 :
    ∀ l : Fin 10, (⌈100000000 * prawitzRationalLowInitial (30 + l.val)⌉ +
      lowIntPrefix (30 + l.val) (prawitzLowCutoffIndex (30 + l.val) - 1) : ℤ) ≤ 25000000 := by
  intro l
  apply lowInteger_of_certificate _ (lowBounds (30 + l.val))
  all_goals fin_cases l <;> decide +kernel

end Causalean.Stat.CLT.BerryEsseen

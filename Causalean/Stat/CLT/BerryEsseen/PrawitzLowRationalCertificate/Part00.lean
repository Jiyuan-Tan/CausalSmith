module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Bounds
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Core

/-! # Low Prawitz certificate: checked blocks 0 through 1

Kernel-checked integer totals for parameter cells 0 through 19.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

set_option maxRecDepth 1000000

set_option maxHeartbeats 20000000 in
-- Each block checks ten complete sums, including every outward rounding.
set_option maxRecDepth 1000000 in
/-- Checked integer totals for parameter cells 0 through 9. -/
private theorem lowInteger_block00 :
    ∀ l : Fin 10, (⌈100000000 * prawitzRationalLowInitial (0 + l.val)⌉ +
      lowIntPrefix (0 + l.val) (prawitzLowCutoffIndex (0 + l.val) - 1) : ℤ) ≤ 25000000 := by
  intro l
  apply lowInteger_of_certificate _ (lowBounds (0 + l.val))
  all_goals fin_cases l <;> decide +kernel

set_option maxHeartbeats 20000000 in
-- Each block checks ten complete sums, including every outward rounding.
set_option maxRecDepth 1000000 in
/-- Checked integer totals for parameter cells 10 through 19. -/
private theorem lowInteger_block01 :
    ∀ l : Fin 10, (⌈100000000 * prawitzRationalLowInitial (10 + l.val)⌉ +
      lowIntPrefix (10 + l.val) (prawitzLowCutoffIndex (10 + l.val) - 1) : ℤ) ≤ 25000000 := by
  intro l
  apply lowInteger_of_certificate _ (lowBounds (10 + l.val))
  all_goals fin_cases l <;> decide +kernel

end Causalean.Stat.CLT.BerryEsseen

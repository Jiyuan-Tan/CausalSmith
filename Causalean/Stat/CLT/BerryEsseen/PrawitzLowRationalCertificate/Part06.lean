module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Bounds
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Core

/-! # Low Prawitz certificate: checked blocks 13 through 16

Kernel-checked integer totals for parameter cells 130 through 169.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

set_option maxRecDepth 1000000

set_option maxHeartbeats 20000000 in
-- Each block checks ten complete sums, including every outward rounding.
set_option maxRecDepth 1000000 in
/-- Checked integer totals for parameter cells 130 through 139. -/
private theorem lowInteger_block13 :
    ∀ l : Fin 10, (⌈100000000 * prawitzRationalLowInitial (130 + l.val)⌉ +
      lowIntPrefix (130 + l.val) (prawitzLowCutoffIndex (130 + l.val) - 1) : ℤ) ≤ 25000000 := by
  intro l
  apply lowInteger_of_certificate _ (lowBounds (130 + l.val))
  all_goals fin_cases l <;> decide +kernel

set_option maxHeartbeats 20000000 in
-- Each block checks ten complete sums, including every outward rounding.
set_option maxRecDepth 1000000 in
/-- Checked integer totals for parameter cells 140 through 149. -/
private theorem lowInteger_block14 :
    ∀ l : Fin 10, (⌈100000000 * prawitzRationalLowInitial (140 + l.val)⌉ +
      lowIntPrefix (140 + l.val) (prawitzLowCutoffIndex (140 + l.val) - 1) : ℤ) ≤ 25000000 := by
  intro l
  apply lowInteger_of_certificate _ (lowBounds (140 + l.val))
  all_goals fin_cases l <;> decide +kernel

set_option maxHeartbeats 20000000 in
-- Each block checks ten complete sums, including every outward rounding.
set_option maxRecDepth 1000000 in
/-- Checked integer totals for parameter cells 150 through 159. -/
private theorem lowInteger_block15 :
    ∀ l : Fin 10, (⌈100000000 * prawitzRationalLowInitial (150 + l.val)⌉ +
      lowIntPrefix (150 + l.val) (prawitzLowCutoffIndex (150 + l.val) - 1) : ℤ) ≤ 25000000 := by
  intro l
  apply lowInteger_of_certificate _ (lowBounds (150 + l.val))
  all_goals fin_cases l <;> decide +kernel

set_option maxHeartbeats 20000000 in
-- Each block checks ten complete sums, including every outward rounding.
set_option maxRecDepth 1000000 in
/-- Checked integer totals for parameter cells 160 through 169. -/
private theorem lowInteger_block16 :
    ∀ l : Fin 10, (⌈100000000 * prawitzRationalLowInitial (160 + l.val)⌉ +
      lowIntPrefix (160 + l.val) (prawitzLowCutoffIndex (160 + l.val) - 1) : ℤ) ≤ 25000000 := by
  intro l
  apply lowInteger_of_certificate _ (lowBounds (160 + l.val))
  all_goals fin_cases l <;> decide +kernel

end Causalean.Stat.CLT.BerryEsseen

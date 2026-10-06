module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Bounds
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Core

/-! # Low Prawitz certificate: checked blocks 22 through 26

Kernel-checked integer totals for parameter cells 220 through 269.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

set_option maxRecDepth 1000000

set_option maxHeartbeats 20000000 in
-- Each block checks ten complete sums, including every outward rounding.
set_option maxRecDepth 1000000 in
/-- Checked integer totals for parameter cells 220 through 229. -/
private theorem lowInteger_block22 :
    ∀ l : Fin 10, (⌈100000000 * prawitzRationalLowInitial (220 + l.val)⌉ +
      lowIntPrefix (220 + l.val) (prawitzLowCutoffIndex (220 + l.val) - 1) : ℤ) ≤ 25000000 := by
  intro l
  apply lowInteger_of_certificate _ (lowBounds (220 + l.val))
  all_goals fin_cases l <;> decide +kernel

set_option maxHeartbeats 20000000 in
-- Each block checks ten complete sums, including every outward rounding.
set_option maxRecDepth 1000000 in
/-- Checked integer totals for parameter cells 230 through 239. -/
private theorem lowInteger_block23 :
    ∀ l : Fin 10, (⌈100000000 * prawitzRationalLowInitial (230 + l.val)⌉ +
      lowIntPrefix (230 + l.val) (prawitzLowCutoffIndex (230 + l.val) - 1) : ℤ) ≤ 25000000 := by
  intro l
  apply lowInteger_of_certificate _ (lowBounds (230 + l.val))
  all_goals fin_cases l <;> decide +kernel

set_option maxHeartbeats 20000000 in
-- Each block checks ten complete sums, including every outward rounding.
set_option maxRecDepth 1000000 in
/-- Checked integer totals for parameter cells 240 through 249. -/
private theorem lowInteger_block24 :
    ∀ l : Fin 10, (⌈100000000 * prawitzRationalLowInitial (240 + l.val)⌉ +
      lowIntPrefix (240 + l.val) (prawitzLowCutoffIndex (240 + l.val) - 1) : ℤ) ≤ 25000000 := by
  intro l
  apply lowInteger_of_certificate _ (lowBounds (240 + l.val))
  all_goals fin_cases l <;> decide +kernel

set_option maxHeartbeats 20000000 in
-- Each block checks ten complete sums, including every outward rounding.
set_option maxRecDepth 1000000 in
/-- Checked integer totals for parameter cells 250 through 259. -/
private theorem lowInteger_block25 :
    ∀ l : Fin 10, (⌈100000000 * prawitzRationalLowInitial (250 + l.val)⌉ +
      lowIntPrefix (250 + l.val) (prawitzLowCutoffIndex (250 + l.val) - 1) : ℤ) ≤ 25000000 := by
  intro l
  apply lowInteger_of_certificate _ (lowBounds (250 + l.val))
  all_goals fin_cases l <;> decide +kernel

set_option maxHeartbeats 20000000 in
-- Each block checks ten complete sums, including every outward rounding.
set_option maxRecDepth 1000000 in
/-- Checked integer totals for parameter cells 260 through 269. -/
private theorem lowInteger_block26 :
    ∀ l : Fin 10, (⌈100000000 * prawitzRationalLowInitial (260 + l.val)⌉ +
      lowIntPrefix (260 + l.val) (prawitzLowCutoffIndex (260 + l.val) - 1) : ℤ) ≤ 25000000 := by
  intro l
  apply lowInteger_of_certificate _ (lowBounds (260 + l.val))
  all_goals fin_cases l <;> decide +kernel

end Causalean.Stat.CLT.BerryEsseen

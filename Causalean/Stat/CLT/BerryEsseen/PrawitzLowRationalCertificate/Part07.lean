module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Bounds
-- private import
import all Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Core

/-! # Low Prawitz certificate: checked blocks 17 through 21

Kernel-checked integer totals for parameter cells 170 through 219.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

set_option maxRecDepth 1000000

set_option maxHeartbeats 20000000 in
-- Each block checks ten complete sums, including every outward rounding.
set_option maxRecDepth 1000000 in
/-- Checked integer totals for parameter cells 170 through 179. -/
private theorem lowInteger_block17 :
    ∀ l : Fin 10, (⌈100000000 * prawitzRationalLowInitial (170 + l.val)⌉ +
      lowIntPrefix (170 + l.val) (prawitzLowCutoffIndex (170 + l.val) - 1) : ℤ) ≤ 25000000 := by
  intro l
  apply lowInteger_of_certificate _ (lowBounds (170 + l.val))
  all_goals fin_cases l <;> decide +kernel

set_option maxHeartbeats 20000000 in
-- Each block checks ten complete sums, including every outward rounding.
set_option maxRecDepth 1000000 in
/-- Checked integer totals for parameter cells 180 through 189. -/
private theorem lowInteger_block18 :
    ∀ l : Fin 10, (⌈100000000 * prawitzRationalLowInitial (180 + l.val)⌉ +
      lowIntPrefix (180 + l.val) (prawitzLowCutoffIndex (180 + l.val) - 1) : ℤ) ≤ 25000000 := by
  intro l
  apply lowInteger_of_certificate _ (lowBounds (180 + l.val))
  all_goals fin_cases l <;> decide +kernel

set_option maxHeartbeats 20000000 in
-- Each block checks ten complete sums, including every outward rounding.
set_option maxRecDepth 1000000 in
/-- Checked integer totals for parameter cells 190 through 199. -/
private theorem lowInteger_block19 :
    ∀ l : Fin 10, (⌈100000000 * prawitzRationalLowInitial (190 + l.val)⌉ +
      lowIntPrefix (190 + l.val) (prawitzLowCutoffIndex (190 + l.val) - 1) : ℤ) ≤ 25000000 := by
  intro l
  apply lowInteger_of_certificate _ (lowBounds (190 + l.val))
  all_goals fin_cases l <;> decide +kernel

set_option maxHeartbeats 20000000 in
-- Each block checks ten complete sums, including every outward rounding.
set_option maxRecDepth 1000000 in
/-- Checked integer totals for parameter cells 200 through 209. -/
private theorem lowInteger_block20 :
    ∀ l : Fin 10, (⌈100000000 * prawitzRationalLowInitial (200 + l.val)⌉ +
      lowIntPrefix (200 + l.val) (prawitzLowCutoffIndex (200 + l.val) - 1) : ℤ) ≤ 25000000 := by
  intro l
  apply lowInteger_of_certificate _ (lowBounds (200 + l.val))
  all_goals fin_cases l <;> decide +kernel

set_option maxHeartbeats 20000000 in
-- Each block checks ten complete sums, including every outward rounding.
set_option maxRecDepth 1000000 in
/-- Checked integer totals for parameter cells 210 through 219. -/
private theorem lowInteger_block21 :
    ∀ l : Fin 10, (⌈100000000 * prawitzRationalLowInitial (210 + l.val)⌉ +
      lowIntPrefix (210 + l.val) (prawitzLowCutoffIndex (210 + l.val) - 1) : ℤ) ≤ 25000000 := by
  intro l
  apply lowInteger_of_certificate _ (lowBounds (210 + l.val))
  all_goals fin_cases l <;> decide +kernel

end Causalean.Stat.CLT.BerryEsseen

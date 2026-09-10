/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Variable-intensity IV ordered treatment algebra

Finite ordered treatment-intensity algebra: adjacent margins, crossing
indicators, and telescoping identities, plus normalized finite weights, used by
the variable-intensity instrumental-variable characterizations in this folder.
This is the sole consumer of the ordered-intensity algebra, so it is colocated
here rather than under `Panel`.
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Causalean.Panel.Weighted.NormalizedWeights

/-! # Variable-Intensity IV Ordered Treatment

This file provides algebra for finite ordered treatment or intensity levels: it
defines adjacent margins, crossing indicators, and telescoping identities that
express a change across ordered levels as the sum of crossed marginal increments,
and re-exports the generic normalized finite weights. These are used in
variable-intensity instrumental-variable characterizations. -/

namespace Causalean
namespace PO.ID.Exact
namespace VariableIntensityIV
namespace OrderedTreatment

open Finset

/-- For [a sequence of $J$ adjacent margins](hyp:J) and [a margin](hyp:j), the [lower treatment level](goal) is the lower endpoint of that margin in the ordered list of $J+1$ levels. -/
def lowerLevel {J : ℕ} (j : Fin J) : Fin (J + 1) :=
  j.castSucc

/-- For [a sequence of $J$ adjacent margins](hyp:J) and [a margin](hyp:j), the [upper treatment level](goal) is the upper endpoint of that margin in the ordered list of $J+1$ levels. -/
def upperLevel {J : ℕ} (j : Fin J) : Fin (J + 1) :=
  j.succ

/-- For [a sequence of $J$ adjacent margins](hyp:J) and [an ordered treatment level](hyp:d), the [numeric intensity value](goal) is that level's position in the ordered list, expressed as a real number. -/
def intensityValue {J : ℕ} (d : Fin (J + 1)) : ℝ :=
  d.val

/-- For [a sequence of $J$ adjacent margins](hyp:J), [a real-valued function on the $J+1$ ordered treatment levels](hyp:f), and [a margin](hyp:j), the [margin increment](goal) is the function value at that margin's upper endpoint minus its value at the lower endpoint. -/
def marginIncrement {J : ℕ} (f : Fin (J + 1) → ℝ) (j : Fin J) : ℝ :=
  f (upperLevel j) - f (lowerLevel j)

/-- For [a sequence of $J$ adjacent margins](hyp:J), [an initial treatment level](hyp:a), [a final treatment level](hyp:b), and [a margin](hyp:j), the [crossing condition](goal) holds exactly when the movement starts below that margin's upper endpoint and ends at or above it. -/
def Crossing {J : ℕ} (a b : Fin (J + 1)) (j : Fin J) : Prop :=
  upperLevel j ≤ b ∧ a < upperLevel j

/-- For [a sequence of $J$ adjacent margins](hyp:J), [an initial treatment level](hyp:a), [a final treatment level](hyp:b), and [a margin](hyp:j), the [crossing indicator](goal) equals one when the movement crosses that margin and zero otherwise. -/
noncomputable def crossingIndicator {J : ℕ} (a b : Fin (J + 1)) (j : Fin J) : ℝ := by
  classical
  exact if Crossing a b j then 1 else 0

/-- Crossing is the same as the lower endpoint lying in the half-open interval
`[a,b)` of numeric intensity levels. -/
private lemma crossingIndicator_eq_ite_val {J : ℕ} (a b : Fin (J + 1)) (j : Fin J) :
    crossingIndicator a b j = if a.val ≤ j.val ∧ j.val < b.val then 1 else 0 := by
  classical
  unfold crossingIndicator Crossing upperLevel
  by_cases h : j.succ ≤ b ∧ a < j.succ
  · rw [if_pos h, if_pos]
    constructor
    · exact Nat.le_of_lt_succ ((Fin.val_fin_lt).2 h.2)
    · exact Nat.lt_of_succ_le ((Fin.val_fin_le).2 h.1)
  · rw [if_neg h, if_neg]
    intro hv
    apply h
    constructor
    · exact (Fin.val_fin_le).1 (Nat.succ_le_of_lt hv.2)
    · exact (Fin.val_fin_lt).1 (Nat.lt_succ_of_le hv.1)

/-- Ordered telescoping across crossed margins for an arbitrary real-valued
function on finite ordered levels. -/
lemma ordered_telescope_indicator {J : ℕ} (f : Fin (J + 1) → ℝ)
    {a b : Fin (J + 1)} (hab : a ≤ b) :
    f b - f a = ∑ j : Fin J, marginIncrement f j * crossingIndicator a b j := by
  classical
  let F : ℕ → ℝ := fun n => if h : n < J + 1 then f ⟨n, h⟩ else 0
  have hNat : a.val ≤ b.val := (Fin.val_fin_le).2 hab
  calc
    f b - f a = F b.val - F a.val := by
      have haJ : a.val ≤ J := Nat.le_of_lt_succ a.isLt
      have hbJ : b.val ≤ J := Nat.le_of_lt_succ b.isLt
      simp [F, haJ, hbJ]
    _ = ∑ i ∈ Finset.Ico a.val b.val, (F (i + 1) - F i) := by
      rw [Finset.sum_Ico_sub F hNat]
    _ = ∑ j : Fin J, marginIncrement f j * crossingIndicator a b j := by
      have hIco :
          Finset.Ico a.val b.val =
            (Finset.range J).filter (fun x => a.val ≤ x ∧ x < b.val) := by
        ext x
        simp [Finset.mem_Ico]
        omega
      rw [hIco, Finset.sum_filter, Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro x hx
      have hxJ : x < J := by simpa using hx
      have hxleJ : x ≤ J := by omega
      simp [F, marginIncrement, lowerLevel, upperLevel, crossingIndicator_eq_ite_val,
        hxJ, hxleJ]

/-- **Ordered telescoping for the identity intensity map.** For [an ordered treatment
level `a` no larger than `b`](hyp:hab) among `J + 1` ordered intensity levels, [the numeric
gap `b − a` equals the number of unit margins `j → j+1` that the movement from `a` to `b`
crosses](goal). -/
lemma ordered_telescope_identity {J : ℕ} {a b : Fin (J + 1)} (hab : a ≤ b) :
    intensityValue b - intensityValue a = ∑ j : Fin J, crossingIndicator a b j := by
  simpa [intensityValue, marginIncrement, lowerLevel, upperLevel] using
    (ordered_telescope_indicator (J := J) (fun d : Fin (J + 1) => intensityValue d) hab)

/-- Given [a finite collection of indices](hyp:ι), [a real weight assigned to each index](hyp:a), and [one index](hyp:i), the [normalized finite weight](goal) is that index's weight divided by the sum of all weights. -/
noncomputable abbrev normalizedWeight {ι : Type*} [Fintype ι] (a : ι → ℝ) (i : ι) : ℝ :=
  Causalean.Panel.Weighted.NormalizedWeights.normalizedWeight a i

/-- Nonnegativity of normalized weights from nonnegative raw weights and a
positive normalizing sum. -/
lemma normalizedWeight_nonneg {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hsum : 0 < ∑ i, a i) (i : ι) :
    0 ≤ normalizedWeight a i := by
  exact Causalean.Panel.Weighted.NormalizedWeights.normalizedWeight_nonneg a ha hsum i

/-- Normalized finite weights sum to one when the normalizing sum is positive. -/
lemma sum_normalizedWeight_eq_one {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (hsum : 0 < ∑ i, a i) :
    ∑ i, normalizedWeight a i = 1 := by
  exact Causalean.Panel.Weighted.NormalizedWeights.sum_normalizedWeight_eq_one a hsum.ne'

end OrderedTreatment
end VariableIntensityIV

namespace OrderedTreatment

export VariableIntensityIV.OrderedTreatment
  (ordered_telescope_indicator ordered_telescope_identity)

end OrderedTreatment

end PO.ID.Exact
end Causalean

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

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Causalean.Stat.Weighted.NormalizedWeights

/-! # Variable-Intensity IV Ordered Treatment

This file provides algebra for finite ordered treatment or intensity levels: it
defines adjacent margins, crossing indicators, and telescoping identities that
express a change across ordered levels as the sum of crossed marginal increments,
and re-exports the generic normalized finite weights. These are used in
variable-intensity instrumental-variable characterizations. -/

@[expose] public section

namespace Causalean
namespace PO.ID.Exact
namespace VariableIntensityIV
namespace OrderedTreatment

open Finset

/-- [The lower endpoint of a treatment margin](goal) is the level immediately below [that
margin](hyp:j) on [a scale with the stated number of adjacent margins](hyp:J). -/
def lowerLevel {J : ℕ} (j : Fin J) : Fin (J + 1) :=
  j.castSucc

/-- [The upper endpoint of a treatment margin](goal) is the level immediately above [that
margin](hyp:j) on [a scale with the stated number of adjacent margins](hyp:J). -/
def upperLevel {J : ℕ} (j : Fin J) : Fin (J + 1) :=
  j.succ

/-- [Numeric treatment intensity](goal) is the real-valued rank of [an ordered treatment
level](hyp:d) on [a scale with the stated number of margins](hyp:J). -/
def intensityValue {J : ℕ} (d : Fin (J + 1)) : ℝ :=
  d.val

/-- [A margin increment](goal) measures how [a real response schedule](hyp:f) changes across [one
adjacent treatment margin](hyp:j) on [the ordered scale](hyp:J). -/
def marginIncrement {J : ℕ} (f : Fin (J + 1) → ℝ) (j : Fin J) : ℝ :=
  f (upperLevel j) - f (lowerLevel j)

/-- [A treatment move crosses a margin](goal) exactly when [its initial level](hyp:a) is below
[that margin](hyp:j) and [its final level](hyp:b) is at or above it on [the ordered
scale](hyp:J). -/
def Crossing {J : ℕ} (a b : Fin (J + 1)) (j : Fin J) : Prop :=
  upperLevel j ≤ b ∧ a < upperLevel j

/-- [The margin-crossing indicator](goal) assigns one when movement from [an initial
level](hyp:a) to [a final level](hyp:b) crosses [the chosen margin](hyp:j), and zero otherwise, on
[the ordered scale](hyp:J). -/
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

/-- [The change in a response schedule between two ordered treatment levels equals the sum of its
increments over exactly the crossed margins](goal) for [a finite ordered scale](hyp:J), [the
response schedule](hyp:f), [the initial and final levels](hyp:a,b), and [their ordering](hyp:hab).
This converts level contrasts into margin-specific causal responses. -/
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

/-- **Ordered telescoping for treatment intensity.** [The numeric increase between two ordered
treatment levels equals the number of margins crossed](goal) on [a finite ordered scale](hyp:J),
for [the initial and final levels](hyp:a,b) under [the condition that treatment weakly
increases](hyp:hab). -/
lemma ordered_telescope_identity {J : ℕ} {a b : Fin (J + 1)} (hab : a ≤ b) :
    intensityValue b - intensityValue a = ∑ j : Fin J, crossingIndicator a b j := by
  simpa [intensityValue, marginIncrement, lowerLevel, upperLevel] using
    (ordered_telescope_indicator (J := J) (fun d : Fin (J + 1) => intensityValue d) hab)

/-- [A normalized finite weight](goal) is [one raw weight](hyp:i) from [a finite index
set](hyp:ι), drawn from [the supplied weight schedule](hyp:a), divided by total raw weight. -/
noncomputable abbrev normalizedWeight {ι : Type*} [Fintype ι] (a : ι → ℝ) (i : ι) : ℝ :=
  Causalean.Stat.Weighted.NormalizedWeights.normalizedWeight a i

/-- [Every normalized weight is nonnegative](goal) when [the finite index set](hyp:ι) carries
[raw weights](hyp:a) that are [all nonnegative](hyp:ha) with [positive total](hyp:hsum), for [the
selected index](hyp:i). -/
lemma normalizedWeight_nonneg {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hsum : 0 < ∑ i, a i) (i : ι) :
    0 ≤ normalizedWeight a i := by
  exact Causalean.Stat.Weighted.NormalizedWeights.normalizedWeight_nonneg a ha hsum i

/-- [Normalized weights sum to one](goal) when [the finite index set](hyp:ι) carries [raw
weights](hyp:a) with [positive total](hyp:hsum), so they form averaging weights. -/
lemma sum_normalizedWeight_eq_one {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (hsum : 0 < ∑ i, a i) :
    ∑ i, normalizedWeight a i = 1 := by
  exact Causalean.Stat.Weighted.NormalizedWeights.sum_normalizedWeight_eq_one a hsum.ne'

end OrderedTreatment
end VariableIntensityIV

namespace OrderedTreatment

export VariableIntensityIV.OrderedTreatment
  (ordered_telescope_indicator ordered_telescope_identity)

end OrderedTreatment

end PO.ID.Exact
end Causalean

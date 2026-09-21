/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Mathlib.Data.List.Infix

/-! # List append and tail identities

This file provides index-level identities for a list formed by appending the tail of one
nonempty list to another list.
-/

public section

namespace Causalean.Mathlib.Data.List

/-- For [lists `pa` and `q`](hyp:pa,q), with [`pa` nonempty](hyp:_hpa) and
[`q` nonempty](hyp:hq), [appending the tail has the stated length and indexing laws](goal). -/
lemma get_appendTail {V : Type*} (pa q : List V)
    (_hpa : pa ≠ []) (hq : q ≠ []) :
    (pa ++ q.tail).length = pa.length + q.length - 1 ∧
    (∀ (j : ℕ) (hj : j < pa.length),
      (pa ++ q.tail).get ⟨j, by
        rw [List.length_append]; have := List.length_tail (l := q); omega⟩ = pa.get ⟨j, hj⟩) ∧
    (∀ (j : ℕ) (hjL : pa.length ≤ j) (hj : j < (pa ++ q.tail).length),
      (pa ++ q.tail).get ⟨j, hj⟩ =
        q.get ⟨j - pa.length + 1, by
          rw [List.length_append, List.length_tail] at hj
          have : 1 ≤ q.length := List.length_pos_iff.mpr hq
          omega⟩) := by
  have htail_len : q.tail.length = q.length - 1 := List.length_tail
  have hqpos : 1 ≤ q.length := List.length_pos_iff.mpr hq
  refine ⟨?_, ?_, ?_⟩
  · rw [List.length_append, htail_len]; omega
  · intro j hj
    simp only [List.get_eq_getElem, List.getElem_append_left (h := hj)]
  · intro j hjL hj
    have hjr : j - pa.length < q.tail.length := by
      rw [List.length_append] at hj; omega
    have e1 : (pa ++ q.tail).get ⟨j, hj⟩ = q.tail[j - pa.length]'hjr := by
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_right (by omega)]
    rw [e1, List.getElem_tail]
    simp [List.get_eq_getElem]

end Causalean.Mathlib.Data.List

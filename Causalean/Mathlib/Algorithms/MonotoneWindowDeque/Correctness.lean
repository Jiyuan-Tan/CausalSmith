import Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Update
import Mathlib.Data.Finset.Max

/-!
# Head and finite-window maximum correctness

The invariant implies that the deque head is an active argmax.  This module exposes both the
argmax witness formulation and equality with the maximum of the finite set of active values, so
consumers never need to unfold the internal domination invariant.
-/

namespace Causalean.Mathlib.Algorithms.MonotoneWindowDeque

variable {α : Type*} [LinearOrder α]

/-- [A stream](hyp:stream) and [a bounded window](hyp:window) determine [the finite set of values
observed in that window](goal). -/
def windowValues (stream : Stream α) (window : Window stream.length) : Finset α :=
  window.indexFinset.image stream.value

/-- [A stream](hyp:stream), [a bounded window](hyp:window), and [strictly ordered window
endpoints](hyp:hne) ensure [that the window's finite value set is nonempty](goal). -/
theorem windowValues_nonempty (stream : Stream α) (window : Window stream.length)
    (hne : window.left < window.right) : (windowValues stream window).Nonempty := by
  refine ⟨stream.value window.left, ?_⟩
  rw [windowValues, Finset.mem_image]
  exact ⟨window.left, (Window.mem_indexFinset_iff window).mpr ⟨le_rfl, hne⟩, rfl⟩

/-- [A stream](hyp:stream), [a bounded window](hyp:window), and [strictly ordered window
endpoints](hyp:hne) determine [the window maximum](goal). -/
def windowMax (stream : Stream α) (window : Window stream.length)
    (hne : window.left < window.right) : α :=
  (windowValues stream window).max' (windowValues_nonempty stream window hne)

/-- [A valid raw-window deque](hyp:hq), [a nonempty raw interval](hyp:hne), and [a right endpoint
within the stream](hyp:hbound) ensure [that the deque head is active and maximizes the stream
value over that interval](goal). -/
theorem ValidAt.head_argmax {stream : Stream α} {left right : ℕ} {q : Deque}
    (hq : ValidAt stream left right q) (hne : left < right) (hbound : right ≤ stream.length) :
    ∃ head tail, q = head :: tail ∧ ActiveAt left right head ∧ head < stream.length ∧
      ∀ i, ActiveAt left right i → i < stream.length → stream.value i ≤ stream.value head := by
  have hq_ne : q ≠ [] := by
    intro hq_nil
    have hleft_bound : left < stream.length := lt_of_lt_of_le hne hbound
    obtain ⟨j, hj, -⟩ := hq.dominates_omitted left ⟨le_rfl, hne⟩ hleft_bound (by
      simp [hq_nil])
    simp [hq_nil] at hj
  obtain ⟨head, tail, rfl⟩ := List.exists_cons_of_ne_nil hq_ne
  have hhead := hq.active head (by simp)
  refine ⟨head, tail, rfl, hhead.1, hhead.2, ?_⟩
  intro i hi hibound
  have hmember_le : ∀ j ∈ head :: tail, stream.value j ≤ stream.value head := by
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact le_rfl
    · exact (List.pairwise_cons.mp hq.value_decreasing).1 j hj |>.le
  by_cases hiq : i ∈ head :: tail
  · exact hmember_le i hiq
  · obtain ⟨j, hjq, -, hij⟩ := hq.dominates_omitted i hi hibound hiq
    exact le_trans hij (hmember_le j hjq)

/-- [A valid bounded-window deque](hyp:hq) and [a nonempty window](hyp:hne) ensure [that its head
is an active argmax](goal). -/
theorem Valid.head_argmax {stream : Stream α} {window : Window stream.length} {q : Deque}
    (hq : Valid stream window q) (hne : window.left < window.right) :
    ∃ head tail, q = head :: tail ∧ Active window head ∧
      ∀ i, Active window i → stream.value i ≤ stream.value head := by
  obtain ⟨head, tail, hqeq, hhead, -, hmax⟩ :=
    ValidAt.head_argmax hq hne window.right_le_length
  refine ⟨head, tail, hqeq, hhead, ?_⟩
  intro i hi
  exact hmax i hi (lt_of_lt_of_le hi.2 window.right_le_length)

/-- [A valid bounded-window deque](hyp:hq) and [a nonempty window](hyp:hne) ensure [that its head
is an active argmax whose value equals the finite-window maximum](goal). -/
theorem Valid.head_value_eq_windowMax {stream : Stream α}
    {window : Window stream.length} {q : Deque}
    (hq : Valid stream window q) (hne : window.left < window.right) :
    ∃ head tail, q = head :: tail ∧ Active window head ∧
      stream.value head = windowMax stream window hne ∧
      ∀ i, Active window i → stream.value i ≤ stream.value head := by
  obtain ⟨head, tail, hqeq, hhead, hmax⟩ := hq.head_argmax hne
  refine ⟨head, tail, hqeq, hhead, ?_, hmax⟩
  unfold windowMax
  symm
  apply (Finset.max'_eq_iff _ _ _).mpr
  constructor
  · rw [windowValues, Finset.mem_image]
    exact ⟨head, (Window.mem_indexFinset_iff window).mpr hhead, rfl⟩
  · intro value hvalue
    rw [windowValues, Finset.mem_image] at hvalue
    obtain ⟨i, hi, rfl⟩ := hvalue
    exact hmax i ((Window.mem_indexFinset_iff window).mp hi)

end Causalean.Mathlib.Algorithms.MonotoneWindowDeque

import Causalean.Mathlib.Algorithms.MonotoneWindowDeque.PredicateRawScan
import Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Accounting
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Correctness and resource bounds for compiled raw-key scans

This module transfers the generic monotone-window deque's head-argmax, amortized operation count,
and peak-storage results to predicate scans on sparse raw keys.  It also packages a fixed finite
family of such scans, providing the constant-number-of-passes interface used by consumers.
-/

open scoped BigOperators

namespace Causalean.Mathlib.Algorithms.MonotoneWindowDeque

open Causalean.Mathlib.Algorithms.MonotoneWindowDeque

variable {ι κ α : Type*} {keys : List ι} {steps : List κ}

/-- [A raw predicate-scan trace](hyp:trace) determines [the aggregate list of pushed raw keys](goal). -/
def rawTracePushed (trace : List (RawStepTrace ι κ)) : List ι :=
  trace.flatMap (fun step => step.pushed)

/-- [A raw predicate-scan trace](hyp:trace) determines [the aggregate list of front-popped raw
keys](goal). -/
def rawTraceFrontPopped (trace : List (RawStepTrace ι κ)) : List ι :=
  trace.flatMap (fun step => step.frontPopped)

/-- [A raw predicate-scan trace](hyp:trace) determines [the aggregate list of back-popped raw
keys](goal). -/
def rawTraceBackPopped (trace : List (RawStepTrace ι κ)) : List ι :=
  trace.flatMap (fun step => step.backPopped)

/-- [A raw predicate-scan trace](hyp:trace) determines [its exact number of deque mutations](goal). -/
def rawDequeOperations (trace : List (RawStepTrace ι κ)) : ℕ :=
  (rawTracePushed trace).length + (rawTraceFrontPopped trace).length +
    (rawTraceBackPopped trace).length

/-- [A predicate schedule](hyp:P) and [a raw score](hyp:score) determine [the raw scan cost](goal),
including one bookkeeping unit per step. -/
noncomputable def PredicateWindowSchedule.rawScanCost [LinearOrder α]
    (P : PredicateWindowSchedule keys steps) (score : ι → α) : ℕ :=
  steps.length + rawDequeOperations (P.rawScan score)

/-- [A raw predicate-scan trace](hyp:trace) determines [the largest raw deque length reached](goal). -/
def rawPeakStored (trace : List (RawStepTrace ι κ)) : ℕ :=
  (trace.map (fun step => step.after.length)).foldl max 0

/- Proof route for transfers: use `scan_predicateSchedule_state_eq` to rewrite the aggregate raw
logs and state lengths.  Establish a private safe-lookup length lemma and the needed in-bounds facts
for the generic scan fields (pushed ranges are below the window right endpoint; front/back pops come
from in-bounds deque states), so `positionsToKeys` preserves their lengths.  Then apply the existing
`scanCost_le`, `peakStored_le_length`, pointwise memory, and head-argmax theorems.  For rightmost tie
maximality, combine strict deque value decrease with `ValidAt.dominates_omitted`: any omitted equal
maximizer is dominated by a later retained equal maximizer, which can only be the head. -/

private theorem positionsToKeys_length_eq (keys : List ι) (is : List ℕ)
    (hbound : ∀ i ∈ is, i < keys.length) :
    (positionsToKeys keys is).length = is.length := by
  induction is with
  | nil => simp [positionsToKeys]
  | cons i is ih =>
      have hi := hbound i (by simp)
      have his : ∀ j ∈ is, j < keys.length := by
        intro j hj
        exact hbound j (by simp [hj])
      rw [show positionsToKeys keys (i :: is) =
        keys[i] :: positionsToKeys keys is by
          simp [positionsToKeys, List.getElem?_eq_getElem hi]]
      simp [ih his]

private theorem push_bound [LinearOrder α] (stream : Stream α) (q : List ℕ) (i : ℕ)
    (hq : ∀ j ∈ q, j < stream.length) (hi : i < stream.length) :
    ∀ j ∈ push stream q i, j < stream.length := by
  intro j hj
  rcases (mem_push_iff stream q i j).mp hj with hj | rfl
  · exact hq j ((pruneBack_prefix stream q i).mem hj)
  · exact hi

private theorem pushAll_fields_bound [LinearOrder α] (stream : Stream α) (q indices : List ℕ)
    (hq : ∀ j ∈ q, j < stream.length)
    (his : ∀ i ∈ indices, i < stream.length) :
    (∀ j ∈ (pushAll stream q indices).state, j < stream.length) ∧
      (∀ j ∈ (pushAll stream q indices).pushed, j < stream.length) ∧
      (∀ j ∈ (pushAll stream q indices).backPopped, j < stream.length) := by
  induction indices generalizing q with
  | nil => exact ⟨by simpa [pushAll] using hq, by simp [pushAll], by simp [pushAll]⟩
  | cons i indices ih =>
      have hi := his i (by simp)
      have his' : ∀ j ∈ indices, j < stream.length := by
        intro j hj
        exact his j (by simp [hj])
      have hq' := push_bound stream q i hq hi
      rcases ih (q := push stream q i) hq' his' with ⟨hstate, hpushed, hback⟩
      refine ⟨hstate, ?_, ?_⟩
      · simpa [pushAll] using And.intro hi hpushed
      · intro j hj
        simp only [pushAll, List.mem_append] at hj
        rcases hj with hj | hj
        · exact hq j ((List.rtakeWhile_suffix _ _).mem hj)
        · exact hback j hj

private theorem update_fields_bound [LinearOrder α] (stream : Stream α) (oldRight : ℕ)
    (window : Window stream.length) (q : List ℕ)
    (hq : ∀ i ∈ q, i < stream.length) :
    let trace := update stream oldRight window q
    (∀ i ∈ trace.before, i < stream.length) ∧
      (∀ i ∈ trace.afterExpiration, i < stream.length) ∧
      (∀ i ∈ trace.after, i < stream.length) ∧
      (∀ i ∈ trace.pushed, i < stream.length) ∧
      (∀ i ∈ trace.frontPopped, i < stream.length) ∧
      (∀ i ∈ trace.backPopped, i < stream.length) := by
  let entered := List.range' (max oldRight window.left)
    (window.right - max oldRight window.left)
  have hentered : ∀ i ∈ entered, i < stream.length := by
    intro i hi
    have hirange := (List.mem_range'_1.mp hi).2
    by_cases hstart : max oldRight window.left ≤ window.right
    · rw [Nat.add_sub_of_le hstart] at hirange
      exact lt_of_lt_of_le hirange window.right_le_length
    · have : entered = [] := by
        simp [entered, Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hstart)]
      simp [this] at hi
  have hexp : ∀ i ∈ expireFront window.left q, i < stream.length := by
    intro i hi
    exact hq i ((List.dropWhile_suffix _).mem hi)
  have hbatch := pushAll_fields_bound stream (expireFront window.left q) entered hexp hentered
  rcases hbatch with ⟨hafter, hpushed, hback⟩
  refine ⟨hq, hexp, ?_, ?_, ?_, ?_⟩
  · simpa [update, entered] using hafter
  · simpa [update, entered] using hpushed
  · intro i hi
    exact hq i ((List.takeWhile_prefix _).mem (by
      simpa only [update, expiredFront] using hi))
  · simpa [update, entered] using hback

private theorem scanFrom_fields_bound [LinearOrder α] (stream : Stream α) :
    ∀ (oldRight : ℕ) (q : List ℕ) (windows : List (Window stream.length)),
      (∀ i ∈ q, i < stream.length) →
      ∀ trace ∈ scanFrom stream oldRight q windows,
        (∀ i ∈ trace.before, i < stream.length) ∧
        (∀ i ∈ trace.afterExpiration, i < stream.length) ∧
        (∀ i ∈ trace.after, i < stream.length) ∧
        (∀ i ∈ trace.pushed, i < stream.length) ∧
        (∀ i ∈ trace.frontPopped, i < stream.length) ∧
        (∀ i ∈ trace.backPopped, i < stream.length) := by
  intro oldRight q windows hq
  induction windows generalizing oldRight q with
  | nil => simp [scanFrom]
  | cons window windows ih =>
      let trace := update stream oldRight window q
      have ht := update_fields_bound stream oldRight window q hq
      intro found hfound
      simp only [scanFrom, List.mem_cons] at hfound
      rcases hfound with rfl | hfound
      · exact ht
      · exact ih (oldRight := window.right) (q := trace.after) ht.2.2.1 found hfound

private theorem scan_fields_bound [LinearOrder α] (stream : Stream α)
    (schedule : Schedule stream.length)
    (trace : StepTrace stream) (htrace : trace ∈ scan stream schedule) :
    (∀ i ∈ trace.before, i < stream.length) ∧
      (∀ i ∈ trace.afterExpiration, i < stream.length) ∧
      (∀ i ∈ trace.after, i < stream.length) ∧
      (∀ i ∈ trace.pushed, i < stream.length) ∧
      (∀ i ∈ trace.frontPopped, i < stream.length) ∧
      (∀ i ∈ trace.backPopped, i < stream.length) := by
  exact scanFrom_fields_bound stream 0 initialDeque schedule.windows (by simp [initialDeque])
    trace (by simpa [scan] using htrace)

private theorem positionsToKeys_flatMap_length_eq {score : ι → α} {fallback : α}
    (keys : List ι)
    (trace : List (StepTrace (keyedStream keys score fallback)))
    (field : StepTrace (keyedStream keys score fallback) → List ℕ)
    (hbound : ∀ step ∈ trace, ∀ i ∈ field step, i < keys.length) :
    (trace.flatMap (fun step => positionsToKeys keys (field step))).length =
      (trace.flatMap field).length := by
  induction trace with
  | nil => simp
  | cons step trace ih =>
      simp only [List.flatMap_cons, List.length_append]
      rw [positionsToKeys_length_eq keys (field step) (hbound step (by simp))]
      congr 1
      apply ih
      intro later hlater
      exact hbound later (by simp [hlater])

private theorem rawScanFrom_get_step [LinearOrder α]
    (P : PredicateWindowSchedule keys steps) (score : ι → α) :
    ∀ (state : RawState ι) (ss : List κ) {k : ℕ} (hk : k < ss.length),
      ∃ trace, (P.rawScanFrom score state ss)[k]? = some trace ∧
        trace.step = ss.get ⟨k, hk⟩ := by
  intro state ss
  induction ss generalizing state with
  | nil => simp
  | cons s ss ih =>
      intro k hk
      cases k with
      | zero =>
          refine ⟨P.rawUpdate score s state, ?_, ?_⟩
          · simp [PredicateWindowSchedule.rawScanFrom]
          · simp [PredicateWindowSchedule.rawUpdate]
      | succ k =>
          have hk' : k < ss.length := by simpa using hk
          let nextState : RawState ι :=
            { pending := (P.rawUpdate score s state).pending
              deque := (P.rawUpdate score s state).after }
          obtain ⟨trace, htrace, hstep⟩ :=
            ih (state := nextState) hk'
          refine ⟨trace, ?_, ?_⟩
          · simpa [PredicateWindowSchedule.rawScanFrom] using htrace
          · simpa using hstep

/-- [A predicate schedule](hyp:P), [a raw score](hyp:score), and [a fallback score](hyp:fallback)
have [raw operation cost exactly equal to the generic compiled position-scan cost](goal). -/
theorem rawScanCost_eq_scanCost [LinearOrder α]
    (P : PredicateWindowSchedule keys steps) (score : ι → α) (fallback : α) :
    P.rawScanCost score = scanCost (keyedStream keys score fallback) P.schedule := by
  let stream := keyedStream keys score fallback
  let generic := scan stream P.schedule
  let raw := P.rawScan score
  have hmap : generic.map (mapStepTrace keys) = raw.map RawStepTrace.dequeTrace :=
    scan_predicateSchedule_state_eq P score fallback
  have hfields : ∀ trace ∈ generic,
      (∀ i ∈ trace.pushed, i < keys.length) ∧
      (∀ i ∈ trace.frontPopped, i < keys.length) ∧
      (∀ i ∈ trace.backPopped, i < keys.length) := by
    intro trace htrace
    have h := scan_fields_bound stream P.schedule trace htrace
    exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  have hpushed := positionsToKeys_flatMap_length_eq keys generic StepTrace.pushed
    (fun trace htrace => (hfields trace htrace).1)
  have hfront := positionsToKeys_flatMap_length_eq keys generic StepTrace.frontPopped
    (fun trace htrace => (hfields trace htrace).2.1)
  have hback := positionsToKeys_flatMap_length_eq keys generic StepTrace.backPopped
    (fun trace htrace => (hfields trace htrace).2.2)
  have hoperations := congrArg
    (fun ts : List (RawDequeTrace ι) =>
      (ts.flatMap RawDequeTrace.pushed).length +
        (ts.flatMap RawDequeTrace.frontPopped).length +
          (ts.flatMap RawDequeTrace.backPopped).length) hmap
  simp only [List.flatMap_map, mapStepTrace,
    RawStepTrace.dequeTrace] at hoperations
  rw [hpushed, hfront, hback] at hoperations
  have hop : dequeOperations stream generic = rawDequeOperations raw := by
    simpa [dequeOperations, TracePushed, TraceFrontPopped, TraceBackPopped,
      rawDequeOperations, rawTracePushed, rawTraceFrontPopped, rawTraceBackPopped]
      using hoperations
  unfold PredicateWindowSchedule.rawScanCost scanCost
  have hs : P.schedule.steps = steps.length := P.schedule_steps
  change steps.length + rawDequeOperations raw = P.schedule.steps + dequeOperations stream generic
  omega

/-- [A predicate schedule](hyp:P), [a raw score](hyp:score), and [a fallback score](hyp:fallback)
have [raw peak storage exactly equal to generic compiled position-scan peak storage](goal). -/
theorem rawPeakStored_eq_peakStored [LinearOrder α]
    (P : PredicateWindowSchedule keys steps) (score : ι → α) (fallback : α) :
    rawPeakStored (P.rawScan score) =
      peakStored (keyedStream keys score fallback)
        (scan (keyedStream keys score fallback) P.schedule) := by
  let stream := keyedStream keys score fallback
  let generic := scan stream P.schedule
  let raw := P.rawScan score
  have hmap : generic.map (mapStepTrace keys) = raw.map RawStepTrace.dequeTrace :=
    scan_predicateSchedule_state_eq P score fallback
  have hlength : ∀ trace ∈ generic,
      (positionsToKeys keys trace.after).length = trace.after.length := by
    intro trace htrace
    exact positionsToKeys_length_eq keys trace.after
      (scan_fields_bound stream P.schedule trace htrace).2.2.1
  have hafter := congrArg
    (fun ts : List (RawDequeTrace ι) =>
      (ts.map (fun trace => trace.after.length)).foldl max 0) hmap
  simp only [List.map_map] at hafter
  change (generic.map (fun trace => (positionsToKeys keys trace.after).length)).foldl max 0 =
    (raw.map (fun trace => trace.after.length)).foldl max 0 at hafter
  have hmapped : generic.map (fun trace => (positionsToKeys keys trace.after).length) =
      generic.map (fun trace => trace.after.length) := by
    apply List.map_congr_left
    intro trace htrace
    exact hlength trace htrace
  rw [hmapped] at hafter
  simpa [rawPeakStored, peakStored, generic, raw, stream] using hafter.symm

/-- [A predicate schedule](hyp:P), [a raw score](hyp:score), and [a fallback score](hyp:fallback)
ensure [raw scan cost is at most twice the number of sparse keys plus the number of steps](goal). -/
theorem rawScanCost_le [LinearOrder α]
    (P : PredicateWindowSchedule keys steps) (score : ι → α) (fallback : α) :
    P.rawScanCost score ≤ 2 * keys.length + steps.length := by
  rw [rawScanCost_eq_scanCost P score fallback]
  simpa [keyedStream, P.schedule_steps] using
    scanCost_le (keyedStream keys score fallback) P.schedule

/-- [A predicate schedule](hyp:P), [a raw score](hyp:score), and [a fallback score](hyp:fallback)
ensure [raw peak deque storage is at most the number of sparse keys](goal). -/
theorem rawPeakStored_le_length [LinearOrder α]
    (P : PredicateWindowSchedule keys steps) (score : ι → α) (fallback : α) :
    rawPeakStored (P.rawScan score) ≤ keys.length := by
  rw [rawPeakStored_eq_peakStored P score fallback]
  simpa [keyedStream] using
    peakStored_le_length (keyedStream keys score fallback) P.schedule

/-- [A predicate schedule](hyp:P), [a raw score](hyp:score), [a fallback score](hyp:fallback), and
[a valid step position](hyp:hk) ensure [the raw deque stored there is no wider than its compiled
window](goal). -/
theorem rawScan_memory_le_windowWidth [LinearOrder α]
    (P : PredicateWindowSchedule keys steps) (score : ι → α) (fallback : α)
    {k : ℕ} (hk : k < steps.length) :
    ∃ trace, (P.rawScan score)[k]? = some trace ∧
      trace.after.length ≤
        P.rightEndpoint (steps.get ⟨k, hk⟩) - P.leftEndpoint (steps.get ⟨k, hk⟩) := by
  have hks : k < P.schedule.steps := by simpa [P.schedule_steps] using hk
  obtain ⟨generic, raw, hgeneric, hraw, hafter⟩ :=
    scan_predicateSchedule_after_eq P score fallback hk
  obtain ⟨found, hfound, hlen⟩ :=
    scan_memory_le_windowWidth (keyedStream keys score fallback) P.schedule hks
  have hfoundEq : found = generic := by
    exact Option.some.inj (hfound.symm.trans hgeneric)
  subst found
  refine ⟨raw, hraw, ?_⟩
  have hgenericMem : generic ∈ scan (keyedStream keys score fallback) P.schedule := by
    rcases List.getElem?_eq_some_iff.mp hgeneric with ⟨hkg, heq⟩
    exact List.mem_iff_getElem.mpr ⟨k, hkg, heq⟩
  have hbound := (scan_fields_bound (keyedStream keys score fallback) P.schedule
    generic hgenericMem).2.2.1
  have hmapLength := positionsToKeys_length_eq keys generic.after hbound
  rw [← hafter, hmapLength]
  have hwindow := P.schedule_window_get hk
  have hget : P.schedule.windows.get ⟨k, hks⟩ =
      P.windowAt (steps.get ⟨k, hk⟩) := by
    convert hwindow using 1
  calc
    generic.after.length ≤
        (P.schedule.windows.get ⟨k, hks⟩).right -
          (P.schedule.windows.get ⟨k, hks⟩).left := hlen
    _ = P.rightEndpoint (steps.get ⟨k, hk⟩) -
        P.leftEndpoint (steps.get ⟨k, hk⟩) := by
          rw [hget]
          rfl

/-- [A predicate schedule](hyp:P), [a raw score](hyp:score), [a fallback score](hyp:fallback),
[a valid step position](hyp:hk), and [a nonempty raw predicate window](hyp:hne) ensure [the raw
deque head is an active score maximizer, with equal maxima resolved at the greatest key
position](goal). -/
theorem rawScan_head_argmax [LinearOrder α]
    (P : PredicateWindowSchedule keys steps) (score : ι → α) (fallback : α)
    {k : ℕ} (hk : k < steps.length)
    (hne : ∃ i : Fin keys.length,
      P.entry (steps.get ⟨k, hk⟩) (keys.get i) ∧
        P.stay (steps.get ⟨k, hk⟩) (keys.get i)) :
    ∃ (trace : RawStepTrace ι κ) (head : ι) (tail : List ι)
        (headPos : Fin keys.length),
      (P.rawScan score)[k]? = some trace ∧
      trace.step = steps.get ⟨k, hk⟩ ∧
      trace.after = head :: tail ∧
      head = keys.get headPos ∧
      P.entry (steps.get ⟨k, hk⟩) head ∧
      P.stay (steps.get ⟨k, hk⟩) head ∧
      (∀ i : Fin keys.length,
        P.entry (steps.get ⟨k, hk⟩) (keys.get i) →
        P.stay (steps.get ⟨k, hk⟩) (keys.get i) →
        score (keys.get i) ≤ score head) ∧
      (∀ i : Fin keys.length,
        P.entry (steps.get ⟨k, hk⟩) (keys.get i) →
        P.stay (steps.get ⟨k, hk⟩) (keys.get i) →
        score (keys.get i) = score head → i.1 ≤ headPos.1) := by
  let stream := keyedStream keys score fallback
  have hks : k < P.schedule.steps := by simpa [P.schedule_steps] using hk
  have hwindowNonempty :
      (P.schedule.windows.get ⟨k, hks⟩).left <
        (P.schedule.windows.get ⟨k, hks⟩).right := by
    obtain ⟨i, hentry, hstay⟩ := hne
    have hactive := (P.active_schedule_iff hk i.isLt).mpr ⟨hentry, hstay⟩
    exact lt_of_le_of_lt hactive.1 hactive.2
  obtain ⟨generic, headIndex, posTail, hgeneric, hwindow, hposAfter,
      hheadActive, hmax⟩ :=
    scan_head_argmax stream P.schedule hks hwindowNonempty
  obtain ⟨validTrace, hvalidTrace, hvalidWindow, hvalid⟩ :=
    scan_valid_at stream P.schedule hks
  have hvg : validTrace = generic :=
    Option.some.inj (hvalidTrace.symm.trans hgeneric)
  subst validTrace
  rw [hwindow] at hvalid
  rw [hwindow] at hheadActive hmax
  obtain ⟨bridgeGeneric, raw, hbridgeGeneric, hraw, hmapAfter⟩ :=
    scan_predicateSchedule_after_eq P score fallback hk
  have hbg : bridgeGeneric = generic :=
    Option.some.inj (hbridgeGeneric.symm.trans hgeneric)
  subst bridgeGeneric
  have hheadBound : headIndex < keys.length := by
    exact lt_of_lt_of_le hheadActive.2
      (P.schedule.windows.get ⟨k, hks⟩).right_le_length
  let headPos : Fin keys.length := ⟨headIndex, hheadBound⟩
  let rawTail := positionsToKeys keys posTail
  have hrawAfter : raw.after = keys.get headPos :: rawTail := by
    rw [← hmapAfter, hposAfter]
    simp [positionsToKeys, headPos, rawTail, List.getElem?_eq_getElem hheadBound]
  obtain ⟨rawAt, hrawAt, hrawStep⟩ :=
    rawScanFrom_get_step P score { pending := keys, deque := [] } steps hk
  have hrawEq : rawAt = raw := by
    exact Option.some.inj (hrawAt.symm.trans hraw)
  subst rawAt
  have hheadPred :
      P.entry (steps.get ⟨k, hk⟩) (keys.get headPos) ∧
        P.stay (steps.get ⟨k, hk⟩) (keys.get headPos) := by
    exact (P.active_schedule_iff hk hheadBound).mp hheadActive
  have hstreamValue (i : Fin keys.length) : stream.value i.1 = score (keys.get i) := by
    simp [stream, keyedStream]
  have hretainedEqHead : ∀ j ∈ generic.after,
      stream.value j = stream.value headIndex → j = headIndex := by
    intro j hj heq
    rw [hposAfter] at hj
    rcases List.mem_cons.mp hj with rfl | hj
    · rfl
    · have hdec := hvalid.value_decreasing
      rw [hposAfter] at hdec
      have hlt := (List.pairwise_cons.mp hdec).1 j hj
      exfalso
      exact (ne_of_lt hlt) heq
  refine ⟨raw, keys.get headPos, rawTail, headPos, hraw, hrawStep,
    hrawAfter, rfl, hheadPred.1, hheadPred.2, ?_, ?_⟩
  · intro i hentry hstay
    have hactive := (P.active_schedule_iff hk i.isLt).mpr ⟨hentry, hstay⟩
    have hv := hmax i.1 hactive
    calc
      score (keys.get i) = stream.value i.1 := (hstreamValue i).symm
      _ ≤ stream.value headIndex := hv
      _ = score (keys.get headPos) := hstreamValue headPos
  · intro i hentry hstay heq
    have hactive := (P.active_schedule_iff hk i.isLt).mpr ⟨hentry, hstay⟩
    have hvalueEq : stream.value i.1 = stream.value headIndex := by
      calc
        stream.value i.1 = score (keys.get i) := hstreamValue i
        _ = score (keys.get headPos) := heq
        _ = stream.value headIndex := (hstreamValue headPos).symm
    by_cases hiq : i.1 ∈ generic.after
    · have := hretainedEqHead i.1 hiq hvalueEq
      simpa [headPos] using Nat.le_of_eq this
    · obtain ⟨j, hjq, hij, hvalue⟩ :=
        hvalid.dominates_omitted i.1 hactive i.isLt hiq
      have hjactive := (hvalid.active j hjq).1
      have hjle := hmax j hjactive
      have hjEq : stream.value j = stream.value headIndex := by
        exact le_antisymm hjle (by simpa [hvalueEq] using hvalue)
      have hjHead := hretainedEqHead j hjq hjEq
      subst j
      simpa [headPos] using Nat.le_of_lt hij

/-- [A raw-key list](hyp:keys), [a step list](hyp:steps), and [a finite pass count](hyp:passes)
determine a pass family with [one predicate-window schedule per pass](hyp:pass). -/
structure PredicatePasses (keys : List ι) (steps : List κ) (passes : ℕ) where
  pass : Fin passes → PredicateWindowSchedule keys steps

/-- [A fixed predicate-pass family](hyp:family) and [a raw score](hyp:score) determine [the sum of
the raw costs of all passes](goal). -/
noncomputable def PredicatePasses.totalRawCost [LinearOrder α]
    {passes : ℕ} (family : PredicatePasses keys steps passes) (score : ι → α) : ℕ :=
  ∑ p, (family.pass p).rawScanCost score

/-- [A fixed predicate-pass family](hyp:family), [a raw score](hyp:score), and [a fallback
score](hyp:fallback) ensure [total raw cost is at most twice pass count times key count plus pass
count times step count](goal). -/
theorem PredicatePasses.totalRawCost_le [LinearOrder α]
    {passes : ℕ} (family : PredicatePasses keys steps passes)
    (score : ι → α) (fallback : α) :
    family.totalRawCost score ≤ 2 * passes * keys.length + passes * steps.length := by
  unfold PredicatePasses.totalRawCost
  calc
    ∑ p, (family.pass p).rawScanCost score ≤
        ∑ _p : Fin passes, (2 * keys.length + steps.length) := by
      apply Finset.sum_le_sum
      intro p hp
      exact rawScanCost_le (family.pass p) score fallback
    _ = 2 * passes * keys.length + passes * steps.length := by
      simp [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm]

end Causalean.Mathlib.Algorithms.MonotoneWindowDeque

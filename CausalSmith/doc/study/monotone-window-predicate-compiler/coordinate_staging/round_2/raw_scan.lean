import Causalean.Mathlib.Algorithms.MonotoneWindowDeque.PredicateSchedule
import Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Scan

/-!
# Raw-key execution and representation equivalence

This module gives the executable raw-key view of a compiled predicate-window scan.  Pending keys
advance by `takeWhile` on entry, expired material is removed by `dropWhile` on stay, and surviving
new keys use the same rightmost-stable monotone back pruning as the position implementation.  The
main theorem identifies every mapped position-level trace with this raw-key trace.
-/

namespace Causalean.Mathlib.Algorithms.MonotoneWindowDeque

open Causalean.Mathlib.Algorithms.MonotoneWindowDeque

variable {ι κ α : Type*} {keys : List ι} {steps : List κ}

/-- [A raw-key list](hyp:keys), [a raw-key score](hyp:score), and [an out-of-bounds fallback
score](hyp:fallback) determine [the total position stream used by the generic deque](goal).  The
fallback is never observed at a valid position. -/
def keyedStream (keys : List ι) (score : ι → α) (fallback : α) : Stream α :=
  { length := keys.length
    value := fun i => (keys[i]?).map score |>.getD fallback }

/-- [A raw-key list](hyp:keys) and [a list of natural positions](hyp:positions) determine [the raw
keys obtained by safe lookup of every in-bounds position](goal). -/
def positionsToKeys (keys : List ι) (positions : List ℕ) : List ι :=
  positions.filterMap (fun i => keys[i]?)

/-- [A raw score](hyp:score), [a raw deque](hyp:q), and [a new key](hyp:x) determine [the deque
prefix after deleting its suffix of scores no larger than the new score](goal). -/
def rawPruneBack [LinearOrder α] (score : ι → α) (q : List ι) (x : ι) : List ι :=
  q.rdropWhile (fun y => decide (score y ≤ score x))

/-- [A raw score](hyp:score), [a raw deque](hyp:q), and [a new key](hyp:x) determine [the keys
removed from the back by the deterministic rightmost-stable tie policy](goal). -/
def rawPrunedBack [LinearOrder α] (score : ι → α) (q : List ι) (x : ι) : List ι :=
  q.rtakeWhile (fun y => decide (score y ≤ score x))

/-- [A raw score](hyp:score), [a raw deque](hyp:q), and [a new key](hyp:x) determine [one
rightmost-stable monotone push](goal); equal old scores are removed in favor of the new key. -/
def rawPush [LinearOrder α] (score : ι → α) (q : List ι) (x : ι) : List ι :=
  rawPruneBack score q x ++ [x]

/-- [A raw-key type](hyp:ι) determines a batch record with [the final key deque](hyp:state),
[the pushed keys](hyp:pushed), and [the keys removed from the back](hyp:backPopped). -/
structure RawPushBatch (ι : Type*) where
  state : List ι
  pushed : List ι
  backPopped : List ι

/-- [A raw score](hyp:score) determines [the recorded batch of rightmost-stable pushes](goal),
given by [leaving an empty input list unchanged](step:1) and [pushing the first key before
recursing on the remainder](step:2). -/
def rawPushAll [LinearOrder α] (score : ι → α) : List ι → List ι → RawPushBatch ι
  | q, [] => { state := q, pushed := [], backPopped := [] }
  | q, x :: xs =>
      let removed := rawPrunedBack score q x
      let rest := rawPushAll score (rawPush score q x) xs
      { state := rest.state
        pushed := x :: rest.pushed
        backPopped := removed ++ rest.backPopped }

/-- [One raw rightmost-stable push](hyp:score,q,x) has [the newly pushed key as its final
element](goal), including when all old entries tie with it. -/
theorem rawPush_getLast?_eq [LinearOrder α] (score : ι → α) (q : List ι) (x : ι) :
    (rawPush score q x).getLast? = some x := by
  simp [rawPush]

/-- [A key removed by rightmost-stable back pruning](hyp:hy) has [score no larger than the newly
pushed key](goal), so equal-score ties deterministically favor the newer occurrence. -/
theorem rawPrunedBack_score_le [LinearOrder α] (score : ι → α) (q : List ι) (x y : ι)
    (hy : y ∈ rawPrunedBack score q x) : score y ≤ score x := by
  have h := List.mem_rtakeWhile_imp hy
  simpa [rawPrunedBack] using h

/-- [A raw-key type](hyp:ι) determines a predicate-scan state with [the unentered suffix](hyp:pending)
and [the current raw-key deque](hyp:deque). -/
structure RawState (ι : Type*) where
  pending : List ι
  deque : List ι

/-- [A raw-key type](hyp:ι) determines a deque-update trace with [the deque before updating](hyp:before),
[the deque after expiration](hyp:afterExpiration), [the final deque](hyp:after), [the pushed
keys](hyp:pushed), [the front-popped keys](hyp:frontPopped), and [the back-popped keys](hyp:backPopped). -/
structure RawDequeTrace (ι : Type*) where
  before : List ι
  afterExpiration : List ι
  after : List ι
  pushed : List ι
  frontPopped : List ι
  backPopped : List ι

/-- [A raw-key type](hyp:ι) and [a step type](hyp:κ) determine a predicate-scan step record that
extends a deque update with [the current step](hyp:step), [the pending suffix before
updating](hyp:beforePending), [the pending suffix afterward](hyp:pending), and [the complete
entered prefix before expiration filtering](hyp:advanced). -/
structure RawStepTrace (ι κ : Type*) extends RawDequeTrace ι where
  step : κ
  beforePending : List ι
  pending : List ι
  advanced : List ι

/-- [A raw predicate step trace](hyp:trace) determines [its exact generic-shaped deque trace](goal). -/
def RawStepTrace.dequeTrace (trace : RawStepTrace ι κ) : RawDequeTrace ι :=
  trace.toRawDequeTrace

/-- [A predicate schedule](hyp:P), [a raw score](hyp:score), [a step](hyp:s), and [a raw state](hyp:state)
determine [the next recorded raw-key update](goal).  It advances entry by `takeWhile`, removes the
non-staying prefixes by `dropWhile`, and pushes precisely the surviving new suffix. -/
noncomputable def PredicateWindowSchedule.rawUpdate [LinearOrder α]
    (P : PredicateWindowSchedule keys steps) (score : ι → α) (s : κ)
    (state : RawState ι) : RawStepTrace ι κ := by
  let advanced := state.pending.takeWhile (P.entryTest s)
  let pending := state.pending.dropWhile (P.entryTest s)
  let afterExpiration := state.deque.dropWhile (P.expiredTest s)
  let frontPopped := state.deque.takeWhile (P.expiredTest s)
  let survivingNew := advanced.dropWhile (P.expiredTest s)
  let batch := rawPushAll score afterExpiration survivingNew
  exact
    { step := s
      beforePending := state.pending
      pending := pending
      advanced := advanced
      before := state.deque
      afterExpiration := afterExpiration
      after := batch.state
      pushed := batch.pushed
      frontPopped := frontPopped
      backPopped := batch.backPopped }

/-- [A predicate schedule](hyp:P) and [a raw score](hyp:score) determine [the raw trace obtained by
folding over a supplied suffix of steps from a supplied state](goal). -/
noncomputable def PredicateWindowSchedule.rawScanFrom [LinearOrder α]
    (P : PredicateWindowSchedule keys steps) (score : ι → α) :
    RawState ι → List κ → List (RawStepTrace ι κ)
  | _, [] => []
  | state, s :: ss =>
      let trace := P.rawUpdate score s state
      trace :: P.rawScanFrom score { pending := trace.pending, deque := trace.after } ss

/-- [A predicate schedule](hyp:P) and [a raw score](hyp:score) determine [the complete raw-key scan
from all keys pending and an empty deque](goal). -/
noncomputable def PredicateWindowSchedule.rawScan [LinearOrder α]
    (P : PredicateWindowSchedule keys steps) (score : ι → α) : List (RawStepTrace ι κ) :=
  P.rawScanFrom score { pending := keys, deque := [] } steps

/-- [A predicate schedule](hyp:P) and [a raw score](hyp:score) produce [one raw trace entry per
step](goal). -/
theorem PredicateWindowSchedule.length_rawScan [LinearOrder α]
    (P : PredicateWindowSchedule keys steps) (score : ι → α) :
    (P.rawScan score).length = steps.length := by
  have hlength : ∀ (state : RawState ι) (ss : List κ),
      (P.rawScanFrom score state ss).length = ss.length := by
    intro state ss
    induction ss generalizing state with
    | nil => rfl
    | cons s ss ih =>
        simp only [rawScanFrom, List.length_cons]
        rw [ih]
  exact hlength { pending := keys, deque := [] } steps

/-- [A raw-key list](hyp:keys) maps [one generic position-level step](hyp:trace) to [the exact
raw-key deque trace](goal) by safe lookup in every list-valued field. -/
def mapStepTrace (keys : List ι) {stream : Stream α} (trace : StepTrace stream) : RawDequeTrace ι :=
  { before := positionsToKeys keys trace.before
    afterExpiration := positionsToKeys keys trace.afterExpiration
    after := positionsToKeys keys trace.after
    pushed := positionsToKeys keys trace.pushed
    frontPopped := positionsToKeys keys trace.frontPopped
    backPopped := positionsToKeys keys trace.backPopped }

private theorem positionsToKeys_cons_of_lt (keys : List ι) (i : ℕ) (is : List ℕ)
    (hi : i < keys.length) :
    positionsToKeys keys (i :: is) = keys[i] :: positionsToKeys keys is := by
  simp [positionsToKeys, List.getElem?_eq_getElem hi]

private theorem positionsToKeys_append (keys : List ι) (is js : List ℕ) :
    positionsToKeys keys (is ++ js) =
      positionsToKeys keys is ++ positionsToKeys keys js := by
  simp [positionsToKeys]

private theorem positionsToKeys_range' (keys : List ι) (start count : ℕ)
    (hbound : start + count ≤ keys.length) :
    positionsToKeys keys (List.range' start count) =
      (keys.drop start).take count := by
  induction count generalizing start with
  | zero => simp [positionsToKeys]
  | succ count ih =>
      have hstart : start < keys.length := by omega
      rw [List.range'_succ, positionsToKeys_cons_of_lt keys start _ hstart,
        List.drop_eq_getElem_cons hstart]
      simp only [List.take_succ_cons]
      rw [ih (start := start + 1) (by omega)]

private theorem dropWhile_map_of_eq {A B : Type*} (f : A → B)
    (p : A → Bool) (q : B → Bool) : ∀ (xs : List A),
    (∀ x ∈ xs, p x = q (f x)) →
      (xs.map f).dropWhile q = (xs.dropWhile p).map f := by
  intro xs h
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx := h x (by simp)
      have hxs : ∀ y ∈ xs, p y = q (f y) := by
        intro y hy
        exact h y (by simp [hy])
      simp only [List.map_cons, List.dropWhile_cons, hx]
      split <;> simp_all

private theorem takeWhile_map_of_eq {A B : Type*} (f : A → B)
    (p : A → Bool) (q : B → Bool) : ∀ (xs : List A),
    (∀ x ∈ xs, p x = q (f x)) →
      (xs.map f).takeWhile q = (xs.takeWhile p).map f := by
  intro xs h
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx := h x (by simp)
      have hxs : ∀ y ∈ xs, p y = q (f y) := by
        intro y hy
        exact h y (by simp [hy])
      simp only [List.map_cons, List.takeWhile_cons, hx]
      split <;> simp_all

private theorem rdropWhile_map_of_eq {A B : Type*} (f : A → B)
    (p : A → Bool) (q : B → Bool) (xs : List A)
    (h : ∀ x ∈ xs, p x = q (f x)) :
    (xs.map f).rdropWhile q = (xs.rdropWhile p).map f := by
  simp only [List.rdropWhile, List.map_reverse]
  congr 1
  rw [← List.map_reverse]
  apply dropWhile_map_of_eq
  intro x hx
  exact h x (by simpa using hx)

private theorem rtakeWhile_map_of_eq {A B : Type*} (f : A → B)
    (p : A → Bool) (q : B → Bool) (xs : List A)
    (h : ∀ x ∈ xs, p x = q (f x)) :
    (xs.map f).rtakeWhile q = (xs.rtakeWhile p).map f := by
  simp only [List.rtakeWhile, List.map_reverse]
  congr 1
  rw [← List.map_reverse]
  apply takeWhile_map_of_eq
  intro x hx
  exact h x (by simpa using hx)

private theorem positionsToKeys_eq_map_getD (keys : List ι) (is : List ℕ) (fallback : ι)
    (hbound : ∀ i ∈ is, i < keys.length) :
    positionsToKeys keys is = is.map (fun i => keys[i]?.getD fallback) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      have hi := hbound i (by simp)
      rw [positionsToKeys_cons_of_lt keys i is hi]
      simp only [List.map_cons, List.getElem?_eq_getElem hi, Option.getD_some, List.cons.injEq,
        true_and]
      apply ih
      intro j hj
      exact hbound j (by simp [hj])

private theorem positionsToKeys_dropWhile (keys : List ι) (is : List ℕ)
    (fallback : ι) (p : ℕ → Bool) (q : ι → Bool)
    (hbound : ∀ i ∈ is, i < keys.length)
    (htest : ∀ i ∈ is, p i = q (keys[i]?.getD fallback)) :
    positionsToKeys keys (is.dropWhile p) =
      (positionsToKeys keys is).dropWhile q := by
  rw [positionsToKeys_eq_map_getD keys is fallback hbound,
    positionsToKeys_eq_map_getD keys (is.dropWhile p) fallback]
  · symm
    apply dropWhile_map_of_eq
    intro i hi
    exact htest i hi
  · intro i hi
    exact hbound i ((List.dropWhile_suffix _).mem hi)

private theorem positionsToKeys_takeWhile (keys : List ι) (is : List ℕ)
    (fallback : ι) (p : ℕ → Bool) (q : ι → Bool)
    (hbound : ∀ i ∈ is, i < keys.length)
    (htest : ∀ i ∈ is, p i = q (keys[i]?.getD fallback)) :
    positionsToKeys keys (is.takeWhile p) =
      (positionsToKeys keys is).takeWhile q := by
  rw [positionsToKeys_eq_map_getD keys is fallback hbound,
    positionsToKeys_eq_map_getD keys (is.takeWhile p) fallback]
  · symm
    apply takeWhile_map_of_eq
    intro i hi
    exact htest i hi
  · intro i hi
    exact hbound i ((List.takeWhile_prefix _).mem hi)

private theorem positionsToKeys_rdropWhile (keys : List ι) (is : List ℕ)
    (fallback : ι) (p : ℕ → Bool) (q : ι → Bool)
    (hbound : ∀ i ∈ is, i < keys.length)
    (htest : ∀ i ∈ is, p i = q (keys[i]?.getD fallback)) :
    positionsToKeys keys (is.rdropWhile p) =
      (positionsToKeys keys is).rdropWhile q := by
  rw [positionsToKeys_eq_map_getD keys is fallback hbound,
    positionsToKeys_eq_map_getD keys (is.rdropWhile p) fallback]
  · symm
    apply rdropWhile_map_of_eq
    intro i hi
    exact htest i hi
  · intro i hi
    exact hbound i ((List.rdropWhile_prefix _ _).mem hi)

private theorem positionsToKeys_rtakeWhile (keys : List ι) (is : List ℕ)
    (fallback : ι) (p : ℕ → Bool) (q : ι → Bool)
    (hbound : ∀ i ∈ is, i < keys.length)
    (htest : ∀ i ∈ is, p i = q (keys[i]?.getD fallback)) :
    positionsToKeys keys (is.rtakeWhile p) =
      (positionsToKeys keys is).rtakeWhile q := by
  rw [positionsToKeys_eq_map_getD keys is fallback hbound,
    positionsToKeys_eq_map_getD keys (is.rtakeWhile p) fallback]
  · symm
    apply rtakeWhile_map_of_eq
    intro i hi
    exact htest i hi
  · intro i hi
    exact hbound i ((List.rtakeWhile_suffix _ _).mem hi)

private theorem entry_of_lt_rightEndpoint
    (P : PredicateWindowSchedule keys steps) (s : κ) {i : ℕ}
    (hi : i < P.rightEndpoint s) :
    P.entry s (keys.get ⟨i, lt_of_lt_of_le hi (P.rightEndpoint_le_length s)⟩) := by
  have hir : i < keys.length := lt_of_lt_of_le hi (P.rightEndpoint_le_length s)
  have hitake : i < (keys.take (P.rightEndpoint s)).length := by
    simpa [List.length_take, Nat.min_eq_left (P.rightEndpoint_le_length s)] using hi
  have hmem : keys.get ⟨i, hir⟩ ∈ keys.take (P.rightEndpoint s) := by
    simpa [List.getElem_take] using List.getElem_mem hitake
  rw [P.take_rightEndpoint_eq_entered s] at hmem
  have htest := List.mem_takeWhile_imp (by simpa [PredicateWindowSchedule.entered] using hmem)
  simpa [PredicateWindowSchedule.entryTest] using htest

private theorem expiredTest_getElem_eq
    (P : PredicateWindowSchedule keys steps) (s : κ) {i : ℕ}
    (hi : i < P.rightEndpoint s) :
    P.expiredTest s
      (keys.get ⟨i, lt_of_lt_of_le hi (P.rightEndpoint_le_length s)⟩) =
        decide (i < P.leftEndpoint s) := by
  classical
  have hir : i < keys.length := lt_of_lt_of_le hi (P.rightEndpoint_le_length s)
  have hentry := entry_of_lt_rightEndpoint P s hi
  change decide (¬P.stay s (keys.get ⟨i, hir⟩)) =
    decide (i < P.leftEndpoint s)
  rw [decide_eq_decide]
  constructor
  · intro hnotStay
    by_contra hnotLt
    have hactive : Active (P.windowAt s) i := ⟨Nat.le_of_not_gt hnotLt, hi⟩
    exact hnotStay ((P.active_windowAt_iff s hir).mp hactive).2
  · intro hlt hstay
    have hactive := (P.active_windowAt_iff s hir).mpr ⟨hentry, hstay⟩
    exact (Nat.not_lt_of_ge hactive.1) hlt

private theorem range'_dropWhile_lt (start count left : ℕ)
    (hleft : left ≤ start + count) :
    (List.range' start count).dropWhile (fun i => decide (i < left)) =
      List.range' (max start left) (start + count - max start left) := by
  induction count generalizing start with
  | zero =>
      have h : left ≤ start := by omega
      simp [max_eq_left h]
  | succ count ih =>
      rw [List.range'_succ]
      by_cases h : start < left
      · simp only [List.dropWhile_cons, decide_eq_true_eq, h, if_true]
        rw [ih (start := start + 1) (by omega)]
        rw [max_eq_right (by omega), max_eq_right (by omega)]
        congr 1
        omega
      · have hle : left ≤ start := Nat.le_of_not_gt h
        simp only [List.dropWhile_cons, decide_eq_true_eq, h, if_false,
          max_eq_left hle]
        rw [← List.range'_succ]
        congr 1
        omega

private theorem positionsToKeys_pruneBack [LinearOrder α]
    (keys : List ι) (score : ι → α) (fallback : α)
    (q : List ℕ) (i : ℕ) (hi : i < keys.length)
    (hq : ∀ j ∈ q, j < keys.length) :
    positionsToKeys keys (pruneBack (keyedStream keys score fallback) q i) =
      rawPruneBack score (positionsToKeys keys q) keys[i] := by
  unfold pruneBack rawPruneBack
  apply positionsToKeys_rdropWhile keys q keys[i]
  · exact hq
  · intro j hj
    simp [keyedStream, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem (hq j hj)]

private theorem positionsToKeys_prunedBack [LinearOrder α]
    (keys : List ι) (score : ι → α) (fallback : α)
    (q : List ℕ) (i : ℕ) (hi : i < keys.length)
    (hq : ∀ j ∈ q, j < keys.length) :
    positionsToKeys keys (prunedBack (keyedStream keys score fallback) q i) =
      rawPrunedBack score (positionsToKeys keys q) keys[i] := by
  unfold prunedBack rawPrunedBack
  apply positionsToKeys_rtakeWhile keys q keys[i]
  · exact hq
  · intro j hj
    simp [keyedStream, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem (hq j hj)]

private theorem positionsToKeys_push [LinearOrder α]
    (keys : List ι) (score : ι → α) (fallback : α)
    (q : List ℕ) (i : ℕ) (hi : i < keys.length)
    (hq : ∀ j ∈ q, j < keys.length) :
    positionsToKeys keys (push (keyedStream keys score fallback) q i) =
      rawPush score (positionsToKeys keys q) keys[i] := by
  rw [push, rawPush, positionsToKeys_append,
    positionsToKeys_pruneBack keys score fallback q i hi hq]
  simp [positionsToKeys, List.getElem?_eq_getElem hi]

private theorem push_bound [LinearOrder α] (stream : Stream α)
    (q : List ℕ) (i bound : ℕ) (hi : i < bound)
    (hq : ∀ j ∈ q, j < bound) :
    ∀ j ∈ push stream q i, j < bound := by
  intro j hj
  rcases (mem_push_iff stream q i j).mp hj with hj | rfl
  · exact hq j ((pruneBack_prefix stream q i).mem hj)
  · exact hi

private theorem pushAll_bound [LinearOrder α] (stream : Stream α)
    (q indices : List ℕ) (bound : ℕ)
    (hq : ∀ j ∈ q, j < bound) (his : ∀ i ∈ indices, i < bound) :
    ∀ j ∈ (pushAll stream q indices).state, j < bound := by
  induction indices generalizing q with
  | nil => simpa [pushAll] using hq
  | cons i indices ih =>
      apply ih (q := push stream q i)
      · exact push_bound stream q i bound (his i (by simp)) hq
      · intro j hj
        exact his j (by simp [hj])

private theorem positionsToKeys_pushAll [LinearOrder α]
    (keys : List ι) (score : ι → α) (fallback : α)
    (q indices : List ℕ)
    (hq : ∀ j ∈ q, j < keys.length)
    (his : ∀ i ∈ indices, i < keys.length) :
    let generic := pushAll (keyedStream keys score fallback) q indices
    let raw := rawPushAll score (positionsToKeys keys q) (positionsToKeys keys indices)
    positionsToKeys keys generic.state = raw.state ∧
      positionsToKeys keys generic.pushed = raw.pushed ∧
      positionsToKeys keys generic.backPopped = raw.backPopped ∧
      ∀ j ∈ generic.state, j < keys.length := by
  induction indices generalizing q with
  | nil =>
      simp only [pushAll]
      exact ⟨rfl, rfl, rfl, hq⟩
  | cons i indices ih =>
      have hi : i < keys.length := his i (by simp)
      have his' : ∀ j ∈ indices, j < keys.length := by
        intro j hj
        exact his j (by simp [hj])
      have hpushBound := push_bound (keyedStream keys score fallback) q i keys.length hi hq
      have hrec := ih (q := push (keyedStream keys score fallback) q i) hpushBound his'
      have hpush := positionsToKeys_push keys score fallback q i hi hq
      have hpopped := positionsToKeys_prunedBack keys score fallback q i hi hq
      rw [hpush] at hrec
      simp only [positionsToKeys_cons_of_lt keys i indices hi, pushAll, rawPushAll,
        hpopped, positionsToKeys_append]
      rcases hrec with ⟨hstate, hpushed, hback, hbound⟩
      refine ⟨hstate, ?_, ?_, hbound⟩
      · rw [positionsToKeys_cons_of_lt keys i _ hi]
        exact congrArg (List.cons keys[i]) hpushed
      · exact congrArg (fun tail => rawPrunedBack score
          (positionsToKeys keys q) keys[i] ++ tail) hback

private theorem takeWhile_drop_eq_drop_takeWhile {A : Type*}
    (p : A → Bool) (xs : List A) (n : ℕ) (h : n ≤ (xs.takeWhile p).length) :
    (xs.drop n).takeWhile p = (xs.takeWhile p).drop n := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
      cases xs with
      | nil => simp at h
      | cons x xs =>
          cases hx : p x with
          | false => simp [hx] at h
          | true =>
              simp only [List.takeWhile_cons, hx, if_true, List.drop_succ_cons]
              apply ih
              simpa [hx] using h

private theorem dropWhile_eq_drop_takeWhile_length {A : Type*}
    (p : A → Bool) (xs : List A) :
    xs.dropWhile p = xs.drop (xs.takeWhile p).length := by
  symm
  calc
    xs.drop (xs.takeWhile p).length =
        (xs.takeWhile p ++ xs.dropWhile p).drop (xs.takeWhile p).length := by
      rw [List.takeWhile_append_dropWhile]
    _ = xs.dropWhile p := List.drop_left

private theorem advanced_eq_positionsToKeys
    (P : PredicateWindowSchedule keys steps) (s : κ) (oldRight : ℕ)
    (hright : oldRight ≤ P.rightEndpoint s) :
    (keys.drop oldRight).takeWhile (P.entryTest s) =
      positionsToKeys keys
        (List.range' oldRight (P.rightEndpoint s - oldRight)) := by
  rw [takeWhile_drop_eq_drop_takeWhile (P.entryTest s) keys oldRight hright,
    show keys.takeWhile (P.entryTest s) = keys.take (P.rightEndpoint s) by
      simpa [PredicateWindowSchedule.entered] using
        (P.take_rightEndpoint_eq_entered s).symm]
  rw [positionsToKeys_range' keys oldRight (P.rightEndpoint s - oldRight)]
  · rw [List.drop_take]
  · rw [Nat.add_sub_of_le hright]
    exact P.rightEndpoint_le_length s

private theorem pending_eq_drop_rightEndpoint
    (P : PredicateWindowSchedule keys steps) (s : κ) (oldRight : ℕ)
    (hright : oldRight ≤ P.rightEndpoint s) :
    (keys.drop oldRight).dropWhile (P.entryTest s) =
      keys.drop (P.rightEndpoint s) := by
  rw [dropWhile_eq_drop_takeWhile_length]
  have hadv := congrArg List.length (advanced_eq_positionsToKeys P s oldRight hright)
  rw [positionsToKeys_range' keys oldRight (P.rightEndpoint s - oldRight)] at hadv
  · simp only [List.length_take, List.length_drop] at hadv
    have hsub : P.rightEndpoint s - oldRight ≤ keys.length - oldRight :=
      Nat.sub_le_sub_right (P.rightEndpoint_le_length s) oldRight
    rw [Nat.min_eq_left hsub] at hadv
    rw [hadv, List.drop_drop, Nat.add_sub_of_le hright]
  · rw [Nat.add_sub_of_le hright]
    exact P.rightEndpoint_le_length s

private theorem newlyEntered_eq_positionsToKeys
    (P : PredicateWindowSchedule keys steps) (s : κ) (oldRight : ℕ)
    (hright : oldRight ≤ P.rightEndpoint s) :
    ((keys.drop oldRight).takeWhile (P.entryTest s)).dropWhile (P.expiredTest s) =
      positionsToKeys keys
        (List.range' (max oldRight (P.leftEndpoint s))
          (P.rightEndpoint s - max oldRight (P.leftEndpoint s))) := by
  rw [advanced_eq_positionsToKeys P s oldRight hright]
  let indices := List.range' oldRight (P.rightEndpoint s - oldRight)
  change (positionsToKeys keys indices).dropWhile (P.expiredTest s) = _
  have hibound : ∀ i ∈ indices, i < keys.length := by
    intro i hi
    have hirange := (List.mem_range'_1.mp hi).2
    rw [Nat.add_sub_of_le hright] at hirange
    exact lt_of_lt_of_le hirange (P.rightEndpoint_le_length s)
  by_cases hempty : indices = []
  · have hcount : P.rightEndpoint s - oldRight = 0 := by
      simpa [indices] using congrArg List.length hempty
    have heq : oldRight = P.rightEndpoint s := by omega
    rw [hempty]
    simp [positionsToKeys, heq,
      max_eq_left (P.leftEndpoint_le_rightEndpoint s)]
  · obtain ⟨fallbackIndex, hfallbackMem⟩ := List.exists_mem_of_ne_nil indices hempty
    have hfallback := hibound fallbackIndex hfallbackMem
    rw [← positionsToKeys_dropWhile keys indices
      (keys.get ⟨fallbackIndex, hibound fallbackIndex hfallbackMem⟩)
      (fun i => decide (i < P.leftEndpoint s)) (P.expiredTest s) hibound]
    · have hleftsum : P.leftEndpoint s ≤
          oldRight + (P.rightEndpoint s - oldRight) := by
        rw [Nat.add_sub_of_le hright]
        exact P.leftEndpoint_le_rightEndpoint s
      rw [range'_dropWhile_lt oldRight (P.rightEndpoint s - oldRight)
          (P.leftEndpoint s) hleftsum]
      rw [Nat.add_sub_of_le hright]
    · intro i hi
      have hirange := (List.mem_range'_1.mp hi).2
      rw [Nat.add_sub_of_le hright] at hirange
      have hexp := expiredTest_getElem_eq P s hirange
      symm
      simpa [List.getElem?_eq_getElem (hibound i hi)] using hexp

private theorem positionsToKeys_expireFront
    (P : PredicateWindowSchedule keys steps) (s : κ) (q : List ℕ)
    (hq : ∀ i ∈ q, i < P.rightEndpoint s) :
    positionsToKeys keys (expireFront (P.leftEndpoint s) q) =
      (positionsToKeys keys q).dropWhile (P.expiredTest s) := by
  by_cases hempty : q = []
  · simp [hempty, positionsToKeys, expireFront]
  · obtain ⟨fallbackIndex, hfallbackMem⟩ := List.exists_mem_of_ne_nil q hempty
    have hbound : ∀ i ∈ q, i < keys.length := by
      intro i hi
      exact lt_of_lt_of_le (hq i hi) (P.rightEndpoint_le_length s)
    unfold expireFront
    apply positionsToKeys_dropWhile keys q
      (keys.get ⟨fallbackIndex, hbound fallbackIndex hfallbackMem⟩)
    · exact hbound
    · intro i hi
      symm
      simpa [List.getElem?_eq_getElem (hbound i hi)] using
        expiredTest_getElem_eq P s (hq i hi)

private theorem positionsToKeys_expiredFront
    (P : PredicateWindowSchedule keys steps) (s : κ) (q : List ℕ)
    (hq : ∀ i ∈ q, i < P.rightEndpoint s) :
    positionsToKeys keys (expiredFront (P.leftEndpoint s) q) =
      (positionsToKeys keys q).takeWhile (P.expiredTest s) := by
  by_cases hempty : q = []
  · simp [hempty, positionsToKeys, expiredFront]
  · obtain ⟨fallbackIndex, hfallbackMem⟩ := List.exists_mem_of_ne_nil q hempty
    have hbound : ∀ i ∈ q, i < keys.length := by
      intro i hi
      exact lt_of_lt_of_le (hq i hi) (P.rightEndpoint_le_length s)
    unfold expiredFront
    apply positionsToKeys_takeWhile keys q
      (keys.get ⟨fallbackIndex, hbound fallbackIndex hfallbackMem⟩)
    · exact hbound
    · intro i hi
      symm
      simpa [List.getElem?_eq_getElem (hbound i hi)] using
        expiredTest_getElem_eq P s (hq i hi)

private theorem rawUpdate_bridge [LinearOrder α]
    (P : PredicateWindowSchedule keys steps) (score : ι → α) (fallback : α)
    (s : κ) (oldRight : ℕ) (q : List ℕ)
    (hright : oldRight ≤ P.rightEndpoint s)
    (hq : ∀ i ∈ q, i < P.rightEndpoint s) :
    let generic := update (keyedStream keys score fallback) oldRight (P.windowAt s) q
    let raw := P.rawUpdate score s
      { pending := keys.drop oldRight, deque := positionsToKeys keys q }
    mapStepTrace keys generic = raw.dequeTrace ∧
      raw.pending = keys.drop (P.rightEndpoint s) ∧
      positionsToKeys keys generic.after = raw.after ∧
      ∀ i ∈ generic.after, i < P.rightEndpoint s := by
  classical
  let entered := List.range' (max oldRight (P.leftEndpoint s))
    (P.rightEndpoint s - max oldRight (P.leftEndpoint s))
  have hqBound : ∀ i ∈ q, i < keys.length := by
    intro i hi
    exact lt_of_lt_of_le (hq i hi) (P.rightEndpoint_le_length s)
  have hafterExpBound : ∀ i ∈ expireFront (P.leftEndpoint s) q,
      i < keys.length := by
    intro i hi
    exact hqBound i ((List.dropWhile_suffix _).mem hi)
  have henteredBound : ∀ i ∈ entered, i < keys.length := by
    intro i hi
    have hirange := (List.mem_range'_1.mp hi).2
    have hmax : max oldRight (P.leftEndpoint s) ≤ P.rightEndpoint s :=
      max_le hright (P.leftEndpoint_le_rightEndpoint s)
    rw [Nat.add_sub_of_le hmax] at hirange
    exact lt_of_lt_of_le hirange (P.rightEndpoint_le_length s)
  have hExpiration := positionsToKeys_expireFront P s q hq
  have hFront := positionsToKeys_expiredFront P s q hq
  have hEntered := newlyEntered_eq_positionsToKeys P s oldRight hright
  have hPending := pending_eq_drop_rightEndpoint P s oldRight hright
  have hbatch := positionsToKeys_pushAll keys score fallback
    (expireFront (P.leftEndpoint s) q) entered hafterExpBound henteredBound
  rw [hExpiration, ← hEntered] at hbatch
  rcases hbatch with ⟨hstate, hpushed, hback, hstateBound⟩
  have hafterRight : ∀ i ∈
      (pushAll (keyedStream keys score fallback)
        (expireFront (P.leftEndpoint s) q) entered).state,
      i < P.rightEndpoint s := by
    apply pushAll_bound
    · intro i hi
      exact hq i ((List.dropWhile_suffix _).mem hi)
    · intro i hi
      have hirange := (List.mem_range'_1.mp hi).2
      have hmax : max oldRight (P.leftEndpoint s) ≤ P.rightEndpoint s :=
        max_le hright (P.leftEndpoint_le_rightEndpoint s)
      simpa [entered, Nat.add_sub_of_le hmax] using hirange
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [mapStepTrace, update, PredicateWindowSchedule.rawUpdate,
      PredicateWindowSchedule.windowAt, RawStepTrace.dequeTrace, entered,
      hExpiration, hFront, hEntered, hstate, hpushed, hback]
  · simpa [PredicateWindowSchedule.rawUpdate] using hPending
  · simpa [update, PredicateWindowSchedule.rawUpdate,
      PredicateWindowSchedule.windowAt, entered] using hstate
  · simpa [update, PredicateWindowSchedule.windowAt, entered] using hafterRight

private theorem scanFrom_bridge [LinearOrder α]
    (P : PredicateWindowSchedule keys steps) (score : ι → α) (fallback : α) :
    ∀ (ss : List κ),
      ss.Pairwise (fun s t => P.rightEndpoint s ≤ P.rightEndpoint t) →
      ∀ (oldRight : ℕ) (q : List ℕ),
        (∀ s ∈ ss, oldRight ≤ P.rightEndpoint s) →
        (∀ i ∈ q, i < oldRight) →
        (scanFrom (keyedStream keys score fallback) oldRight q
            (ss.map P.windowAt)).map (mapStepTrace keys) =
          (P.rawScanFrom score
            { pending := keys.drop oldRight, deque := positionsToKeys keys q } ss).map
              RawStepTrace.dequeTrace := by
  intro ss hpair oldRight q hright hq
  induction ss generalizing oldRight q with
  | nil => rfl
  | cons s ss ih =>
      have hp := List.pairwise_cons.mp hpair
      have hold : oldRight ≤ P.rightEndpoint s := hright s (by simp)
      have hqCurrent : ∀ i ∈ q, i < P.rightEndpoint s := by
        intro i hi
        exact lt_of_lt_of_le (hq i hi) hold
      let generic := update (keyedStream keys score fallback) oldRight (P.windowAt s) q
      let raw := P.rawUpdate score s
        { pending := keys.drop oldRight, deque := positionsToKeys keys q }
      have hbridge := rawUpdate_bridge P score fallback s oldRight q hold hqCurrent
      change mapStepTrace keys generic ::
          (scanFrom (keyedStream keys score fallback) (P.rightEndpoint s) generic.after
            (ss.map P.windowAt)).map (mapStepTrace keys) =
        raw.dequeTrace ::
          (P.rawScanFrom score { pending := raw.pending, deque := raw.after } ss).map
            RawStepTrace.dequeTrace
      rcases hbridge with ⟨htrace, hpending, hafter, hbound⟩
      rw [htrace]
      congr 1
      have htail := ih hp.2 (oldRight := P.rightEndpoint s) (q := generic.after)
        (by
          intro t ht
          exact hp.1 t ht)
        hbound
      rw [hpending, ← hafter]
      exact htail

/- Proof route for representation equivalence: strengthen the induction over `steps` with
`pending = keys.drop oldRight` and equality of mapped deques.  The Schedule endpoint-advancement
lemmas identify `advanced` and its surviving suffix with the generic consecutive range.  Mapping
commutes with front `takeWhile`/`dropWhile`; a separate induction shows that mapping commutes with
`pushAll`, including back-pop logs, because `keyedStream.value` agrees with `score` in bounds. -/

/-- [A predicate schedule](hyp:P), [a raw-key score](hyp:score), and [a fallback score](hyp:fallback)
have [the generic position scan mapped through raw-key lookup exactly equal to the corresponding
raw-key predicate scan](goal), including every deque state and push/pop log. -/
theorem scan_predicateSchedule_state_eq [LinearOrder α]
    (P : PredicateWindowSchedule keys steps) (score : ι → α) (fallback : α) :
    (scan (keyedStream keys score fallback) P.schedule).map (mapStepTrace keys) =
      (P.rawScan score).map RawStepTrace.dequeTrace := by
  have hpair : steps.Pairwise
      (fun s t => P.rightEndpoint s ≤ P.rightEndpoint t) :=
    P.entry_step_mono.imp (fun h => P.rightEndpoint_mono_of_entry h)
  have hbridge := scanFrom_bridge P score fallback steps hpair 0 []
    (by simp) (by simp)
  change (scanFrom (keyedStream keys score fallback) 0 initialDeque
      (steps.map P.windowAt)).map (mapStepTrace keys) =
    (P.rawScanFrom score { pending := keys, deque := [] } steps).map
      RawStepTrace.dequeTrace
  simpa [initialDeque, positionsToKeys] using hbridge

/-- [A predicate schedule](hyp:P), [a raw score](hyp:score), [a valid step position](hyp:hk), and
[a fallback score](hyp:fallback) have [the generic deque after that step mapped through key lookup
equal to the raw predicate-scan deque](goal). -/
theorem scan_predicateSchedule_after_eq [LinearOrder α]
    (P : PredicateWindowSchedule keys steps) (score : ι → α) (fallback : α)
    {k : ℕ} (hk : k < steps.length) :
    ∃ generic raw,
      (scan (keyedStream keys score fallback) P.schedule)[k]? = some generic ∧
      (P.rawScan score)[k]? = some raw ∧
      positionsToKeys keys generic.after = raw.after := by
  let genericTrace := scan (keyedStream keys score fallback) P.schedule
  let rawTrace := P.rawScan score
  have hGenericLength : genericTrace.length = steps.length := by
    rw [show genericTrace.length = P.schedule.steps by
      exact length_scan (keyedStream keys score fallback) P.schedule]
    exact P.schedule_steps
  have hRawLength : rawTrace.length = steps.length := by
    exact P.length_rawScan score
  have hgk : k < genericTrace.length := by simpa [hGenericLength] using hk
  have hrk : k < rawTrace.length := by simpa [hRawLength] using hk
  let generic := genericTrace.get ⟨k, hgk⟩
  let raw := rawTrace.get ⟨k, hrk⟩
  refine ⟨generic, raw, ?_, ?_, ?_⟩
  · exact List.getElem?_eq_getElem hgk
  · exact List.getElem?_eq_getElem hrk
  · have heq := congrArg (fun xs => xs[k]?)
      (scan_predicateSchedule_state_eq P score fallback)
    change (genericTrace.map (mapStepTrace keys))[k]? =
      (rawTrace.map RawStepTrace.dequeTrace)[k]? at heq
    simp only [List.getElem?_map, List.getElem?_eq_getElem hgk,
      List.getElem?_eq_getElem hrk, Option.map_some, Option.some.injEq] at heq
    exact congrArg RawDequeTrace.after heq

end Causalean.Mathlib.Algorithms.MonotoneWindowDeque

import Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Basic

/-!
# Compiling monotone raw-key predicates to position windows

This module turns entry and stay predicates on an arbitrary sparse list of raw keys into bounded
half-open position windows.  The hypotheses say exactly that entry sets are prefixes, stay sets are
suffixes, entry can only expand along the step list, and stay can only shrink.  No order or density
assumption is imposed on the raw key type itself.
-/

namespace Causalean.Mathlib.Algorithms.MonotoneWindowDeque

open Causalean.Mathlib.Algorithms.MonotoneWindowDeque

variable {ι κ : Type*} {keys : List ι} {steps : List κ}

/-- [A sparse raw-key list](hyp:keys) and [an ordered step list](hyp:steps) determine a predicate
window specification whose [entry predicate](hyp:entry), [stay predicate](hyp:stay),
[entry-prefix law](hyp:entry_prefix), [stay-suffix law](hyp:stay_suffix), [entry monotonicity
across steps](hyp:entry_step_mono), and [stay antitonicity across steps](hyp:stay_step_anti)
describe a monotone active window. -/
structure PredicateWindowSchedule (keys : List ι) (steps : List κ) where
  entry : κ → ι → Prop
  stay : κ → ι → Prop
  entry_prefix : ∀ (s : κ) {i j : ℕ} (hi : i < keys.length) (hj : j < keys.length),
    i ≤ j → entry s (keys.get ⟨j, hj⟩) → entry s (keys.get ⟨i, hi⟩)
  stay_suffix : ∀ (s : κ) {i j : ℕ} (hi : i < keys.length) (hj : j < keys.length),
    i ≤ j → stay s (keys.get ⟨i, hi⟩) → stay s (keys.get ⟨j, hj⟩)
  entry_step_mono : steps.Pairwise
    (fun s t => ∀ x ∈ keys, entry s x → entry t x)
  stay_step_anti : steps.Pairwise
    (fun s t => ∀ x ∈ keys, stay t x → stay s x)

namespace PredicateWindowSchedule

/-- [A predicate schedule](hyp:P), [a step](hyp:s), and [a raw key](hyp:x) determine [the Boolean
entry test used by executable list operations](goal). -/
noncomputable def entryTest (P : PredicateWindowSchedule keys steps) (s : κ) (x : ι) : Bool := by
  classical
  exact decide (P.entry s x)

/-- [A predicate schedule](hyp:P), [a step](hyp:s), and [a raw key](hyp:x) determine [the Boolean
test that the key has expired](goal). -/
noncomputable def expiredTest (P : PredicateWindowSchedule keys steps) (s : κ) (x : ι) : Bool := by
  classical
  exact decide (¬ P.stay s x)

/-- [A predicate schedule](hyp:P) and [a step](hyp:s) determine [the raw prefix that has entered by
that step](goal). -/
noncomputable def entered (P : PredicateWindowSchedule keys steps) (s : κ) : List ι := by
  exact keys.takeWhile (P.entryTest s)

/-- [A predicate schedule](hyp:P) and [a step](hyp:s) determine [the right position endpoint](goal),
namely the length of the entered raw-key prefix. -/
noncomputable def rightEndpoint (P : PredicateWindowSchedule keys steps) (s : κ) : ℕ :=
  (P.entered s).length

/-- [A predicate schedule](hyp:P) and [a step](hyp:s) determine [the expired prefix of entered
keys](goal), namely the initial segment that no longer satisfies the stay predicate. -/
noncomputable def expiredPrefix (P : PredicateWindowSchedule keys steps) (s : κ) : List ι := by
  exact (keys.take (P.rightEndpoint s)).takeWhile (P.expiredTest s)

/-- [A predicate schedule](hyp:P) and [a step](hyp:s) determine [the left position endpoint](goal),
namely the length of the expired prefix among entered keys. -/
noncomputable def leftEndpoint (P : PredicateWindowSchedule keys steps) (s : κ) : ℕ :=
  (P.expiredPrefix s).length

/- Proof route for this layer: first establish membership in `takeWhile` from the prefix law and
its negation from the first failed test.  Use those characterizations to prove the two endpoint
bounds and `active_windowAt_iff`.  Predicate inclusion then gives prefix inclusion/length
monotonicity.  The take/drop advancement identities follow from `takeWhile_append_dropWhile`,
`take_take`, `drop_take`, and the established endpoint inequalities. -/

private theorem lt_length_takeWhile_iff_of_prefix {α : Type*} (l : List α) (p : α → Bool)
    (hp : ∀ {i j : ℕ} (hi : i < l.length) (hj : j < l.length),
      i ≤ j → p (l.get ⟨j, hj⟩) = true → p (l.get ⟨i, hi⟩) = true) :
    ∀ {i : ℕ} (hi : i < l.length),
      i < (l.takeWhile p).length ↔ p (l.get ⟨i, hi⟩) = true := by
  induction l with
  | nil => simp
  | cons a l ih =>
      intro i hi
      cases hpa : p a with
      | false =>
          have hnot : p ((a :: l).get ⟨i, hi⟩) = false := by
            apply Bool.eq_false_iff.mpr
            intro h
            have hx := hp (by simp) hi (Nat.zero_le i) (by simpa using h)
            simp [hpa] at hx
          constructor
          · intro hlt
            simp [hpa] at hlt
          · intro htrue
            have htrue' : p ((a :: l).get ⟨i, hi⟩) = true := by
              simpa only [List.get_eq_getElem] using htrue
            rw [hnot] at htrue'
            exact Bool.noConfusion htrue'
      | true =>
          have hptail : ∀ {i j : ℕ} (hi : i < l.length) (hj : j < l.length),
              i ≤ j → p (l.get ⟨j, hj⟩) = true → p (l.get ⟨i, hi⟩) = true := by
            intro i j hi hj hij h
            simpa using hp (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hj)
              (Nat.succ_le_succ hij) (by simpa using h)
          cases i with
          | zero => simp [hpa]
          | succ i =>
              have hi' : i < l.length := by simpa using hi
              simpa [hpa] using ih hptail hi'

private theorem takeWhile_drop_eq_drop_takeWhile {α : Type*} (p : α → Bool)
    (l : List α) (n : ℕ) (h : n ≤ (l.takeWhile p).length) :
    (l.drop n).takeWhile p = (l.takeWhile p).drop n := by
  induction n generalizing l with
  | zero => simp
  | succ n ih =>
      cases l with
      | nil => simp at h
      | cons a l =>
          cases hpa : p a with
          | false => simp [hpa] at h
          | true =>
              simp only [List.takeWhile_cons, hpa, if_true, List.drop_succ_cons]
              apply ih
              simpa [hpa] using h

/-- [A predicate schedule](hyp:P) has [every right endpoint bounded by the raw-key count](goal). -/
theorem rightEndpoint_le_length (P : PredicateWindowSchedule keys steps) (s : κ) :
    P.rightEndpoint s ≤ keys.length := by
  exact (List.takeWhile_prefix _).length_le

/-- [A predicate schedule](hyp:P) has [every left endpoint bounded by its right endpoint](goal). -/
theorem leftEndpoint_le_rightEndpoint (P : PredicateWindowSchedule keys steps) (s : κ) :
    P.leftEndpoint s ≤ P.rightEndpoint s := by
  change ((keys.take (P.rightEndpoint s)).takeWhile (P.expiredTest s)).length ≤
    P.rightEndpoint s
  calc
    _ ≤ (keys.take (P.rightEndpoint s)).length := (List.takeWhile_prefix _).length_le
    _ = P.rightEndpoint s := by
      simp [List.length_take, Nat.min_eq_left (P.rightEndpoint_le_length s)]

/-- [A predicate schedule](hyp:P) and [a step](hyp:s) determine [a bounded half-open position
window](goal), including when the raw-key list or the active window is empty. -/
noncomputable def windowAt (P : PredicateWindowSchedule keys steps) (s : κ) : Window keys.length :=
  { left := P.leftEndpoint s
    right := P.rightEndpoint s
    left_le_right := P.leftEndpoint_le_rightEndpoint s
    right_le_length := P.rightEndpoint_le_length s }

/-- [A predicate schedule](hyp:P) has [its right prefix exactly equal to the `takeWhile` entry
segment](goal). -/
theorem take_rightEndpoint_eq_entered (P : PredicateWindowSchedule keys steps) (s : κ) :
    keys.take (P.rightEndpoint s) = P.entered s := by
  change keys.take (keys.takeWhile (P.entryTest s)).length = keys.takeWhile (P.entryTest s)
  calc
    _ = (keys.takeWhile (P.entryTest s) ++ keys.dropWhile (P.entryTest s)).take
        (keys.takeWhile (P.entryTest s)).length := by
      rw [List.takeWhile_append_dropWhile]
    _ = _ := List.take_left

/-- [A predicate schedule](hyp:P) has [its left prefix exactly equal to the `takeWhile` segment of
entered keys that fail the stay predicate](goal). -/
theorem take_leftEndpoint_eq_expiredPrefix (P : PredicateWindowSchedule keys steps) (s : κ) :
    (keys.take (P.rightEndpoint s)).take (P.leftEndpoint s) = P.expiredPrefix s := by
  change (keys.take (P.rightEndpoint s)).take (P.expiredPrefix s).length = P.expiredPrefix s
  rw [← List.takeWhile_append_dropWhile (p := P.expiredTest s)
    (l := keys.take (P.rightEndpoint s))]
  exact List.take_left

/-- [A predicate schedule](hyp:P) has [the keys between its endpoints exactly equal to dropping the
non-staying prefix from the entered prefix](goal). -/
theorem drop_leftEndpoint_eq_dropWhile (P : PredicateWindowSchedule keys steps) (s : κ) :
    (keys.take (P.rightEndpoint s)).drop (P.leftEndpoint s) =
      (keys.take (P.rightEndpoint s)).dropWhile (P.expiredTest s) := by
  let l := keys.take (P.rightEndpoint s)
  change l.drop (l.takeWhile (P.expiredTest s)).length = l.dropWhile (P.expiredTest s)
  calc
    _ = (l.takeWhile (P.expiredTest s) ++ l.dropWhile (P.expiredTest s)).drop
        (l.takeWhile (P.expiredTest s)).length := by
      rw [List.takeWhile_append_dropWhile]
    _ = _ := List.drop_left

private theorem lt_rightEndpoint_iff_entry (P : PredicateWindowSchedule keys steps) (s : κ)
    {i : ℕ} (hi : i < keys.length) :
    i < P.rightEndpoint s ↔ P.entry s (keys.get ⟨i, hi⟩) := by
  change i < (keys.takeWhile (P.entryTest s)).length ↔ _
  rw [lt_length_takeWhile_iff_of_prefix keys (P.entryTest s) (hi := hi)]
  · simp [entryTest]
  · intro a b ha hb hab h
    simpa [entryTest] using P.entry_prefix s ha hb hab (by simpa [entryTest] using h)

private theorem lt_leftEndpoint_iff_not_stay (P : PredicateWindowSchedule keys steps) (s : κ)
    {i : ℕ} (hi : i < P.rightEndpoint s) :
    i < P.leftEndpoint s ↔
      ¬P.stay s (keys.get ⟨i, lt_of_lt_of_le hi (P.rightEndpoint_le_length s)⟩) := by
  let l := keys.take (P.rightEndpoint s)
  have hl : l.length = P.rightEndpoint s := by
    simp [l, List.length_take, Nat.min_eq_left (P.rightEndpoint_le_length s)]
  have hil : i < l.length := by simpa [hl]
  have hp : ∀ {a b : ℕ} (ha : a < l.length) (hb : b < l.length),
      a ≤ b → P.expiredTest s (l.get ⟨b, hb⟩) = true →
        P.expiredTest s (l.get ⟨a, ha⟩) = true := by
    intro a b ha hb hab hexp
    have haK : a < keys.length := lt_of_lt_of_le (by simpa [hl] using ha)
      (P.rightEndpoint_le_length s)
    have hbK : b < keys.length := lt_of_lt_of_le (by simpa [hl] using hb)
      (P.rightEndpoint_le_length s)
    have hexp' : ¬P.stay s (l.get ⟨b, hb⟩) := by
      simpa [expiredTest] using hexp
    apply (show P.expiredTest s (l.get ⟨a, ha⟩) = true from ?_)
    simp only [expiredTest, decide_eq_true_eq]
    intro hstay
    apply hexp'
    have hstayK : P.stay s (keys.get ⟨a, haK⟩) := by
      simpa [l, List.get_eq_getElem] using hstay
    have hout := P.stay_suffix s haK hbK hab hstayK
    simpa [l, List.get_eq_getElem] using hout
  have h := lt_length_takeWhile_iff_of_prefix l (P.expiredTest s) hp hil
  simpa [leftEndpoint, expiredPrefix, l, expiredTest, List.get_eq_getElem] using h

/-- [A predicate schedule](hyp:P), [a step](hyp:s), and [an in-bounds position](hyp:hi) satisfy
[the exact equivalence between position activity and the raw entry-and-stay predicates](goal). -/
theorem active_windowAt_iff (P : PredicateWindowSchedule keys steps) (s : κ)
    {i : ℕ} (hi : i < keys.length) :
    Active (P.windowAt s) i ↔
      P.entry s (keys.get ⟨i, hi⟩) ∧ P.stay s (keys.get ⟨i, hi⟩) := by
  constructor
  · rintro ⟨hli, hir⟩
    refine ⟨(P.lt_rightEndpoint_iff_entry s hi).mp hir, ?_⟩
    by_contra hstay
    exact (Nat.not_lt_of_ge hli) ((P.lt_leftEndpoint_iff_not_stay s hir).mpr hstay)
  · rintro ⟨hentry, hstay⟩
    have hir := (P.lt_rightEndpoint_iff_entry s hi).mpr hentry
    refine ⟨Nat.le_of_not_gt ?_, hir⟩
    intro hil
    exact ((P.lt_leftEndpoint_iff_not_stay s hir).mp hil) hstay

/-- [Predicate inclusion from an earlier step to a later step](hyp:hentry) makes [right endpoints
nondecreasing](goal). -/
theorem rightEndpoint_mono_of_entry (P : PredicateWindowSchedule keys steps) {s t : κ}
    (hentry : ∀ x ∈ keys, P.entry s x → P.entry t x) :
    P.rightEndpoint s ≤ P.rightEndpoint t := by
  by_contra h
  have hlt : P.rightEndpoint t < P.rightEndpoint s := Nat.lt_of_not_ge h
  have hi : P.rightEndpoint t < keys.length :=
    lt_of_lt_of_le hlt (P.rightEndpoint_le_length s)
  have hs := (P.lt_rightEndpoint_iff_entry s hi).mp hlt
  have ht := hentry _ (List.get_mem keys ⟨P.rightEndpoint t, hi⟩) hs
  exact (Nat.lt_irrefl _) ((P.lt_rightEndpoint_iff_entry t hi).mpr ht)

/-- [Expanding entry](hyp:hentry) and [shrinking stay](hyp:hstay) from one step to another make
[left endpoints nondecreasing](goal). -/
theorem leftEndpoint_mono_of_predicates (P : PredicateWindowSchedule keys steps) {s t : κ}
    (hentry : ∀ x ∈ keys, P.entry s x → P.entry t x)
    (hstay : ∀ x ∈ keys, P.stay t x → P.stay s x) :
    P.leftEndpoint s ≤ P.leftEndpoint t := by
  by_contra h
  have hlt : P.leftEndpoint t < P.leftEndpoint s := Nat.lt_of_not_ge h
  have hright := P.rightEndpoint_mono_of_entry hentry
  have hirS : P.leftEndpoint t < P.rightEndpoint s :=
    lt_of_lt_of_le hlt (P.leftEndpoint_le_rightEndpoint s)
  have hirT : P.leftEndpoint t < P.rightEndpoint t := lt_of_lt_of_le hirS hright
  have hi : P.leftEndpoint t < keys.length :=
    lt_of_lt_of_le hirT (P.rightEndpoint_le_length t)
  have hnotStayS := (P.lt_leftEndpoint_iff_not_stay s hirS).mp hlt
  have hstayT : P.stay t (keys.get ⟨P.leftEndpoint t, hi⟩) := by
    by_contra hn
    exact (Nat.lt_irrefl _)
      ((P.lt_leftEndpoint_iff_not_stay t hirT).mpr hn)
  exact hnotStayS (hstay _ (List.get_mem keys ⟨P.leftEndpoint t, hi⟩) hstayT)

/-- [A predicate schedule](hyp:P), [an earlier step](hyp:s), [a later step](hyp:t), and [entry
inclusion](hyp:hentry) have [newly entered raw keys exactly equal to the later entered prefix after
dropping the earlier right endpoint](goal). -/
theorem newlyEntering_eq_drop_entered (P : PredicateWindowSchedule keys steps) (s t : κ)
    (hentry : ∀ x ∈ keys, P.entry s x → P.entry t x) :
    (keys.drop (P.rightEndpoint s)).takeWhile (P.entryTest t) =
      (P.entered t).drop (P.rightEndpoint s) := by
  exact takeWhile_drop_eq_drop_takeWhile (P.entryTest t) keys (P.rightEndpoint s)
    (P.rightEndpoint_mono_of_entry hentry)

/-- [A predicate schedule](hyp:P), [an earlier step](hyp:s), [a later step](hyp:t), and [entry
inclusion](hyp:hentry) have [later right endpoint equal to the earlier endpoint plus the exact
`takeWhile` entering-segment length](goal). -/
theorem rightEndpoint_eq_add_newlyEntering (P : PredicateWindowSchedule keys steps) (s t : κ)
    (hentry : ∀ x ∈ keys, P.entry s x → P.entry t x) :
    P.rightEndpoint t = P.rightEndpoint s +
      ((keys.drop (P.rightEndpoint s)).takeWhile (P.entryTest t)).length := by
  rw [P.newlyEntering_eq_drop_entered s t hentry, List.length_drop]
  exact (Nat.add_sub_of_le (P.rightEndpoint_mono_of_entry hentry)).symm

/-- [A predicate schedule](hyp:P), [an earlier step](hyp:s), [a later step](hyp:t), [entry
expansion](hyp:hentry), and [stay shrinkage](hyp:hstay) have [the keys crossing the left endpoint
exactly equal to the `takeWhile` non-staying segment](goal). -/
theorem newlyExpired_eq_takeWhile (P : PredicateWindowSchedule keys steps) (s t : κ)
    (hentry : ∀ x ∈ keys, P.entry s x → P.entry t x)
    (hstay : ∀ x ∈ keys, P.stay t x → P.stay s x) :
    ((keys.take (P.rightEndpoint t)).drop (P.leftEndpoint s)).take
        (P.leftEndpoint t - P.leftEndpoint s) =
      ((keys.take (P.rightEndpoint t)).drop (P.leftEndpoint s)).takeWhile
        (P.expiredTest t) := by
  have hmono := P.leftEndpoint_mono_of_predicates hentry hstay
  let l := keys.take (P.rightEndpoint t)
  change (l.drop (P.leftEndpoint s)).take (P.leftEndpoint t - P.leftEndpoint s) =
    (l.drop (P.leftEndpoint s)).takeWhile (P.expiredTest t)
  calc
    _ = (l.take (P.leftEndpoint s + (P.leftEndpoint t - P.leftEndpoint s))).drop
        (P.leftEndpoint s) := List.take_drop
    _ = (l.take (P.leftEndpoint t)).drop (P.leftEndpoint s) := by
      rw [Nat.add_sub_of_le hmono]
    _ = (P.expiredPrefix t).drop (P.leftEndpoint s) := by
      rw [P.take_leftEndpoint_eq_expiredPrefix t]
    _ = _ := by
      symm
      exact takeWhile_drop_eq_drop_takeWhile (P.expiredTest t) l (P.leftEndpoint s) hmono

/-- [A predicate schedule](hyp:P), [an earlier step](hyp:s), [a later step](hyp:t), [entry
expansion](hyp:hentry), and [stay shrinkage](hyp:hstay) have [later left endpoint equal to the
earlier endpoint plus the exact `takeWhile` expiration-segment length](goal). -/
theorem leftEndpoint_eq_add_newlyExpired (P : PredicateWindowSchedule keys steps) (s t : κ)
    (hentry : ∀ x ∈ keys, P.entry s x → P.entry t x)
    (hstay : ∀ x ∈ keys, P.stay t x → P.stay s x) :
    P.leftEndpoint t = P.leftEndpoint s +
      (((keys.take (P.rightEndpoint t)).drop (P.leftEndpoint s)).takeWhile
        (P.expiredTest t)).length := by
  have hmono := P.leftEndpoint_mono_of_predicates hentry hstay
  have heq := congrArg List.length (P.newlyExpired_eq_takeWhile s t hentry hstay)
  have hbound := P.leftEndpoint_le_rightEndpoint t
  simp only [List.length_take, List.length_drop] at heq
  rw [Nat.min_eq_left (P.rightEndpoint_le_length t)] at heq
  rw [Nat.min_eq_left (Nat.sub_le_sub_right hbound (P.leftEndpoint s))] at heq
  omega

/-- [A predicate schedule](hyp:P) compiles to [the monotone bounded-window schedule over key
positions](goal). -/
noncomputable def schedule (P : PredicateWindowSchedule keys steps) : Schedule keys.length := by
  classical
  refine { windows := steps.map P.windowAt, left_mono := ?_, right_mono := ?_ }
  · rw [List.pairwise_map]
    exact (P.entry_step_mono.and P.stay_step_anti).imp
      (fun h => P.leftEndpoint_mono_of_predicates h.1 h.2)
  · rw [List.pairwise_map]
    exact P.entry_step_mono.imp (fun h => P.rightEndpoint_mono_of_entry h)

/-- [A predicate schedule](hyp:P) compiles to [one position window for each raw step](goal). -/
theorem schedule_steps (P : PredicateWindowSchedule keys steps) :
    P.schedule.steps = steps.length := by
  simp [schedule, Schedule.steps]

/-- [A predicate schedule](hyp:P) and [a valid step-list position](hyp:hk) compile [the window at
that position to the endpoints of the corresponding raw step](goal). -/
theorem schedule_window_get (P : PredicateWindowSchedule keys steps) {k : ℕ}
    (hk : k < steps.length) :
    P.schedule.windows.get ⟨k, by simpa [schedule, Schedule.steps] using hk⟩ =
      P.windowAt (steps.get ⟨k, hk⟩) := by
  simp [schedule, List.get_eq_getElem]

/-- [A predicate schedule](hyp:P), [a valid step position](hyp:hk), and [an in-bounds key
position](hyp:hi) characterize [activity in the compiled scheduled window by the raw
predicates](goal). -/
theorem active_schedule_iff (P : PredicateWindowSchedule keys steps) {k i : ℕ}
    (hk : k < steps.length) (hi : i < keys.length) :
    Active (P.schedule.windows.get ⟨k, by simpa [schedule, Schedule.steps] using hk⟩) i ↔
      P.entry (steps.get ⟨k, hk⟩) (keys.get ⟨i, hi⟩) ∧
        P.stay (steps.get ⟨k, hk⟩) (keys.get ⟨i, hi⟩) := by
  rw [P.schedule_window_get hk]
  exact P.active_windowAt_iff (steps.get ⟨k, hk⟩) hi

/-- [A predicate schedule](hyp:P), [two valid step positions](hyp:hi,hj), and [their strict
order](hyp:hij) ensure [the earlier compiled right endpoint is no larger](goal). -/
theorem rightEndpoint_le_of_step_lt (P : PredicateWindowSchedule keys steps)
    {i j : ℕ} (hi : i < steps.length) (hj : j < steps.length) (hij : i < j) :
    P.rightEndpoint (steps.get ⟨i, hi⟩) ≤ P.rightEndpoint (steps.get ⟨j, hj⟩) := by
  apply P.rightEndpoint_mono_of_entry
  exact P.entry_step_mono.rel_get_of_lt hij

/-- [A predicate schedule](hyp:P), [two valid step positions](hyp:hi,hj), and [their strict
order](hyp:hij) ensure [the earlier compiled left endpoint is no larger](goal). -/
theorem leftEndpoint_le_of_step_lt (P : PredicateWindowSchedule keys steps)
    {i j : ℕ} (hi : i < steps.length) (hj : j < steps.length) (hij : i < j) :
    P.leftEndpoint (steps.get ⟨i, hi⟩) ≤ P.leftEndpoint (steps.get ⟨j, hj⟩) := by
  apply P.leftEndpoint_mono_of_predicates
  · exact P.entry_step_mono.rel_get_of_lt hij
  · exact P.stay_step_anti.rel_get_of_lt hij

/-- [A predicate schedule over an empty raw-key list](hyp:P) has [both endpoints equal to zero at
every step](goal). -/
theorem windowAt_empty (P : PredicateWindowSchedule ([] : List ι) steps) (s : κ) :
    (P.windowAt s).left = 0 ∧ (P.windowAt s).right = 0 := by
  simp [windowAt, leftEndpoint, rightEndpoint, expiredPrefix, entered]

end PredicateWindowSchedule

end Causalean.Mathlib.Algorithms.MonotoneWindowDeque

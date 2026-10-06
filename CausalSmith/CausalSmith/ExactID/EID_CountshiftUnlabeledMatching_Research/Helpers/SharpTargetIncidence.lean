module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.TCompatibilityCompletion
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.TEntrywiseCompletion

/-! Maintained-incidence peeling invariants and initialization bounds. -/

public section

open MeasureTheory

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

/-- Repeated private-row deletion has stabilized after one round per group. -/
-- @node: peelStep_fixed_after_card
lemma peelStep_fixed_after_card {p : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
    (S : G → Finset (Fin p)) (frozen : Option G) :
    peelStep S frozen (peelResidual S frozen) = peelResidual S frozen := by
  classical
  let step := peelStep S frozen
  have hsubset (R : Finset G) : step R ⊆ R := by
    intro g hg
    exact (Finset.mem_filter.mp hg).1
  have hfixed (n : ℕ) : ∀ R : Finset G, R.card ≤ n →
      step (step^[n] R) = step^[n] R := by
    induction n with
    | zero =>
      intro R hcard
      have hR : R = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
      simp [hR, step, peelStep]
    | succ n ih =>
      intro R hcard
      by_cases h : step R = R
      · have hit (k : ℕ) : step^[k] R = R := by
          induction k with
          | zero => rfl
          | succ k hk => simp [Function.iterate_succ_apply, hk, h]
        simp [hit, h]
      · have hstrict : step R ⊂ R :=
          Finset.ssubset_iff_subset_ne.mpr ⟨hsubset R, h⟩
        have hcard' : (step R).card ≤ n := by
          have := Finset.card_lt_card hstrict
          omega
        simpa only [Function.iterate_succ_apply] using ih (step R) hcard'
  simpa only [peelResidual] using
    hfixed (Fintype.card G) Finset.univ (by simp)

-- @node: incidenceBuild_cost_eq
lemma incidenceBuild_cost_eq {p : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
    (S : G → Finset (Fin p)) :
    (incidenceBuild S).2 = Fintype.card G + 3 * ∑ g : G, (S g).card := by
  classical
  let inner (g : G) (st : ((Fin p → Finset G) × (Fin p → ℕ)) × ℕ) :=
    (S g).toList.foldl (fun st i =>
      ((Function.update st.1.1 i (insert g (st.1.1 i)),
        Function.update st.1.2 i (st.1.2 i + 1)), st.2 + 3)) st
  have hinner (g : G) (xs : List (Fin p))
      (st : ((Fin p → Finset G) × (Fin p → ℕ)) × ℕ) :
      (xs.foldl (fun st i =>
        ((Function.update st.1.1 i (insert g (st.1.1 i)),
          Function.update st.1.2 i (st.1.2 i + 1)), st.2 + 3)) st).2 =
          st.2 + 3 * xs.length := by
    induction xs generalizing st with
    | nil => simp
    | cons i xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      simp
      omega
  have hstep (g : G) (st : ((Fin p → Finset G) × (Fin p → ℕ)) × ℕ) :
      (inner g (st.1, st.2 + 1)).2 = st.2 + 1 + 3 * (S g).card := by
    simp only [inner]
    rw [hinner]
    simp
  have houter (xs : List G)
      (st : ((Fin p → Finset G) × (Fin p → ℕ)) × ℕ) :
      (xs.foldl (fun st g => inner g (st.1, st.2 + 1)) st).2 =
        st.2 + (xs.map fun g => 1 + 3 * (S g).card).sum := by
    induction xs generalizing st with
    | nil => simp
    | cons g xs ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih, hstep]
      omega
  simp only [incidenceBuild]
  change ((Finset.univ.toList.foldl (fun st g => inner g (st.1, st.2 + 1))
    ((fun _ => ∅, fun _ => 0), 0))).2 = _
  rw [houter]
  simp only [zero_add, List.sum_map_add, List.sum_map_mul_left]
  simp

-- @node: incidenceQueueBuild_cost_le
lemma incidenceQueueBuild_cost_le {p : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
    (S : G → Finset (Fin p)) (frozen : Option G) (degree : Fin p → ℕ) :
    (incidenceQueueBuild S frozen degree).2 ≤
      2 * Fintype.card G + ∑ g : G, (S g).card := by
  classical
  let step : (Finset G × ℕ) → G → Finset G × ℕ := fun st g =>
    if some g ≠ frozen ∧ ∃ i ∈ S g, degree i = 1 then
      (insert g st.1, st.2 + 2 + (S g).card)
    else (st.1, st.2 + 1 + (S g).card)
  have hstep (st : Finset G × ℕ) (g : G) :
      (step st g).2 ≤ st.2 + 2 + (S g).card := by
    simp only [step]
    split_ifs <;> simp
  have houter (xs : List G) (st : Finset G × ℕ) :
      (xs.foldl step st).2 ≤
        st.2 + (xs.map fun g => 2 + (S g).card).sum := by
    induction xs generalizing st with
    | nil => simp
    | cons g xs ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      have h := ih (step st g)
      have h' := hstep st g
      omega
  unfold incidenceQueueBuild
  exact le_trans (houter Finset.univ.toList (∅, 0)) (by
    simp only [zero_add, List.sum_map_add]
    simp
    omega)

/-- The initial queue contains exactly the eligible groups with a private row. -/
-- @node: incidenceQueueBuild_spec
lemma incidenceQueueBuild_spec {p : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
    (S : G → Finset (Fin p)) (frozen : Option G) (degree : Fin p → ℕ) :
    (incidenceQueueBuild S frozen degree).1 =
      Finset.univ.filter (fun g => some g ≠ frozen ∧
        ∃ i ∈ S g, degree i = 1) := by
  classical
  let P (g : G) := some g ≠ frozen ∧ ∃ i ∈ S g, degree i = 1
  let step (st : Finset G × ℕ) (g : G) : Finset G × ℕ :=
    if P g then (insert g st.1, st.2 + 2 + (S g).card)
    else (st.1, st.2 + 1 + (S g).card)
  have hfold (xs : List G) (st : Finset G × ℕ) :
      (xs.foldl step st).1 = st.1 ∪ xs.toFinset.filter P := by
    induction xs generalizing st with
    | nil => simp
    | cons g xs ih =>
      rw [List.foldl_cons, ih]
      by_cases hg : P g
      · ext x
        simp only [step, hg, ↓reduceIte, List.toFinset_cons,
          Finset.filter_insert, Finset.mem_union, Finset.mem_insert]
        simp [or_assoc, or_left_comm]
      · simp only [step, hg, ↓reduceIte, List.toFinset_cons,
          Finset.filter_insert, if_neg hg]
  unfold incidenceQueueBuild
  change (Finset.univ.toList.foldl step (∅, 0)).1 = _
  rw [hfold]
  simp [P]

-- @node: incidencePeelInit_cost_le
lemma incidencePeelInit_cost_le {p : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
    (S : G → Finset (Fin p)) (frozen : Option G) :
    (incidencePeelInit S frozen).cost ≤
      p + 3 * Fintype.card G + 4 * ∑ g : G, (S g).card := by
  classical
  have hb := incidenceBuild_cost_eq S
  have hq := incidenceQueueBuild_cost_le S frozen (incidenceBuild S).1.2
  unfold incidencePeelInit
  dsimp
  omega

/-- Initialization stores the actual number of groups incident to each coordinate. -/
-- @node: incidencePeelInit_degree_correct
lemma incidencePeelInit_degree_correct {p : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (S : G → Finset (Fin p))
    (frozen : Option G) :
    ∀ i, (incidencePeelInit S frozen).degree i =
      (Finset.univ.filter fun g : G => i ∈ S g).card := by
  classical
  intro i
  let update (g : G) (st : ((Fin p → Finset G) × (Fin p → ℕ)) × ℕ)
      (j : Fin p) :=
    ((Function.update st.1.1 j (insert g (st.1.1 j)),
      Function.update st.1.2 j (st.1.2 j + 1)), st.2 + 3)
  have hinner (g : G) (xs : List (Fin p))
      (st : ((Fin p → Finset G) × (Fin p → ℕ)) × ℕ) :
      (xs.foldl (update g) st).1.2 i =
        st.1.2 i + (xs.filter (· = i)).length := by
    induction xs generalizing st with
    | nil => simp
    | cons j xs ih =>
      simp only [List.foldl_cons, List.filter_cons]
      rw [ih]
      by_cases hji : j = i
      · subst j
        simp [update]
        omega
      · simp [update, hji, Ne.symm hji]
  let step (st : ((Fin p → Finset G) × (Fin p → ℕ)) × ℕ) (g : G) :=
    (S g).toList.foldl (update g) (st.1, st.2 + 1)
  have hstep (st : ((Fin p → Finset G) × (Fin p → ℕ)) × ℕ) (g : G) :
      (step st g).1.2 i = st.1.2 i + if i ∈ S g then 1 else 0 := by
    have hcard : ((S g).toList.filter (· = i)).length =
        if i ∈ S g then 1 else 0 := by
      rw [← List.toFinset_card_of_nodup ((S g).nodup_toList.filter _),
        List.toFinset_filter]
      by_cases hi : i ∈ S g
      · have heq : (S g).filter (· = i) = {i} := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · exact fun hj => hj.2
          · intro hj
            subst j
            exact ⟨hi, rfl⟩
        simp [hi, heq]
      · simp [hi]
    simpa [step, hcard] using hinner g (S g).toList (st.1, st.2 + 1)
  have houter (xs : List G)
      (st : ((Fin p → Finset G) × (Fin p → ℕ)) × ℕ) :
      (xs.foldl step st).1.2 i =
        st.1.2 i + (xs.filter (fun g => i ∈ S g)).length := by
    induction xs generalizing st with
    | nil => simp
    | cons g xs ih =>
      simp only [List.foldl_cons, List.filter_cons]
      rw [ih, hstep]
      by_cases hi : i ∈ S g
      · simp [hi]
        omega
      · simp [hi]
  change (Finset.univ.toList.foldl step ((fun _ => ∅, fun _ => 0), 0)).1.2 i = _
  rw [houter]
  have hcard : (Finset.univ.toList.filter (fun g : G => i ∈ S g)).length =
      (Finset.univ.filter fun g : G => i ∈ S g).card := by
    rw [← List.toFinset_card_of_nodup (Finset.univ.nodup_toList.filter _),
      List.toFinset_filter]
    simp
  simp [hcard]

/-- Incidence construction records exactly the original neighbors of each coordinate. -/
-- @node: incidencePeelInit_neighbors_correct
lemma incidencePeelInit_neighbors_correct {p : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (S : G → Finset (Fin p))
    (frozen : Option G) :
    ∀ i, (incidencePeelInit S frozen).neighbors i =
      Finset.univ.filter (fun g : G => i ∈ S g) := by
  classical
  intro i
  let update (g : G) (st : ((Fin p → Finset G) × (Fin p → ℕ)) × ℕ)
      (j : Fin p) :=
    ((Function.update st.1.1 j (insert g (st.1.1 j)),
      Function.update st.1.2 j (st.1.2 j + 1)), st.2 + 3)
  have hinner (g : G) (xs : List (Fin p))
      (st : ((Fin p → Finset G) × (Fin p → ℕ)) × ℕ) :
      (xs.foldl (update g) st).1.1 i =
        st.1.1 i ∪ (if i ∈ xs then {g} else ∅) := by
    induction xs generalizing st with
    | nil => simp
    | cons j xs ih =>
      rw [List.foldl_cons, ih]
      by_cases hji : j = i
      · subst j
        ext h
        by_cases hi : i ∈ xs <;>
          simp [update, hi, Finset.mem_insert]
      · simp [update, Ne.symm hji]
  let step (st : ((Fin p → Finset G) × (Fin p → ℕ)) × ℕ) (g : G) :=
    (S g).toList.foldl (update g) (st.1, st.2 + 1)
  have hstep (st : ((Fin p → Finset G) × (Fin p → ℕ)) × ℕ) (g : G) :
      (step st g).1.1 i = st.1.1 i ∪
        (if i ∈ S g then {g} else ∅) := by
    simpa [step] using hinner g (S g).toList (st.1, st.2 + 1)
  have houter (xs : List G)
      (st : ((Fin p → Finset G) × (Fin p → ℕ)) × ℕ) :
      (xs.foldl step st).1.1 i =
        st.1.1 i ∪ xs.toFinset.filter (fun g => i ∈ S g) := by
    induction xs generalizing st with
    | nil => simp
    | cons g xs ih =>
      rw [List.foldl_cons, ih, hstep]
      ext h
      simp only [Finset.mem_union, List.toFinset_cons, Finset.filter_insert,
        Finset.mem_filter]
      by_cases hig : i ∈ S g <;> simp [hig, or_assoc, or_left_comm]
  change (Finset.univ.toList.foldl step
    ((fun _ => ∅, fun _ => 0), 0)).1.1 i = _
  rw [houter]
  simp

/-- A queue step only removes a group from the remaining family. -/
-- @node: incidencePeelStep_neighbors_eq
lemma incidencePeelStep_neighbors_eq {p : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (S : G → Finset (Fin p))
    (frozen : Option G) (st : IncidencePeelState p G) :
    (incidencePeelStep S frozen st).neighbors = st.neighbors := by
  classical
  unfold incidencePeelStep
  split_ifs <;> rfl

-- @node: incidencePeelRun_neighbors_correct
lemma incidencePeelRun_neighbors_correct {p : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (S : G → Finset (Fin p))
    (frozen : Option G) (n : ℕ) :
    ∀ i, (((incidencePeelStep S frozen)^[n]
      (incidencePeelInit S frozen)).neighbors i) =
        Finset.univ.filter (fun g : G => i ∈ S g) := by
  intro i
  induction n with
  | zero => exact incidencePeelInit_neighbors_correct S frozen i
  | succ n ih =>
      rw [Function.iterate_succ_apply', incidencePeelStep_neighbors_eq]
      exact ih

/-- A queue step only removes a group from the remaining family. -/
-- @node: incidencePeelStep_remaining_subset
lemma incidencePeelStep_remaining_subset {p : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (S : G → Finset (Fin p))
    (frozen : Option G) (st : IncidencePeelState p G) :
    (incidencePeelStep S frozen st).remaining ⊆ st.remaining := by
  classical
  unfold incidencePeelStep
  split_ifs
  · exact Finset.erase_subset _ _
  · exact Finset.Subset.rfl

/-- Every intermediate queue run retains only groups from its initial family. -/
-- @node: incidencePeelRun_remaining_subset
lemma incidencePeelRun_remaining_subset {p : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (S : G → Finset (Fin p))
    (frozen : Option G) (n : ℕ) (st : IncidencePeelState p G) :
    ((incidencePeelStep S frozen)^[n] st).remaining ⊆ st.remaining := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (incidencePeelStep_remaining_subset S frozen _).trans ih

/-- The maintained degrees remain the incidence counts after a valid queue deletion. -/
-- @node: incidencePeelStep_degree_correct
lemma incidencePeelStep_degree_correct {p : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (S : G → Finset (Fin p))
    (frozen : Option G) (st : IncidencePeelState p G)
    (hdegree : ∀ i, st.degree i =
      (st.remaining.filter fun h => i ∈ S h).card)
    (hqueue : st.queue ⊆ st.remaining) :
    ∀ i, (incidencePeelStep S frozen st).degree i =
      ((incidencePeelStep S frozen st).remaining.filter
        fun h => i ∈ S h).card := by
  classical
  intro i
  unfold incidencePeelStep
  split_ifs with hq
  · let g := Classical.choose hq
    have hgq : g ∈ st.queue := Classical.choose_spec hq
    have hgR : g ∈ st.remaining := hqueue hgq
    change (if i ∈ S g then st.degree i - 1 else st.degree i) =
      ((st.remaining.erase g).filter fun h => i ∈ S h).card
    have hfilter : (st.remaining.erase g).filter (fun h => i ∈ S h) =
        (st.remaining.filter fun h => i ∈ S h).erase g := by
      ext h
      simp only [Finset.mem_filter, Finset.mem_erase]
      tauto
    rw [hfilter, hdegree i]
    by_cases hi : i ∈ S g
    · simp only [hi, ↓reduceIte]
      have hg : g ∈ st.remaining.filter (fun h => i ∈ S h) :=
        Finset.mem_filter.mpr ⟨hgR, hi⟩
      simp [Finset.card_erase_of_mem hg]
    · simp [hi]
  · exact hdegree i

/-- Queue entries continue to be among the groups that have not been deleted. -/
-- @node: incidencePeelStep_queue_subset
lemma incidencePeelStep_queue_subset {p : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (S : G → Finset (Fin p))
    (frozen : Option G) (st : IncidencePeelState p G)
    (hqueue : st.queue ⊆ st.remaining) :
    (incidencePeelStep S frozen st).queue ⊆
      (incidencePeelStep S frozen st).remaining := by
  classical
  unfold incidencePeelStep
  split_ifs with hq
  · intro h hh
    simp only [Finset.mem_union] at hh
    rcases hh with hold | hnew
    · exact Finset.mem_erase.mpr
        ⟨(Finset.mem_erase.mp hold).1, hqueue (Finset.mem_erase.mp hold).2⟩
    · simp only [Finset.mem_biUnion] at hnew
      obtain ⟨i, _, hi⟩ := hnew
      split_ifs at hi
      · exact (Finset.mem_filter.mp hi).2.1
      · simp at hi
  · exact hqueue

/-- Degree counts and queue membership are maintained throughout the run. -/
-- @node: incidencePeelRun_degree_correct
lemma incidencePeelRun_degree_correct {p : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (S : G → Finset (Fin p))
    (frozen : Option G) (n : ℕ) (st : IncidencePeelState p G)
    (hdegree : ∀ i, st.degree i =
      (st.remaining.filter fun h => i ∈ S h).card)
    (hqueue : st.queue ⊆ st.remaining) :
    (∀ i, ((incidencePeelStep S frozen)^[n] st).degree i =
      (((incidencePeelStep S frozen)^[n] st).remaining.filter
        fun h => i ∈ S h).card) ∧
    ((incidencePeelStep S frozen)^[n] st).queue ⊆
      ((incidencePeelStep S frozen)^[n] st).remaining := by
  induction n with
  | zero => simpa using And.intro hdegree hqueue
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨incidencePeelStep_degree_correct S frozen _ ih.1 ih.2,
      incidencePeelStep_queue_subset S frozen _ ih.2⟩

/-- A degree-one coordinate in a surviving group is precisely a private
coordinate among the surviving groups. -/
-- @node: incidenceDegree_one_iff_private
lemma incidenceDegree_one_iff_private {p : ℕ} {G : Type*}
    (S : G → Finset (Fin p))
    (st : IncidencePeelState p G) (g : G) (hg : g ∈ st.remaining)
    (hdegree : ∀ i, st.degree i =
      (st.remaining.filter fun h => i ∈ S h).card)
    (i : Fin p) (hi : i ∈ S g) :
    st.degree i = 1 ↔
      ∀ h ∈ st.remaining, h ≠ g → i ∉ S h := by
  classical
  let R := st.remaining.filter fun h => i ∈ S h
  have hgR : g ∈ R := Finset.mem_filter.mpr ⟨hg, hi⟩
  rw [hdegree i]
  change R.card = 1 ↔ _
  constructor
  · intro hcard h hh hne hmem
    have hhR : h ∈ R := Finset.mem_filter.mpr ⟨hh, hmem⟩
    have hsingle : R = {g} := by
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
      change R = {a} at ha
      have hga : g = a := by simpa [ha] using hgR
      simpa [hga] using ha
    have : h = g := by simpa [hsingle] using hhR
    exact hne this
  · intro hprivate
    have hsingle : R = {g} := by
      apply Finset.Subset.antisymm
      · intro h hhR
        obtain ⟨hh, hmem⟩ := Finset.mem_filter.mp hhR
        by_cases heq : h = g
        · simp [heq]
        · exact False.elim ((hprivate h hh heq) hmem)
      · simpa using hgR
    simp [hsingle]

/-- The initial queue implements the ordinary private-row deletion predicate. -/
-- @node: incidencePeelInit_queue_iff_deletable
lemma incidencePeelInit_queue_iff_deletable {p : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (S : G → Finset (Fin p))
    (frozen : Option G) (g : G) :
    g ∈ (incidencePeelInit S frozen).queue ↔
      FrozenDeletable S frozen (incidencePeelInit S frozen).remaining g := by
  classical
  have hdegree := incidencePeelInit_degree_correct S frozen
  have hremaining : (incidencePeelInit S frozen).remaining = Finset.univ := rfl
  have hqueue : (incidencePeelInit S frozen).queue =
      Finset.univ.filter (fun g => some g ≠ frozen ∧
        ∃ i ∈ S g, (incidencePeelInit S frozen).degree i = 1) := by
    change (incidenceQueueBuild S frozen (incidenceBuild S).1.2).1 =
      Finset.univ.filter (fun g => some g ≠ frozen ∧
        ∃ i ∈ S g, (incidenceBuild S).1.2 i = 1)
    exact incidenceQueueBuild_spec S frozen (incidenceBuild S).1.2
  rw [hqueue]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change (some g ≠ frozen ∧
      ∃ i ∈ S g, (incidencePeelInit S frozen).degree i = 1) ↔
    (g ∈ (incidencePeelInit S frozen).remaining ∧ some g ≠ frozen ∧
      ∃ i ∈ S g, ∀ h ∈ (incidencePeelInit S frozen).remaining,
        h ≠ g → i ∉ S h)
  constructor
  · rintro ⟨hgf, i, hi, hdi⟩
    refine ⟨by simp [hremaining], hgf, i, hi, ?_⟩
    exact (incidenceDegree_one_iff_private S (incidencePeelInit S frozen)
      g (by simp [hremaining]) hdegree i hi).mp hdi
  · rintro ⟨_, hgf, i, hi, hprivate⟩
    refine ⟨hgf, i, hi, ?_⟩
    exact (incidenceDegree_one_iff_private S (incidencePeelInit S frozen)
      g (by simp [hremaining]) hdegree i hi).mpr hprivate

/-- A queue entry remains a legal deletion after one maintained-incidence step. -/
-- @node: incidencePeelStep_queue_sound
lemma incidencePeelStep_queue_sound {p : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (S : G → Finset (Fin p))
    (frozen : Option G) (st : IncidencePeelState p G)
    (hdegree : ∀ i, st.degree i =
      (st.remaining.filter fun h => i ∈ S h).card)
    (hneighbors : ∀ i, st.neighbors i =
      Finset.univ.filter fun h : G => i ∈ S h)
    (hqueue : ∀ h, h ∈ st.queue → FrozenDeletable S frozen st.remaining h) :
    ∀ h, h ∈ (incidencePeelStep S frozen st).queue →
      FrozenDeletable S frozen (incidencePeelStep S frozen st).remaining h := by
  classical
  intro h hh
  by_cases hq : st.queue.Nonempty
  · let g := Classical.choose hq
    have hgq : g ∈ st.queue := Classical.choose_spec hq
    have hgdel := hqueue g hgq
    have hgR : g ∈ st.remaining := hgdel.1
    have hqsub : st.queue ⊆ st.remaining :=
      fun k hk => (hqueue k hk).1
    have hdegree' := incidencePeelStep_degree_correct S frozen st hdegree hqsub
    have hrem : (incidencePeelStep S frozen st).remaining = st.remaining.erase g := by
      unfold incidencePeelStep
      simp [hq, g]
    have hqueue' : (incidencePeelStep S frozen st).queue =
        st.queue.erase g ∪ (S g).biUnion (fun i =>
          if st.degree i = 2 then
            (st.neighbors i).filter (fun k => k ∈ st.remaining.erase g ∧
              some k ≠ frozen)
          else ∅) := by
      unfold incidencePeelStep
      simp [hq, g]
    rw [hqueue', Finset.mem_union] at hh
    rw [hrem]
    rcases hh with hold | hnew
    · have hhg : h ≠ g := (Finset.mem_erase.mp hold).1
      obtain ⟨hR, hf, i, hi, hprivate⟩ := hqueue h
        (Finset.mem_erase.mp hold).2
      refine ⟨Finset.mem_erase.mpr ⟨hhg, hR⟩, hf, i, hi, ?_⟩
      intro k hk hkh
      exact hprivate k (Finset.mem_erase.mp hk).2 hkh
    · obtain ⟨i, hig, hi⟩ := Finset.mem_biUnion.mp hnew
      split_ifs at hi with hd
      · obtain ⟨hin, hR, hf⟩ := Finset.mem_filter.mp hi
        have hSi : i ∈ S h := by
          have : h ∈ Finset.univ.filter (fun k : G => i ∈ S k) :=
            hneighbors i ▸ hin
          exact (Finset.mem_filter.mp this).2
        have hdegreei : (incidencePeelStep S frozen st).degree i = 1 := by
          unfold incidencePeelStep
          simp only [dif_pos hq]
          simp [hd]
          exact hig
        refine ⟨hR, hf, i, hSi, ?_⟩
        simpa only [← hrem] using (incidenceDegree_one_iff_private S
          (incidencePeelStep S frozen st) h
          (by simpa [hrem] using hR) hdegree' i hSi).mp hdegreei
      · simp at hi
  · have hsame : (incidencePeelStep S frozen st).remaining = st.remaining := by
      unfold incidencePeelStep
      simp [hq]
    have hqueue' : (incidencePeelStep S frozen st).queue = st.queue := by
      unfold incidencePeelStep
      simp [hq]
    rw [hqueue'] at hh
    simpa only [hsame] using hqueue h hh

/-- Every queued group in an incidence run has a private row and may be deleted. -/
-- @node: incidencePeelRun_queue_sound
lemma incidencePeelRun_queue_sound {p : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (S : G → Finset (Fin p))
    (frozen : Option G) (n : ℕ) :
    ∀ h, h ∈ ((incidencePeelStep S frozen)^[n]
      (incidencePeelInit S frozen)).queue →
      FrozenDeletable S frozen
        ((incidencePeelStep S frozen)^[n]
          (incidencePeelInit S frozen)).remaining h := by
  induction n with
  | zero =>
      intro h hh
      exact (incidencePeelInit_queue_iff_deletable S frozen h).mp hh
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hstate := incidencePeelRun_degree_correct S frozen n
        (incidencePeelInit S frozen)
        (incidencePeelInit_degree_correct S frozen)
        (by intro h hh
            exact ((incidencePeelInit_queue_iff_deletable S frozen h).mp hh).1)
      exact incidencePeelStep_queue_sound S frozen _ hstate.1
        (incidencePeelRun_neighbors_correct S frozen n) ih

/-- A frozen group is never selected from the maintained-incidence queue. -/
-- @node: incidencePeelRun_frozen_mem
lemma incidencePeelRun_frozen_mem {p : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (S : G → Finset (Fin p))
    (g : G) (n : ℕ) :
    g ∈ ((incidencePeelStep S (some g))^[n]
      (incidencePeelInit S (some g))).remaining := by
  classical
  induction n with
  | zero => simp [incidencePeelInit]
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      let st := (incidencePeelStep S (some g))^[n]
        (incidencePeelInit S (some g))
      by_cases hq : st.queue.Nonempty
      · have hk := incidencePeelRun_queue_sound S (some g) n
          (Classical.choose hq) (Classical.choose_spec hq)
        have hne : Classical.choose hq ≠ g := by
          intro heq
          exact hk.2.1 (by rw [heq])
        change g ∈ (incidencePeelStep S (some g) st).remaining
        simp only [incidencePeelStep, dif_pos hq]
        exact Finset.mem_erase.mpr ⟨hne.symm, ih⟩
      · change g ∈ (incidencePeelStep S (some g) st).remaining
        simp only [incidencePeelStep, dif_neg hq]
        exact ih


end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

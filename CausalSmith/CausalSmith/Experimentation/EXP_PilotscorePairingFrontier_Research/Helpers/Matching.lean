module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Basic
public import Mathlib.Data.List.Indexes
public import Mathlib.Data.Nat.Digits.Lemmas

/-! # Adjacent-score matching inequalities -/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

variable {d m N : ℕ} {β L cX CX cg Cg h c0 c1 C1 C2 : ℝ}

open scoped BigOperators

/-- The base-`N + 1` code records every partner of a matching injectively. -/
lemma matchingCode_injective (hN2 : 2 ≤ N) :
    Function.Injective (matchingCode : Match N → ℕ) := by
  intro M M' hcode
  have hdigits :
      Nat.ofDigits (N + 1) (List.ofFn fun i : Fin N => (M.val i).val) =
        Nat.ofDigits (N + 1) (List.ofFn fun i : Fin N => (M'.val i).val) := by
    simpa only [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn, List.get_ofFn,
      List.length_ofFn, Fin.val_cast, mul_comm, List.sum_ofFn, matchingCode] using! hcode
  have hlists :
      (List.ofFn fun i : Fin N => (M.val i).val) =
        List.ofFn fun i : Fin N => (M'.val i).val := by
    apply Nat.ofDigits_inj_of_len_eq (b := N + 1) (by omega)
    · simp
    · intro k hk
      rw [List.mem_ofFn] at hk
      obtain ⟨i, rfl⟩ := hk
      omega
    · intro k hk
      rw [List.mem_ofFn] at hk
      obtain ⟨i, rfl⟩ := hk
      omega
    · exact hdigits
  apply Subtype.ext
  apply Equiv.ext
  intro i
  apply Fin.ext
  exact congrFun (List.ofFn_inj.mp hlists) i

/-- The squared-distance cost of a fixed matching is measurable in the covariate tuple. -/
lemma geometricCost_measurable (M : Match N) :
    Measurable (fun x : MainCovariates N d => geometricCost x M) := by
  unfold geometricCost euclideanDistance
  fun_prop

/-- The least-cost matching with the numeric tie-break from `geometricMatching` is measurable. -/
lemma geometricMatching_measurable (hN : Even N) (hN2 : 2 ≤ N) :
    Measurable (fun x : MainCovariates N d => geometricMatching x hN hN2) := by
  apply measurable_to_countable'
  intro M
  have hfiber :
      (fun x : MainCovariates N d => geometricMatching x hN hN2) ⁻¹' {M} =
        {x | ∀ M' : Match N,
          geometricCost x M ≤ geometricCost x M' ∧
          (geometricCost x M = geometricCost x M' →
            matchingCode M ≤ matchingCode M')} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · intro h
      subst M
      exact Classical.choose_spec (exists_geometricMatching x hN hN2)
    · intro hM
      have hG := Classical.choose_spec (exists_geometricMatching x hN hN2)
      have hcost : geometricCost x (geometricMatching x hN hN2) =
          geometricCost x M := le_antisymm (hG M).1 (hM _).1
      apply matchingCode_injective hN2
      exact le_antisymm ((hG M).2 hcost) ((hM _).2 hcost.symm)
  rw [hfiber]
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro M'
  simp only [Set.ofPred_and]
  apply MeasurableSet.inter
  · exact measurableSet_le (geometricCost_measurable M) (geometricCost_measurable M')
  · by_cases hcode : matchingCode M ≤ matchingCode M'
    · simp [hcode]
    · have heq : MeasurableSet
          {x : MainCovariates N d | geometricCost x M = geometricCost x M'} :=
        measurableSet_eq_fun (geometricCost_measurable M) (geometricCost_measurable M')
      convert heq.compl using 1 <;> ext x <;> simp [hcode]

/-- A sorted-adjacent specification determines a unique matching when the size is even. -/
lemma adjSortSpec_unique (hN : Even N) {s : Fin N → ℝ} {M₁ M₂ : Match N}
    (h₁ : AdjSortSpec s M₁) (h₂ : AdjSortSpec s M₂) : M₁ = M₂ := by
  obtain ⟨π₁, hord₁, hpair₁⟩ := h₁
  obtain ⟨π₂, hord₂, hpair₂⟩ := h₂
  have hs₁ : π₁ = Tuple.sort s := by
    apply (Tuple.eq_sort_iff (f := s) (σ := π₁)).2
    constructor
    · intro i j hij
      rcases eq_or_lt_of_le hij with rfl | hij
      · exact le_rfl
      · rcases hord₁ i j hij with hlt | heq
        · exact hlt.le
        · exact heq.1.le
    · intro i j hij heq
      rcases hord₁ i j hij with hlt | htie
      · exact (hlt.ne heq).elim
      · exact htie.2
  have hs₂ : π₂ = Tuple.sort s := by
    apply (Tuple.eq_sort_iff (f := s) (σ := π₂)).2
    constructor
    · intro i j hij
      rcases eq_or_lt_of_le hij with rfl | hij
      · exact le_rfl
      · rcases hord₂ i j hij with hlt | heq
        · exact hlt.le
        · exact heq.1.le
    · intro i j hij heq
      rcases hord₂ i j hij with hlt | htie
      · exact (hlt.ne heq).elim
      · exact htie.2
  subst π₂
  subst π₁
  apply Subtype.ext
  apply Equiv.ext
  intro u
  let i := (Tuple.sort s).symm u
  have hu : Tuple.sort s i = u := by simp [i]
  by_cases hi : Even i.val
  · have hinext : i.val + 1 < N := by
      obtain ⟨k, hk⟩ := hN
      obtain ⟨r, hr⟩ := hi
      omega
    let j : Fin N := ⟨i.val + 1, hinext⟩
    have hp₁ := hpair₁ i j (by simp [j]) hi
    have hp₂ := hpair₂ i j (by simp [j]) hi
    rw [← hu, hp₁, hp₂]
  · have hipos : 0 < i.val := by
      by_contra h
      have : i.val = 0 := by omega
      exact hi (this ▸ ⟨0, by omega⟩)
    let j : Fin N := ⟨i.val - 1, by omega⟩
    have hj : Even j.val := by
      rw [Nat.even_iff]
      rw [Nat.even_iff] at hi
      simp only [j]
      omega
    have hp₁ := hpair₁ j i (by simp [j]; omega) hj
    have hp₂ := hpair₂ j i (by simp [j]; omega) hj
    have hh₁ := M₁.property.1 (Tuple.sort s j)
    have hh₂ := M₂.property.1 (Tuple.sort s j)
    rw [hp₁] at hh₁
    rw [hp₂] at hh₂
    rw [← hu, hh₁, hh₂]

/-- Adjacent matching is measurable for any coordinatewise measurable score family. -/
lemma adjSortMatching_measurable (hN : Even N) (hN2 : 2 ≤ N)
    {Ω : Type*} [MeasurableSpace Ω] (s : Ω → Fin N → ℝ)
    (hs : ∀ i, Measurable (fun ω => s ω i)) :
    Measurable (fun ω => adjSortMatching (s ω) hN hN2) := by
  apply measurable_to_countable'
  intro M
  have hfiber :
      (fun ω => adjSortMatching (s ω) hN hN2) ⁻¹' {M} =
        {ω | AdjSortSpec (s ω) M} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · intro h
      subst M
      exact Classical.choose_spec (exists_adjSortMatching (s ω) hN hN2)
    · intro hM
      exact adjSortSpec_unique hN
        (Classical.choose_spec (exists_adjSortMatching (s ω) hN hN2)) hM
  rw [hfiber]
  change MeasurableSet {ω | ∃ π : Equiv.Perm (Fin N),
    (∀ i j : Fin N, i < j →
      s ω (π i) < s ω (π j) ∨
        (s ω (π i) = s ω (π j) ∧ (π i).val < (π j).val)) ∧
    (∀ i j : Fin N, i.val + 1 = j.val → Even i.val → M.val (π i) = π j)}
  rw [show {ω | ∃ π : Equiv.Perm (Fin N),
      (∀ i j : Fin N, i < j →
        s ω (π i) < s ω (π j) ∨
          (s ω (π i) = s ω (π j) ∧ (π i).val < (π j).val)) ∧
      (∀ i j : Fin N, i.val + 1 = j.val → Even i.val → M.val (π i) = π j)} =
      ⋃ π : Equiv.Perm (Fin N), if
        (∀ i j : Fin N, i.val + 1 = j.val → Even i.val → M.val (π i) = π j) then
        {ω | ∀ i j : Fin N, i < j →
          s ω (π i) < s ω (π j) ∨
            (s ω (π i) = s ω (π j) ∧ (π i).val < (π j).val)}
      else ∅ by
        ext ω
        constructor
        · rintro ⟨π, hord, hpair⟩
          simp only [Set.mem_iUnion]
          exact ⟨π, by rw [if_pos hpair]; exact hord⟩
        · simp only [Set.mem_iUnion]
          rintro ⟨π, hπ⟩
          by_cases hpair :
              ∀ i j : Fin N, i.val + 1 = j.val → Even i.val → M.val (π i) = π j
          · refine ⟨π, ?_, hpair⟩
            simpa only [if_pos hpair, Set.mem_ofPred_eq] using hπ
          · have : ω ∈ (∅ : Set Ω) := by simpa only [if_neg hpair] using hπ
            exact this.elim]
  apply MeasurableSet.iUnion
  intro π
  by_cases hpair :
      ∀ i j : Fin N, i.val + 1 = j.val → Even i.val → M.val (π i) = π j
  · rw [if_pos hpair]
    rw [show {ω | ∀ i j : Fin N, i < j →
        s ω (π i) < s ω (π j) ∨
          (s ω (π i) = s ω (π j) ∧ (π i).val < (π j).val)} =
        ⋂ i : Fin N, ⋂ j : Fin N, if i < j then
          {ω | s ω (π i) < s ω (π j) ∨
            (s ω (π i) = s ω (π j) ∧ (π i).val < (π j).val)}
        else Set.univ by ext ω; simp]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    by_cases hij : i < j
    · rw [if_pos hij]
      apply MeasurableSet.union
      · exact measurableSet_lt (hs (π i)) (hs (π j))
      · by_cases hlabel : (π i).val < (π j).val
        · have heq : MeasurableSet
              {ω | s ω (π i) = s ω (π j)} :=
            measurableSet_eq_fun (hs (π i)) (hs (π j))
          simp only [hlabel, and_true]
          change MeasurableSet {ω | s ω (π i) = s ω (π j)}
          exact heq
        · simp only [hlabel, and_false]
          change MeasurableSet (∅ : Set Ω)
          exact MeasurableSet.empty
    · rw [if_neg hij]
      exact MeasurableSet.univ
  · rw [if_neg hpair]
    exact MeasurableSet.empty

-- @node: adjacent_matching_exchange
lemma adjacent_matching_exchange {a b c d : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    (b - a) ^ 2 + (d - c) ^ 2 ≤ (c - a) ^ 2 + (d - b) ^ 2 ∧
    (b - a) ^ 2 + (d - c) ^ 2 ≤ (d - a) ^ 2 + (c - b) ^ 2 := by
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hbc) (sub_nonneg.mpr (le_trans hab (le_trans hbc hcd)))]
  · nlinarith [mul_nonneg (sub_nonneg.mpr (le_trans hbc hcd))
      (sub_nonneg.mpr (le_trans hab hbc))]

@[no_expose]
private def pairedEntries : List (ℝ × ℝ) → List ℝ
  | [] => []
  | (a, b) :: ps => a :: b :: pairedEntries ps

@[no_expose]
private def pairedSqLoss : List (ℝ × ℝ) → ℝ
  | [] => 0
  | (a, b) :: ps => (b - a) ^ 2 + pairedSqLoss ps

/-- The sum of squared gaps between consecutive pairs in a list. -/
@[no_expose]
def adjacentSqLoss : List ℝ → ℝ
  | a :: b :: xs => (b - a) ^ 2 + adjacentSqLoss xs
  | _ => 0

private lemma pairedEntries_extract {x : ℝ} {ps : List (ℝ × ℝ)}
    (hx : x ∈ pairedEntries ps) :
    ∃ u qs, (pairedEntries ps).Perm (x :: u :: pairedEntries qs) ∧
      pairedSqLoss ps = (u - x) ^ 2 + pairedSqLoss qs := by
  induction ps with
  | nil => simp [pairedEntries] at hx
  | cons p ps ih =>
      rcases p with ⟨a, b⟩
      simp only [pairedEntries, List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact ⟨b, ps, .refl _, rfl⟩
      · exact ⟨a, ps, List.Perm.swap _ _ _, by simp only [pairedSqLoss]; ring⟩
      · rcases ih hx with ⟨u, qs, hp, heq⟩
        refine ⟨u, (a, b) :: qs, ?_, ?_⟩
        · have h₁ := hp.cons b |>.cons a
          have h₂ := List.Perm.append_right (pairedEntries qs)
            (List.perm_append_comm (l₁ := [a, b]) (l₂ := [x, u]))
          exact h₁.trans (by simpa [pairedEntries] using h₂)
        · simp only [pairedSqLoss]
          rw [heq]
          ring

private lemma even_tail_of_even_cons_cons {a b : α} {xs : List α}
    (h : Even (a :: b :: xs).length) : Even xs.length := by
  rcases h with ⟨k, hk⟩
  simp only [List.length_cons] at hk
  have hkpos : 1 ≤ k := by omega
  exact ⟨k - 1, by omega⟩

private lemma adjacentSqLoss_le_pairedSqLoss
    {xs : List ℝ} {ps : List (ℝ × ℝ)}
    (heven : Even xs.length) (hsorted : xs.Pairwise (· ≤ ·))
    (hperm : (pairedEntries ps).Perm xs) :
    adjacentSqLoss xs ≤ pairedSqLoss ps := by
  cases xs with
  | nil =>
      have hempty : pairedEntries ps = [] := hperm.eq_nil
      cases ps with
      | nil => rfl
      | cons p ps => rcases p with ⟨a, b⟩; simp [pairedEntries] at hempty
  | cons a xs =>
      cases xs with
      | nil =>
          rcases heven with ⟨k, hk⟩
          simp only [List.length_cons, List.length_nil] at hk
          omega
      | cons b tail =>
          have heven' : Even tail.length := even_tail_of_even_cons_cons heven
          rcases List.pairwise_cons.mp hsorted with ⟨ha, hsorted_b⟩
          rcases List.pairwise_cons.mp hsorted_b with ⟨hb, hsorted_tail⟩
          have hab : a ≤ b := ha b (by simp)
          have ha_mem : a ∈ pairedEntries ps := (hperm.mem_iff).2 (by simp)
          rcases pairedEntries_extract ha_mem with ⟨u, qs, hp, hloss⟩
          have hrest : (u :: pairedEntries qs).Perm (b :: tail) :=
            List.Perm.cons_inv (hp.symm.trans hperm)
          by_cases hu : u = b
          · subst u
            have htailperm : (pairedEntries qs).Perm tail := List.Perm.cons_inv hrest
            have hind := adjacentSqLoss_le_pairedSqLoss heven' hsorted_tail htailperm
            rw [hloss]
            change (b - a) ^ 2 + adjacentSqLoss tail ≤ _
            linarith
          · have hb_mem : b ∈ pairedEntries qs := by
              have hm : b ∈ u :: pairedEntries qs := (hrest.mem_iff).2 (by simp)
              simpa [show b ≠ u from Ne.symm hu] using hm
            rcases pairedEntries_extract hb_mem with ⟨v, rs, hp₂, hloss₂⟩
            have hsource : (u :: b :: v :: pairedEntries rs).Perm (b :: tail) :=
              (hp₂.cons u).symm.trans hrest
            have hrem : (u :: v :: pairedEntries rs).Perm tail := by
              apply List.Perm.cons_inv
              exact (List.Perm.swap b u (v :: pairedEntries rs)).symm.trans hsource
            have hu_tail : u ∈ tail := (hrem.mem_iff).1 (by simp)
            have hv_tail : v ∈ tail := (hrem.mem_iff).1 (by simp)
            have hbu : b ≤ u := hb u hu_tail
            have hbv : b ≤ v := hb v hv_tail
            have hexchange : (b - a) ^ 2 + (v - u) ^ 2 ≤
                (u - a) ^ 2 + (v - b) ^ 2 := by
              by_cases huv : u ≤ v
              · exact (adjacent_matching_exchange hab hbu huv).1
              · have hvu : v ≤ u := le_of_not_ge huv
                have hs : (v - u) ^ 2 = (u - v) ^ 2 := by ring
                rw [hs]
                exact (adjacent_matching_exchange hab hbv hvu).2
            have hind := adjacentSqLoss_le_pairedSqLoss (ps := (u, v) :: rs)
              heven' hsorted_tail (by simpa [pairedEntries] using hrem)
            calc
              adjacentSqLoss (a :: b :: tail) =
                  (b - a) ^ 2 + adjacentSqLoss tail := rfl
              _ ≤ (b - a) ^ 2 + pairedSqLoss ((u, v) :: rs) := by linarith
              _ ≤ ((u - a) ^ 2 + (v - b) ^ 2) + pairedSqLoss rs := by
                simp only [pairedSqLoss]
                linarith
              _ = pairedSqLoss ps := by rw [hloss, hloss₂]; ring
termination_by xs.length

@[no_expose]
private def listPairs : List ℝ → List (ℝ × ℝ)
  | a :: b :: xs => (a, b) :: listPairs xs
  | _ => []

private lemma pairedEntries_listPairs_of_even {xs : List ℝ}
    (heven : Even xs.length) : pairedEntries (listPairs xs) = xs := by
  cases xs with
  | nil => rfl
  | cons a xs =>
      cases xs with
      | nil =>
          rcases heven with ⟨k, hk⟩
          simp only [List.length_cons, List.length_nil] at hk
          omega
      | cons b tail =>
          rw [show listPairs (a :: b :: tail) = (a, b) :: listPairs tail from rfl]
          rw [show pairedEntries ((a, b) :: listPairs tail) =
            a :: b :: pairedEntries (listPairs tail) from rfl]
          rw [pairedEntries_listPairs_of_even (even_tail_of_even_cons_cons heven)]
termination_by xs.length

private lemma pairedSqLoss_listPairs (xs : List ℝ) :
    pairedSqLoss (listPairs xs) = adjacentSqLoss xs := by
  induction xs using listPairs.induct <;>
    simp_all [listPairs, pairedSqLoss, adjacentSqLoss]

private lemma pairedSqLoss_ofFn {n : ℕ} (p : Fin n → ℝ × ℝ) :
    pairedSqLoss (List.ofFn p) = ∑ i, ((p i).2 - (p i).1) ^ 2 := by
  induction n with
  | zero => simp [pairedSqLoss]
  | succ n ih =>
      rw [List.ofFn_succ, Fin.sum_univ_succ]
      simp only [pairedSqLoss]
      rw [ih]

private lemma pairedEntries_ofFn {n : ℕ} (p : Fin n → ℝ × ℝ) :
    pairedEntries (List.ofFn p) =
      (List.ofFn fun i => [(p i).1, (p i).2]).flatten := by
  induction n with
  | zero => simp [pairedEntries]
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ]
      simp only [pairedEntries, List.flatten_cons, ih]
      rfl

private lemma pairedEntries_ofFn_two {k : ℕ} (f : Fin (k * 2) → ℝ) :
    pairedEntries (List.ofFn fun r : Fin k =>
      (f ⟨r.val * 2, by omega⟩, f ⟨r.val * 2 + 1, by omega⟩)) =
      List.ofFn f := by
  rw [List.ofFn_mul, pairedEntries_ofFn]
  congr 1

private lemma adjacentSqLoss_pairedEntries (ps : List (ℝ × ℝ)) :
    adjacentSqLoss (pairedEntries ps) = pairedSqLoss ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      rcases p with ⟨a, b⟩
      simp only [pairedEntries, adjacentSqLoss, pairedSqLoss, ih]

/-- Consecutive pairing minimizes total squared gap among all reorderings of a sorted even list. -/
lemma adjacentSqLoss_le_of_perm_sorted {xs ys : List ℝ}
    (heven : Even xs.length) (hsorted : xs.Pairwise (· ≤ ·))
    (hperm : ys.Perm xs) : adjacentSqLoss xs ≤ adjacentSqLoss ys := by
  rw [← pairedSqLoss_listPairs ys]
  apply adjacentSqLoss_le_pairedSqLoss heven hsorted
  rw [pairedEntries_listPairs_of_even (hperm.length_eq ▸ heven)]
  exact hperm

/-- Every fixed-point-free involution can be enumerated in consecutive matched pairs. -/
lemma exists_pairingPerm (M : Match N) (hN : Even N) :
    ∃ σ : Equiv.Perm (Fin N), ∀ i j : Fin N,
      i.val + 1 = j.val → Even i.val → M.val (σ i) = σ j := by
  obtain ⟨k, hk⟩ := hN
  let R := {i : Fin N // i < M.val i}
  let qfun : R × Fin 2 → Fin N :=
    fun p => if p.2.val = 0 then p.1.val else M.val p.1.val
  have hqinj : Function.Injective qfun := by
    rintro ⟨a, u⟩ ⟨b, v⟩ huv
    fin_cases u <;> fin_cases v
    · simp only [qfun, Fin.zero_eta, Fin.val_zero, ↓reduceIte] at huv
      exact Prod.ext (Subtype.ext huv) rfl
    · simp only [qfun, Fin.zero_eta, Fin.val_zero, ↓reduceIte, Fin.isValue,
        one_ne_zero] at huv
      have hrev := congrArg M.val huv
      have hbb := M.property.1 b.val
      simp only [hbb] at hrev
      have : a.val < b.val := by simpa [← hrev] using a.property
      have : b.val < a.val := by simpa [huv] using b.property
      omega
    · simp only [qfun, Fin.isValue, one_ne_zero, ↓reduceIte,
        Fin.zero_eta, Fin.val_zero] at huv
      have hrev := congrArg M.val huv
      have haa := M.property.1 a.val
      simp only [haa] at hrev
      have : a.val < b.val := by simpa [huv] using a.property
      have : b.val < a.val := by simpa [← hrev] using b.property
      omega
    · simp only [qfun, one_ne_zero, ↓reduceIte] at huv
      have hrev := congrArg M.val huv
      have hab : a.val = b.val := by simpa only [M.property.1] using hrev
      exact Prod.ext (Subtype.ext hab) rfl
  have hqsurj : Function.Surjective qfun := by
    intro j
    by_cases hj : j < M.val j
    · exact ⟨(⟨j, hj⟩, 0), by simp [qfun]⟩
    · have hjne : M.val j ≠ j := M.property.2 j
      have hrev : M.val (M.val j) = j := M.property.1 j
      have hlt : M.val j < M.val (M.val j) := by
        rw [hrev]
        exact lt_of_le_of_ne (le_of_not_gt hj) hjne
      exact ⟨(⟨M.val j, hlt⟩, 1), by simp [qfun, hrev]⟩
  let q : R × Fin 2 ≃ Fin N := Equiv.ofBijective qfun ⟨hqinj, hqsurj⟩
  have hcard : Fintype.card R = k := by
    have hc := Fintype.card_congr q
    simp only [Fintype.card_prod, Fintype.card_fin] at hc
    omega
  let r : Fin k ≃ R :=
    (Fin.castOrderIso hcard.symm).toEquiv.trans (Fintype.equivFin R).symm
  let e : Fin N ≃ Fin k × Fin 2 :=
    (Fin.castOrderIso (show N = k * 2 by omega)).toEquiv.trans
      (finProdFinEquiv (m := k) (n := 2)).symm
  let σ : Equiv.Perm (Fin N) := e.trans ((Equiv.prodCongr r (Equiv.refl _)).trans q)
  refine ⟨σ, ?_⟩
  intro i j hij hi
  obtain ⟨t, ht⟩ := hi
  have hi0 : i.val % 2 = 0 := by omega
  have hi0' : (Fin.cast (show N = k * 2 by omega) i).modNat = (0 : Fin 2) := by
    apply Fin.ext
    simpa using hi0
  have hepair : (e i).1 = (e j).1 ∧ (e i).2 = 0 ∧ (e j).2 = 1 := by
    constructor
    · simp [e, finProdFinEquiv, Fin.ext_iff]
      omega
    · constructor
      · simp [e, finProdFinEquiv, Fin.ext_iff, hi0']
      · simp [e, finProdFinEquiv, Fin.ext_iff, hi0']
        omega
  rcases hepair with ⟨hfst, hi2, hj2⟩
  change M.val (q (r (e i).1, e i |>.2)) = q (r (e j).1, e j |>.2)
  rw [hfst, hi2, hj2]
  simp [q, qfun]

private lemma matchingCost_eq_adjacentSqLoss (M : Match N) (hN : Even N)
    (s : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (hσ : ∀ i j : Fin N, i.val + 1 = j.val → Even i.val →
      M.val (σ i) = σ j) :
    (1 / 2 : ℝ) * ∑ i : Fin N, (s i - s (M.val i)) ^ 2 =
      adjacentSqLoss (List.ofFn (s ∘ σ)) := by
  obtain ⟨k, hk⟩ := hN
  let e : Fin N ≃ Fin k × Fin 2 :=
    (Fin.castOrderIso (show N = k * 2 by omega)).toEquiv.trans
      (finProdFinEquiv (m := k) (n := 2)).symm
  let p : Fin k → ℝ × ℝ := fun r =>
    (s (σ (e.symm (r, 0))), s (σ (e.symm (r, 1))))
  have hpairs (r : Fin k) :
      M.val (σ (e.symm (r, 0))) = σ (e.symm (r, 1)) := by
    apply hσ
    · simp [e, finProdFinEquiv, Fin.ext_iff]
      omega
    · rw [Nat.even_iff]
      simp [e, finProdFinEquiv, Fin.ext_iff]
  have hpairs' (r : Fin k) :
      M.val (σ (e.symm (r, 1))) = σ (e.symm (r, 0)) := by
    rw [← hpairs r]
    exact M.property.1 _
  have hsum : (∑ i : Fin N, (s i - s (M.val i)) ^ 2) =
      2 * ∑ r : Fin k,
        (s (σ (e.symm (r, 1))) - s (σ (e.symm (r, 0)))) ^ 2 := by
    rw [← Equiv.sum_comp σ, ← Equiv.sum_comp e.symm]
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [Fin.sum_univ_two, hpairs r, hpairs' r]
    ring
  have hloss : pairedSqLoss (List.ofFn p) =
      ∑ r : Fin k,
        (s (σ (e.symm (r, 1))) - s (σ (e.symm (r, 0)))) ^ 2 := by
    rw [pairedSqLoss_ofFn]
  have hentries : pairedEntries (List.ofFn p) = List.ofFn (s ∘ σ) := by
    have hk2 : N = k * 2 := by omega
    let f : Fin (k * 2) → ℝ := fun u => s (σ (Fin.cast hk2.symm u))
    have hb := pairedEntries_ofFn_two f
    convert hb using 1
    · simp [p, f, e, finProdFinEquiv, Function.comp_def]
      apply congrArg pairedEntries
      congr 1
      funext r
      apply Prod.ext <;> simp only
      · congr 2
        apply Fin.ext
        simp
        omega
      · congr 2
        apply Fin.ext
        simp
        omega
    · apply List.ext_get
      · simp [hk2]
      · intro n hn₁ hn₂
        simp only [List.get_eq_getElem, List.getElem_ofFn]
        congr 2
  rw [hsum, ← hentries, adjacentSqLoss_pairedEntries, hloss]
  ring

lemma adjacent_matching_minimizes (hN : Even N) (hN2 : 2 ≤ N)
    (g : XSpace d → ℝ) (x : MainCovariates N d) (M : Match N) :
    pairLoss g x (oracleMatching g x hN hN2) ≤ pairLoss g x M := by
  let s : Fin N → ℝ := fun i => g (x i)
  let M₀ : Match N := oracleMatching g x hN hN2
  have hspec : AdjSortSpec s M₀ := by
    dsimp [M₀, oracleMatching, s]
    exact Classical.choose_spec (exists_adjSortMatching (fun i => g (x i)) hN hN2)
  rcases hspec with ⟨π, hord, hπ⟩
  obtain ⟨σ, hσ⟩ := exists_pairingPerm M hN
  have hsorted : (List.ofFn (s ∘ π)).Pairwise (· ≤ ·) := by
    rw [List.pairwise_ofFn]
    intro i j hij
    rcases hord i j hij with hlt | heq
    · exact hlt.le
    · exact heq.1.le
  have heven : Even (List.ofFn (s ∘ π)).length := by
    simpa using hN
  have hperm : (List.ofFn (s ∘ σ)).Perm (List.ofFn (s ∘ π)) :=
    (σ.ofFn_comp_perm s).trans (π.ofFn_comp_perm s).symm
  have hlist := adjacentSqLoss_le_of_perm_sorted heven hsorted hperm
  have hcost₀ := matchingCost_eq_adjacentSqLoss M₀ hN s π hπ
  have hcost := matchingCost_eq_adjacentSqLoss M hN s σ hσ
  unfold pairLoss
  change (1 / 2 : ℝ) * ∑ i : Fin N, (s i - s (M₀.val i)) ^ 2 ≤
    (1 / 2 : ℝ) * ∑ i : Fin N, (s i - s (M.val i)) ^ 2
  rw [hcost₀, hcost]
  exact hlist

-- @node: pairLoss_triangle_bound
lemma pairLoss_triangle_bound (f g : XSpace d → ℝ)
    (x : MainCovariates N d) (M : Match N) :
    pairLoss (fun y => f y + g y) x M ≤
      2 * pairLoss f x M + 2 * pairLoss g x M := by
  unfold pairLoss
  have hsum :
      (∑ i : Fin N, ((f (x i) + g (x i)) -
        (f (x (M.val i)) + g (x (M.val i)))) ^ 2) ≤
      ∑ i : Fin N, (2 * (f (x i) - f (x (M.val i))) ^ 2 +
        2 * (g (x i) - g (x (M.val i))) ^ 2) := by
    apply Finset.sum_le_sum
    intro i _
    nlinarith [sq_nonneg ((f (x i) - f (x (M.val i))) -
      (g (x i) - g (x (M.val i))))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  nlinarith

-- @node: pairLoss_difference_bound
lemma pairLoss_difference_bound (f g : XSpace d → ℝ)
    (x : MainCovariates N d) (M : Match N) :
    pairLoss (fun y => f y - g y) x M ≤
      2 * ∑ i : Fin N, (f (x i) - g (x i)) ^ 2 := by
  unfold pairLoss
  have hsum :
      (∑ i : Fin N, ((f (x i) - g (x i)) -
        (f (x (M.val i)) - g (x (M.val i)))) ^ 2) ≤
      ∑ i : Fin N, (2 * (f (x i) - g (x i)) ^ 2 +
        2 * (f (x (M.val i)) - g (x (M.val i))) ^ 2) := by
    apply Finset.sum_le_sum
    intro i _
    nlinarith [sq_nonneg ((f (x i) - g (x i)) +
      (f (x (M.val i)) - g (x (M.val i))))]
  have hperm : (∑ i : Fin N, (f (x (M.val i)) - g (x (M.val i))) ^ 2) =
      ∑ i : Fin N, (f (x i) - g (x i)) ^ 2 := by
    exact Equiv.sum_comp M.val (fun i : Fin N => (f (x i) - g (x i)) ^ 2)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hperm] at hsum
  nlinarith

lemma adjacent_matching_stability (hN : Even N) (hN2 : 2 ≤ N)
    (g ĝ : XSpace d → ℝ) (x : MainCovariates N d) :
    pairLoss g x (oracleMatching ĝ x hN hN2) ≤
      4 * pairLoss g x (oracleMatching g x hN hN2) +
        12 * ∑ i : Fin N, (g (x i) - ĝ (x i)) ^ 2 := by
  let e : XSpace d → ℝ := fun y => g y - ĝ y
  let M₁ := oracleMatching ĝ x hN hN2
  let M₀ := oracleMatching g x hN hN2
  have h₁ : pairLoss g x M₁ ≤ 2 * pairLoss ĝ x M₁ + 2 * pairLoss e x M₁ := by
    convert pairLoss_triangle_bound ĝ e x M₁ using 1 <;> simp [e]
  have h₂ : pairLoss ĝ x M₁ ≤ pairLoss ĝ x M₀ :=
    adjacent_matching_minimizes hN hN2 ĝ x M₀
  have h₃ : pairLoss ĝ x M₀ ≤ 2 * pairLoss g x M₀ + 2 * pairLoss e x M₀ := by
    have hh := pairLoss_triangle_bound g (fun y => -e y) x M₀
    have hneg : pairLoss (fun y => -e y) x M₀ = pairLoss e x M₀ := by
      unfold pairLoss
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hneg] at hh
    convert hh using 1
    congr 1
    funext y
    simp [e]
  have h₄ : pairLoss e x M₀ ≤ 2 * ∑ i : Fin N, (g (x i) - ĝ (x i)) ^ 2 := by
    simpa [e] using pairLoss_difference_bound g ĝ x M₀
  have h₅ : pairLoss e x M₁ ≤ 2 * ∑ i : Fin N, (g (x i) - ĝ (x i)) ^ 2 := by
    simpa [e] using pairLoss_difference_bound g ĝ x M₁
  dsimp [M₀, M₁] at *
  nlinarith

end CausalSmith.Experimentation.PilotscorePairingFrontier

module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.RoundingGeometry

/-! # Finite termination of ordered boundary rounding

A trace count forces a nonempty constructed nullspace basis whenever the active
count exceeds the retained constraint count. The phase invariant and strict
boundary progress then exhaust all active coordinates in at most n moves.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity
variable {n : ℕ}

/-- [ A vector with zero squared Euclidean length is zero.](goal) -/
-- @node: rowDot_self_eq_zero_iff
lemma rowDot_self_eq_zero_iff (v : Fin n → ℝ) : rowDot v v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    have hi := Finset.single_le_sum (fun j _ => mul_self_nonneg (v j))
      (Finset.mem_univ i)
    change v i * v i ≤ rowDot v v at hi
    rw [h] at hi
    change v i = 0
    nlinarith [sq_nonneg (v i)]
  · rintro rfl
    simp [rowDot]

/-- [ With no constraints the residual is the input vector itself.](goal) -/
-- @node: removeProjections_nil
lemma removeProjections_nil (v : Fin n → ℝ) : removeProjections [] v = v := by
  funext i
  simp [removeProjections]

/-- [ Gram--Schmidt never removes old vectors.](goal) -/
-- @node: insertOrtho_contains_old
lemma insertOrtho_contains_old (bs : List (Fin n → ℝ)) (v : Fin n → ℝ) :
    ∀ b ∈ bs, b ∈ insertOrtho bs v := by
  intro b hb
  dsimp only [insertOrtho]
  split_ifs <;> simp [hb]

/-- [ An empty insertion has both an empty input basis and a zero input vector.](goal) -/
-- @node: insertOrtho_eq_nil_iff
lemma insertOrtho_eq_nil_iff (bs : List (Fin n → ℝ)) (v : Fin n → ℝ) :
    insertOrtho bs v = [] ↔ bs = [] ∧ v = 0 := by
  constructor
  · intro h
    have hb : bs = [] := by
      by_contra hn
      obtain ⟨b, hmem⟩ := List.exists_mem_of_ne_nil bs hn
      have hm := insertOrtho_contains_old bs v b hmem
      rw [h] at hm
      simp at hm
    subst bs
    have hz : rowDot v v = 0 := by
      have hn : 0 ≤ rowDot v v := Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
      by_contra hh
      have hp : 0 < Real.sqrt (rowDot v v) := Real.sqrt_pos.2 (lt_of_le_of_ne hn (Ne.symm hh))
      simp [insertOrtho, removeProjections_nil, hp] at h
    exact ⟨rfl, (rowDot_self_eq_zero_iff v).mp hz⟩
  · rintro ⟨rfl, rfl⟩
    simp [insertOrtho, removeProjections, rowDot]

/-- [ The structural orthonormalization is empty only when every input vector is zero.](goal) -/
-- @node: orderedOrtho_eq_nil_iff
lemma orderedOrtho_eq_nil_iff (vs : List (Fin n → ℝ)) :
    orderedOrtho vs = [] ↔ ∀ v ∈ vs, v = 0 := by
  have hf (ls : List (Fin n → ℝ)) : ∀ bs,
      ls.foldl insertOrtho bs = [] ↔ bs = [] ∧ ∀ v ∈ ls, v = 0 := by
    induction ls with
    | nil => intro bs; simp
    | cons v ls ih =>
      intro bs
      rw [List.foldl_cons, ih, insertOrtho_eq_nil_iff]
      simp only [List.mem_cons, forall_eq_or_imp]
      tauto
  simpa [orderedOrtho] using hf vs []

/-- [ At most one vector is added by each insertion.](goal) -/
-- @node: insertOrtho_length_le
lemma insertOrtho_length_le (bs : List (Fin n → ℝ)) (v : Fin n → ℝ) :
    (insertOrtho bs v).length ≤ bs.length + 1 := by
  dsimp only [insertOrtho]
  split_ifs <;> simp

/-- [ Discarding residuals cannot increase the number of input constraints.](goal) -/
-- @node: orderedOrtho_length_le
lemma orderedOrtho_length_le (vs : List (Fin n → ℝ)) :
    (orderedOrtho vs).length ≤ vs.length := by
  have hf (ls : List (Fin n → ℝ)) : ∀ bs,
      (ls.foldl insertOrtho bs).length ≤ bs.length + ls.length := by
    induction ls with
    | nil => intro bs; simp
    | cons v ls ih =>
      intro bs
      have h := ih (insertOrtho bs v)
      have hi := insertOrtho_length_le bs v
      simp only [List.foldl_cons, List.length_cons]
      omega
  simpa [orderedOrtho] using hf vs []

/-- [ The constraint basis has no more vectors than retained rows.](goal) -/
-- @node: constraintBasis_length_le
lemma constraintBasis_length_le (a : Fin (n / 4) → Fin n → ℝ) (q : ℕ)
    (u : Fin n → ℝ) : (constraintBasis a q u).length ≤ q := by
  simpa [constraintBasis] using orderedOrtho_length_le
    ((List.range q).map (fun h => activeMask u (if hh : h < n / 4 then a ⟨h, hh⟩ else 0)))

/-- An empty constructed nullspace basis annihilates every projected coordinate vector. Under [the stated conditions](hyp:he), [the asserted mathematical result follows](goal). -/
-- @node: nullspaceBasis_empty_projection
lemma nullspaceBasis_empty_projection (a : Fin (n / 4) → Fin n → ℝ) (q : ℕ)
    (u : Fin n → ℝ) (he : nullspaceBasis a q u = []) (j : Fin n) :
    constraintProjection a q u (fun i => if i = j then 1 else 0) = 0 := by
  apply (orderedOrtho_eq_nil_iff _).mp he
  exact List.mem_map.mpr ⟨j, by simp, rfl⟩

/-- The active-coordinate count is the trace of the active mask. [The asserted mathematical result follows](goal). -/
-- @node: activeIndices_length_eq_trace
lemma activeIndices_length_eq_trace (u : Fin n → ℝ) :
    ((activeIndices u).length : ℝ) = ∑ j : Fin n, if |u j| < 1 then 1 else 0 := by
  classical
  have he : (activeIndices u).toFinset = Finset.univ.filter (fun j => |u j| < 1) := by
    ext j
    simp [mem_activeIndices]
  rw [← List.toFinset_card_of_nodup (activeIndices_nodup u), he]
  simp

/-- [ Summing the diagonal contributions of a finite basis gives its total squared length.](goal) -/
-- @node: basis_diagonal_trace
lemma basis_diagonal_trace (bs : List (Fin n → ℝ)) :
    (∑ j : Fin n, (bs.map (fun b => b j * b j)).sum) =
      (bs.map (fun b => rowDot b b)).sum := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]
    rfl

/-- Unit squared lengths make the basis trace exactly its number of vectors. Under [the stated conditions](hyp:hb), [the asserted mathematical result follows](goal). -/
-- @node: basis_unit_trace
lemma basis_unit_trace (bs : List (Fin n → ℝ))
    (hb : ∀ b ∈ bs, rowDot b b = 1) :
    (bs.map (fun b => rowDot b b)).sum = (bs.length : ℝ) := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [hb b (by simp), ih (fun c hc => hb c (by simp [hc]))]
    ring

/-- [ If all projected coordinate vectors vanish, the active trace equals the constraint trace.](goal) Under [the stated conditions](hyp:he). -/
-- @node: nullspaceBasis_empty_trace
lemma nullspaceBasis_empty_trace (a : Fin (n / 4) → Fin n → ℝ) (q : ℕ)
    (u : Fin n → ℝ) (he : nullspaceBasis a q u = []) :
    (activeIndices u).length = (constraintBasis a q u).length := by
  have hs : ∀ b ∈ constraintBasis a q u, ∀ j, ¬|u j| < 1 → b j = 0 := by
    apply orderedOrtho_active_support
    intro b hb j hj
    obtain ⟨h, _, rfl⟩ := List.mem_map.mp hb
    simp [activeMask, hj]
  have hd (j : Fin n) :
      (if |u j| < 1 then (1 : ℝ) else 0) =
        ((constraintBasis a q u).map (fun b => b j * b j)).sum := by
    have hz := congrFun (nullspaceBasis_empty_projection a q u he j) j
    have hdot (b : Fin n → ℝ) (hb : b ∈ constraintBasis a q u) :
        rowDot (activeMask u (fun i => if i = j then 1 else 0)) b = b j := by
      have hm : activeMask u (fun i => if i = j then 1 else 0) =
          (fun i => if i = j then (if |u j| < 1 then 1 else 0) else 0) := by
        funext i
        by_cases hi : i = j
        · subst i; simp [activeMask]
        · simp [activeMask, hi]
      rw [hm]
      by_cases hj : |u j| < 1
      · simp [rowDot, hj]
      · simp [rowDot, hj, hs b hb j hj]
    have hmap : ((constraintBasis a q u).map (fun b =>
        rowDot (activeMask u (fun i => if i = j then 1 else 0)) b * b j)).sum =
        ((constraintBasis a q u).map (fun b => b j * b j)).sum := by
      congr 1
      apply List.map_congr_left
      intro b hb
      rw [hdot b hb]
    change (if |u j| < 1 then (if j = j then (1 : ℝ) else 0) else 0) -
      ((constraintBasis a q u).map (fun b =>
        rowDot (activeMask u (fun i => if i = j then 1 else 0)) b * b j)).sum = 0 at hz
    simp only [if_true, hmap] at hz
    linarith
  have ht : ((activeIndices u).length : ℝ) = (constraintBasis a q u).length := by
    rw [activeIndices_length_eq_trace, Finset.sum_congr rfl (fun j _ => hd j),
      basis_diagonal_trace]
    exact basis_unit_trace (constraintBasis a q u) (orderedOrtho_unit_length _)
  exact_mod_cast ht

/-- [ More active coordinates than retained rows forces an actual constructed direction.](goal) Under [the stated conditions](hyp:hq). -/
-- @node: nullspaceBasis_nonempty_of_active_count
lemma nullspaceBasis_nonempty_of_active_count (a : Fin (n / 4) → Fin n → ℝ)
    (q : ℕ) (u : Fin n → ℝ) (hq : q < (activeIndices u).length) :
    nullspaceBasis a q u ≠ [] := by
  intro he
  have ht := nullspaceBasis_empty_trace a q u he
  have hl := constraintBasis_length_le a q u
  omega

/-- [ The retained row count never exceeds the phase stopping count.](goal) Under [the stated conditions](hyp:hq). -/
-- @node: phaseMove_retained_le_stop
lemma phaseMove_retained_le_stop (a : Fin (n / 4) → Fin n → ℝ)
    (st : RoundingState n) (seed₁ seed₂ : ℝ) (hq : st.2.2 ≤ st.2.1) :
    (phaseMove a st seed₁ seed₂).2.2 ≤ (phaseMove a st seed₁ seed₂).2.1 := by
  dsimp only [phaseMove]
  split_ifs with hsmall hstart
  · cases activeIndices st.1 with
    | nil => exact hq
    | cons i is => simp
  · dsimp only
    omega
  · exact hq

/-- [ At zero active count the padded iteration is exactly the identity.](goal) Under [the stated conditions](hyp:he). -/
-- @node: phaseMove_fixed_of_no_active
lemma phaseMove_fixed_of_no_active (a : Fin (n / 4) → Fin n → ℝ)
    (st : RoundingState n) (seed₁ seed₂ : ℝ) (he : activeIndices st.1 = []) :
    phaseMove a st seed₁ seed₂ = st := by
  simp [phaseMove, he]

/-- [ The phase invariant ensures a nonempty constructed basis on every live nonterminal move.](goal) Under [the stated conditions](hyp:hq,hlarge). -/
-- @node: phaseMove_nonterminal_basis_nonempty
lemma phaseMove_nonterminal_basis_nonempty (a : Fin (n / 4) → Fin n → ℝ)
    (st : RoundingState n) (hq : st.2.2 ≤ st.2.1)
    (hlarge : ¬((activeIndices st.1).length ≤ st.2.1 ∧
      (activeIndices st.1).length ≤ 3)) :
    nullspaceBasis a
      (if (activeIndices st.1).length ≤ st.2.1 then
        (activeIndices st.1).length / 4 else st.2.2) st.1 ≠ [] := by
  apply nullspaceBasis_nonempty_of_active_count
  split_ifs with hstart
  · have hr : 3 < (activeIndices st.1).length := by omega
    omega
  · omega

/-- [ Every live move preserves the cube and removes at least one active coordinate.](goal) Under [the stated conditions](hyp:hu,hq,hne). -/
-- @node: phaseMove_progress
lemma phaseMove_progress (a : Fin (n / 4) → Fin n → ℝ)
    (st : RoundingState n) (seed₁ seed₂ : ℝ)
    (hu : ∀ j, |st.1 j| ≤ 1) (hq : st.2.2 ≤ st.2.1)
    (hne : activeIndices st.1 ≠ []) :
    (∀ j, |(phaseMove a st seed₁ seed₂).1 j| ≤ 1) ∧
    (activeIndices (phaseMove a st seed₁ seed₂).1).length < (activeIndices st.1).length := by
  by_cases hsmall : (activeIndices st.1).length ≤ st.2.1 ∧
      (activeIndices st.1).length ≤ 3
  · exact phaseMove_terminal_progress a st seed₁ seed₂ hu hsmall hne
  · have hp := roundingStep_progress_of_nonempty_basis a
      (if (activeIndices st.1).length ≤ st.2.1 then
        (activeIndices st.1).length / 4 else st.2.2) st.1 seed₁ seed₂ hu
      (phaseMove_nonterminal_basis_nonempty a st hq hsmall)
    simpa only [phaseMove, if_neg hsmall] using hp

/-- [ One padded move preserves the cube and lowers the active count by one until exhaustion.](goal) Under [the stated conditions](hyp:hu,hq). -/
-- @node: phaseMove_cube_and_count
lemma phaseMove_cube_and_count (a : Fin (n / 4) → Fin n → ℝ)
    (st : RoundingState n) (seed₁ seed₂ : ℝ)
    (hu : ∀ j, |st.1 j| ≤ 1) (hq : st.2.2 ≤ st.2.1) :
    (∀ j, |(phaseMove a st seed₁ seed₂).1 j| ≤ 1) ∧
    (activeIndices (phaseMove a st seed₁ seed₂).1).length ≤
      (activeIndices st.1).length - 1 := by
  by_cases he : activeIndices st.1 = []
  · rw [phaseMove_fixed_of_no_active a st seed₁ seed₂ he, he]
    exact ⟨hu, by simp⟩
  · have hp := phaseMove_progress a st seed₁ seed₂ hu hq he
    exact ⟨hp.1, by have hh := hp.2; omega⟩

/-- The finite iteration preserves the phase invariant at every step. [The asserted mathematical result follows](goal). -/
-- @node: roundingIteration_retained_le_stop
lemma roundingIteration_retained_le_stop (a : Fin (n / 4) → Fin n → ℝ)
    (seeds : RoundingSeeds n) (k : ℕ) :
    (roundingIteration a seeds k).2.2 ≤ (roundingIteration a seeds k).2.1 := by
  induction k with
  | zero => simp [roundingIteration]
  | succ k ih => exact phaseMove_retained_le_stop a _ _ _ ih

/-- [ Every seed realization remains in the cube and has at most n-k active coordinates.](goal) -/
-- @node: roundingIteration_cube_and_count
lemma roundingIteration_cube_and_count (a : Fin (n / 4) → Fin n → ℝ)
    (seeds : RoundingSeeds n) (k : ℕ) :
    (∀ j, |(roundingIteration a seeds k).1 j| ≤ 1) ∧
    (activeIndices (roundingIteration a seeds k).1).length ≤ n - k := by
  induction k with
  | zero => simp [roundingIteration, activeIndices]
  | succ k ih =>
    have hp := phaseMove_cube_and_count a (roundingIteration a seeds k)
      (roundingSeed seeds (2 * k)) (roundingSeed seeds (2 * k + 1)) ih.1
      (roundingIteration_retained_le_stop a seeds k)
    refine ⟨hp.1, ?_⟩
    change (activeIndices (phaseMove a (roundingIteration a seeds k)
      (roundingSeed seeds (2 * k)) (roundingSeed seeds (2 * k + 1))).1).length ≤ n - (k + 1)
    have hh := hp.2
    have hi := ih.2
    omega

/-- [ After n moves no coordinate is fractional.](goal) -/
-- @node: roundingIteration_no_active
lemma roundingIteration_no_active (a : Fin (n / 4) → Fin n → ℝ)
    (seeds : RoundingSeeds n) : activeIndices (roundingIteration a seeds n).1 = [] := by
  have h := (roundingIteration_cube_and_count a seeds n).2
  have he : (activeIndices (roundingIteration a seeds n).1).length = 0 := by omega
  simpa using he

/-- [ The actual terminal state equals the output signing, for every seed realization.](goal) -/
-- @node: roundingIteration_terminal_eq_sign
lemma roundingIteration_terminal_eq_sign (a : Fin (n / 4) → Fin n → ℝ)
    (seeds : RoundingSeeds n) (i : Fin n) :
    (roundingIteration a seeds n).1 i = sgn (orderedBoundaryRounding n a seeds i) := by
  have hu := (roundingIteration_cube_and_count a seeds n).1 i
  have hnot : ¬|(roundingIteration a seeds n).1 i| < 1 := by
    intro hi
    have hm := (mem_activeIndices _ i).mpr hi
    rw [roundingIteration_no_active a seeds] at hm
    simp at hm
  have he : |(roundingIteration a seeds n).1 i| = 1 := le_antisymm hu (le_of_not_gt hnot)
  by_cases hp : 0 < (roundingIteration a seeds n).1 i
  · rw [abs_of_pos hp] at he
    simpa [orderedBoundaryRounding, sgn, hp] using he
  · rw [abs_of_nonpos (le_of_not_gt hp)] at he
    simp only [orderedBoundaryRounding, hp, decide_false, sgn, Bool.false_eq_true, if_false]
    linarith

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity

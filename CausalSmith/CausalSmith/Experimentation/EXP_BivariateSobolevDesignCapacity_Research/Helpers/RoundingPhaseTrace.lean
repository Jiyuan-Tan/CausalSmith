module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.RoundingStoppedPhases

/-! # Protected rows along the actual rounding trace

The retained prefix dominates one quarter of the active count on live moves.
Consequently, row h cannot change until fewer than 4h coordinates remain active.
These pathwise facts connect the actual iteration to the unprotected phase budget.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ Active counts decrease monotonically along the actual seed realization.](goal) -/
-- @node: roundingIteration_active_count_antitone
lemma roundingIteration_active_count_antitone (a : Fin (n / 4) → Fin n → ℝ)
    (seeds : RoundingSeeds n) :
    Antitone (fun k => (activeIndices (roundingIteration a seeds k).1).length) := by
  apply antitone_nat_of_succ_le
  intro k
  have hp := (phaseMove_cube_and_count a (roundingIteration a seeds k)
    (roundingSeed seeds (2 * k)) (roundingSeed seeds (2 * k + 1))
    (roundingIteration_cube_and_count a seeds k).1
    (roundingIteration_retained_le_stop a seeds k)).2
  exact hp.trans (Nat.sub_le _ _)

/-- A move preserves the lower bound on the retained prefix when its phase is live. Under [the stated conditions](hyp:hu,hq,hn,hlive), [the asserted mathematical result follows](goal). -/
-- @node: phaseMove_live_prefix_invariant
lemma phaseMove_live_prefix_invariant (a : Fin (n / 4) → Fin n → ℝ)
    (st : RoundingState n) (seed₁ seed₂ : ℝ)
    (hu : ∀ i, |st.1 i| ≤ 1) (hq : st.2.2 ≤ st.2.1)
    (hn : (activeIndices st.1).length ≤ n)
    (hlive : st.2.1 < (activeIndices st.1).length →
      (activeIndices st.1).length / 4 ≤ st.2.2) :
    (phaseMove a st seed₁ seed₂).2.1 <
        (activeIndices (phaseMove a st seed₁ seed₂).1).length →
      (activeIndices (phaseMove a st seed₁ seed₂).1).length / 4 ≤
        (phaseMove a st seed₁ seed₂).2.2 := by
  have hp := (phaseMove_cube_and_count a st seed₁ seed₂ hu hq).2
  have hmono : (activeIndices (phaseMove a st seed₁ seed₂).1).length ≤
      (activeIndices st.1).length := hp.trans (Nat.sub_le _ _)
  by_cases hs : (activeIndices st.1).length ≤ st.2.1 ∧
      (activeIndices st.1).length ≤ 3
  · cases he : activeIndices st.1 with
    | nil => simp [phaseMove, hs, he]
    | cons i is =>
      have hstop : (phaseMove a st seed₁ seed₂).2.1 = n := by
        dsimp only [phaseMove]
        rw [if_pos hs]
        simp only [he]
      rw [hstop]
      intro h
      omega
  ·
    have he : (phaseMove a st seed₁ seed₂).2.2 =
        if (activeIndices st.1).length ≤ st.2.1 then
          (activeIndices st.1).length / 4 else st.2.2 := by
        simp [phaseMove, hs]
    rw [he]
    intro _
    split_ifs with hnew
    · exact Nat.div_le_div_right hmono
    · exact (Nat.div_le_div_right hmono).trans (hlive (by omega))

/-- On a live actual phase, the retained prefix contains at least a quarter of
its current active coordinates. [The asserted mathematical result follows](goal). -/
-- @node: roundingIteration_live_prefix_invariant
lemma roundingIteration_live_prefix_invariant (a : Fin (n / 4) → Fin n → ℝ)
    (seeds : RoundingSeeds n) (k : ℕ) :
    (roundingIteration a seeds k).2.1 <
        (activeIndices (roundingIteration a seeds k).1).length →
      (activeIndices (roundingIteration a seeds k).1).length / 4 ≤
        (roundingIteration a seeds k).2.2 := by
  induction k with
  | zero =>
    have hn := (roundingIteration_cube_and_count a seeds 0).2
    intro h
    simp only [roundingIteration] at h hn
    omega
  | succ k ih =>
    exact phaseMove_live_prefix_invariant a _ _ _
      (roundingIteration_cube_and_count a seeds k).1
      (roundingIteration_retained_le_stop a seeds k)
      ((roundingIteration_cube_and_count a seeds k).2.trans (Nat.sub_le _ _)) ih

/-- A supplied row stays fixed on a move with at least four times its row number
active coordinates, whether that move starts a new phase or continues one. Under [the stated conditions](hyp:hactive), [the asserted mathematical result follows](goal). -/
-- @node: roundingIteration_protected_row_fixed
lemma roundingIteration_protected_row_fixed (a : Fin (n / 4) → Fin n → ℝ)
    (seeds : RoundingSeeds n) (k : ℕ) (h : Fin (n / 4))
    (hactive : 4 * (h.val + 1) ≤ (activeIndices (roundingIteration a seeds k).1).length) :
    rowDot (a h) (roundingIteration a seeds (k + 1)).1 =
      rowDot (a h) (roundingIteration a seeds k).1 := by
  let st := roundingIteration a seeds k
  have hs : ¬((activeIndices st.1).length ≤ st.2.1 ∧
      (activeIndices st.1).length ≤ 3) := by
    dsimp only [st]
    omega
  have hret : h.val < (if (activeIndices st.1).length ≤ st.2.1
      then (activeIndices st.1).length / 4 else st.2.2) := by
    split_ifs with hnew
    · dsimp only [st]
      omega
    · have hi := roundingIteration_live_prefix_invariant a seeds k (by
        change st.2.1 < (activeIndices st.1).length
        omega)
      dsimp only [st] at *
      omega
  change rowDot (a h) (phaseMove a st _ _).1 = rowDot (a h) st.1
  simp only [phaseMove, if_neg hs]
  exact roundingStep_retained_row_fixed a _ st.1 _ _ h hret

/-- [ While a phase is live, its stopping threshold and retained row count do not
change on the next actual move.](goal) Under [the stated conditions](hyp:hlive). -/
-- @node: roundingIteration_live_phase_metadata
lemma roundingIteration_live_phase_metadata (a : Fin (n / 4) → Fin n → ℝ)
    (seeds : RoundingSeeds n) (k : ℕ)
    (hlive : (roundingIteration a seeds k).2.1 <
      (activeIndices (roundingIteration a seeds k).1).length) :
    (roundingIteration a seeds (k + 1)).2 = (roundingIteration a seeds k).2 := by
  have hnew : ¬(activeIndices (roundingIteration a seeds k).1).length ≤
      (roundingIteration a seeds k).2.1 := by omega
  simp [roundingIteration, phaseMove, hnew]

/-- [ A supplied row is still zero at every actual state above its protection
threshold, because all earlier states have at least as many active coordinates.](goal) Under [the stated conditions](hyp:hactive). -/
-- @node: roundingIteration_protected_row_zero
lemma roundingIteration_protected_row_zero (a : Fin (n / 4) → Fin n → ℝ)
    (seeds : RoundingSeeds n) (k : ℕ) (h : Fin (n / 4))
    (hactive : 4 * (h.val + 1) ≤ (activeIndices (roundingIteration a seeds k).1).length) :
    rowDot (a h) (roundingIteration a seeds k).1 = 0 := by
  induction k with
  | zero => simp [roundingIteration, rowDot]
  | succ k ih =>
    have hk : 4 * (h.val + 1) ≤
        (activeIndices (roundingIteration a seeds k).1).length :=
      hactive.trans (roundingIteration_active_count_antitone a seeds (Nat.le_succ k))
    rw [roundingIteration_protected_row_fixed a seeds k h hk]
    exact ih hk

/-- [ The paper's one-based row numbering has the same protection threshold, even
for rows beyond the supplied prefix (whose protection premise is impossible).](goal) Under [the stated conditions](hyp:hh,hactive). -/
-- @node: roundingIteration_numbered_protected_row_fixed
lemma roundingIteration_numbered_protected_row_fixed (rows : ℕ → Fin n → ℝ)
    (seeds : RoundingSeeds n) (k h : ℕ) (hh : 1 ≤ h)
    (hactive : 4 * h ≤ (activeIndices (roundingIteration (rowPrefix rows) seeds k).1).length) :
    rowDot (rows h) (roundingIteration (rowPrefix rows) seeds (k + 1)).1 =
      rowDot (rows h) (roundingIteration (rowPrefix rows) seeds k).1 := by
  have hn := (roundingIteration_cube_and_count (rowPrefix rows) seeds k).2
  have hprefix : h - 1 < n / 4 := by omega
  have he : (h - 1) + 1 = h := by omega
  simpa only [rowPrefix, he] using
    roundingIteration_protected_row_fixed (rowPrefix rows) seeds k
      ⟨h - 1, hprefix⟩ (by simpa only [he] using hactive)

/-- [ Protection can be represented by a zero-padded increment supported precisely
on the unprotected active-count event.](goal) Under [the stated conditions](hyp:hh). -/
-- @node: roundingIteration_unprotected_row_increment
lemma roundingIteration_unprotected_row_increment (rows : ℕ → Fin n → ℝ)
    (seeds : RoundingSeeds n) (k h : ℕ) (hh : 1 ≤ h) :
    rowDot (rows h) (fun i =>
      (roundingIteration (rowPrefix rows) seeds (k + 1)).1 i -
      (roundingIteration (rowPrefix rows) seeds k).1 i) =
    if (activeIndices (roundingIteration (rowPrefix rows) seeds k).1).length < 4 * h
      then rowDot (rows h) (fun i =>
        (roundingIteration (rowPrefix rows) seeds (k + 1)).1 i -
        (roundingIteration (rowPrefix rows) seeds k).1 i) else 0 := by
  split_ifs with hsmall
  · rfl
  · change dotProduct (rows h) (_ - _) = 0
    rw [dotProduct_sub]
    exact sub_eq_zero.mpr
      (roundingIteration_numbered_protected_row_fixed rows seeds k h hh (by omega))

/-- The actual active count is a Borel statistic of the seeds. This uses [the stated conclusion](goal). -/
@[fun_prop]
-- @node: roundingIteration_active_count_measurable
lemma roundingIteration_active_count_measurable (a : Fin (n / 4) → Fin n → ℝ)
    (k : ℕ) : Measurable (fun seeds : RoundingSeeds n =>
      (activeIndices (roundingIteration a seeds k).1).length) := by
  have hu : Measurable (fun seeds : RoundingSeeds n => (roundingIteration a seeds k).1) := by
    fun_prop
  exact activeIndices_consumer_measurable _ hu (fun _ cs => cs.length)
    (fun _ => measurable_const)

/-- The event that a numbered row is unprotected before a move is Borel. [The asserted mathematical result follows](goal). -/
-- @node: roundingIteration_unprotected_event_measurable
lemma roundingIteration_unprotected_event_measurable (a : Fin (n / 4) → Fin n → ℝ)
    (k h : ℕ) : MeasurableSet {seeds : RoundingSeeds n |
      (activeIndices (roundingIteration a seeds k).1).length < 4 * h} := by
  exact measurableSet_lt (roundingIteration_active_count_measurable a k) measurable_const

/-- Protection is decided before either fresh seed used by the next move is read. Under [the stated conditions](hyp:hj), [the asserted mathematical result follows](goal). -/
-- @node: roundingIteration_unprotected_event_predictable
lemma roundingIteration_unprotected_event_predictable (a : Fin (n / 4) → Fin n → ℝ)
    (k h : ℕ) (j : Fin (3 * n)) (hj : 2 * k ≤ j.val)
    (seeds : RoundingSeeds n) (t : ℝ) :
    ((activeIndices (roundingIteration a (Function.update seeds j t) k).1).length < 4 * h) ↔
      (activeIndices (roundingIteration a seeds k).1).length < 4 * h := by
  rw [roundingIteration_update_future a seeds k j t hj]

/-- [ Once a row is unprotected it remains so; the selected moves form a terminal
interval of the actual trace.](goal) Under [the stated conditions](hyp:hkl,hk). -/
-- @node: roundingIteration_unprotected_persistent
lemma roundingIteration_unprotected_persistent (a : Fin (n / 4) → Fin n → ℝ)
    (seeds : RoundingSeeds n) (k l h : ℕ) (hkl : k ≤ l)
    (hk : (activeIndices (roundingIteration a seeds k).1).length < 4 * h) :
    (activeIndices (roundingIteration a seeds l).1).length < 4 * h := by
  exact (roundingIteration_active_count_antitone a seeds hkl).trans_lt hk

/-- [ The final row second moment is exactly the sum over its unprotected moves.
This specializes the proved martingale identity to the paper's actual trace.](goal) Under [the stated conditions](hyp:hh). -/
-- @node: orderedBoundaryRounding_unprotected_second_moment_sum
lemma orderedBoundaryRounding_unprotected_second_moment_sum
    (rows : ℕ → Fin n → ℝ) (h : ℕ) (hh : 1 ≤ h) :
    (∫ seeds, (∑ i, rows h i * sgn (orderedBoundaryRounding n (rowPrefix rows) seeds i)) ^ 2
      ∂roundingSeedLaw n) =
    ∑ k ∈ Finset.range n, ∫ seeds,
      (Set.indicator {seeds | (activeIndices (roundingIteration (rowPrefix rows) seeds k).1).length < 4 * h}
         (fun seeds => rowDot (rows h) (fun i =>
          (roundingIteration (rowPrefix rows) seeds (k + 1)).1 i -
          (roundingIteration (rowPrefix rows) seeds k).1 i)) seeds) ^ 2
      ∂roundingSeedLaw n := by
  rw [orderedBoundaryRounding_row_second_moment_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply integral_congr_ae
  filter_upwards [] with seeds
  by_cases hs : (activeIndices (roundingIteration (rowPrefix rows) seeds k).1).length < 4 * h
  · simp only [Set.indicator, Set.mem_setOf_eq, hs, if_true]
    congr 1
    change dotProduct (rows h) _ - dotProduct (rows h) _ =
      dotProduct (rows h) (_ - _)
    exact (dotProduct_sub _ _ _).symm
  · have he := roundingIteration_numbered_protected_row_fixed rows seeds k h hh (by omega)
    simp only [Set.indicator, Set.mem_setOf_eq, hs, if_false, he, sub_self]

/-- [ A nonterminal refresh records exactly the paper's halving threshold and
quarter-prefix length for its realized starting active count.](goal) Under [the stated conditions](hyp:hnew,hlarge). -/
-- @node: roundingIteration_new_phase_metadata
lemma roundingIteration_new_phase_metadata (a : Fin (n / 4) → Fin n → ℝ)
    (seeds : RoundingSeeds n) (k : ℕ)
    (hnew : (activeIndices (roundingIteration a seeds k).1).length ≤
      (roundingIteration a seeds k).2.1)
    (hlarge : 4 ≤ (activeIndices (roundingIteration a seeds k).1).length) :
    (roundingIteration a seeds (k + 1)).2 =
      ((activeIndices (roundingIteration a seeds k).1).length / 2,
        (activeIndices (roundingIteration a seeds k).1).length / 4) := by
  have hs : ¬((activeIndices (roundingIteration a seeds k).1).length ≤
      (roundingIteration a seeds k).2.1 ∧
        (activeIndices (roundingIteration a seeds k).1).length ≤ 3) := by omega
  change (phaseMove a (roundingIteration a seeds k) _ _).2 = _
  simp only [phaseMove, if_neg hs, if_pos hnew]

/-- [ Keeping a refreshed phase's metadata until its threshold is reached gives
an actual active count at most half that phase's starting count.](goal) Under [the stated conditions](hyp:hnew,hlarge,hmetadata,hend). -/
-- @node: roundingIteration_phase_end_halves
lemma roundingIteration_phase_end_halves (a : Fin (n / 4) → Fin n → ℝ)
    (seeds : RoundingSeeds n) (k l : ℕ)
    (hnew : (activeIndices (roundingIteration a seeds k).1).length ≤
      (roundingIteration a seeds k).2.1)
    (hlarge : 4 ≤ (activeIndices (roundingIteration a seeds k).1).length)
    (hmetadata : (roundingIteration a seeds l).2 =
      (roundingIteration a seeds (k + 1)).2)
    (hend : (activeIndices (roundingIteration a seeds l).1).length ≤
      (roundingIteration a seeds l).2.1) :
    2 * (activeIndices (roundingIteration a seeds l).1).length ≤
      (activeIndices (roundingIteration a seeds k).1).length := by
  have he := roundingIteration_new_phase_metadata a seeds k hnew hlarge
  rw [hmetadata, he] at hend
  omega

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity

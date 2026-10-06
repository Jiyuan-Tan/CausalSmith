module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorSegmentSplit
public import Mathlib.Data.List.GetD

/-!
# Prefix transport for decoded structural segments

Complete-history coordinates through epoch `t` depend only on the first
`t + 1` generated steps.  These pointwise identities let segment-law
pushforwards use the prefix truncation theorem for `segmentFrom`.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open CausalSmith.Stat.PomdpLatentOverlapMinimax

/-- Taking a prefix does not alter a padded list coordinate strictly before the prefix endpoint.
For [the first event](hyp:A), [the path](hyp:path), [the history length](hyp:k), [the i](hyp:i),
[the i assumption](hyp:hi), and [the fallback state](hyp:fallback), this establishes
[the segment get d take of strict bound result](goal). -/
-- @node: segment_getD_take_of_lt
lemma segment_getD_take_of_lt {A : Type*} (path : List A) (k i : Nat)
    (hi : i < k) (fallback : A) :
    (path.take k).getD i fallback = path.getD i fallback := by
  simp [List.getD, hi]

/-- The decoded state at an epoch is unchanged after retaining every step up to and including
that epoch. For [the sample size](hyp:n), [the observed-state count](hyp:nX),
[the hidden-state count](hyp:nH), [the fallback state](hyp:fallback), [the state](hyp:s),
[the path](hyp:path), [the history length](hyp:k), [the epoch index](hyp:t), and
[the epoch index assumption](hyp:ht), this establishes
[the decode segment take cur state of strict bound result](goal). -/
-- @node: decodeSegment_take_curState_of_lt
lemma decodeSegment_take_curState_of_lt {n nX nH : Nat}
    (fallback s : JointState nX nH)
    (path : List (Bool × ℝ × JointState nX nH)) (k : Nat) (t : Fin n)
    (ht : t.val < k) :
    curState t (decodeSegment fallback (s, path.take k)) =
      curState t (decodeSegment fallback (s, path)) := by
  change (if t.val = 0 then s else
      ((path.take k).getD (t.val - 1) (false, 0, fallback)).2.2) =
    (if t.val = 0 then s else
      (path.getD (t.val - 1) (false, 0, fallback)).2.2)
  by_cases h : t.val = 0
  · simp [h]
  · simp only [h, if_false]
    rw [segment_getD_take_of_lt path k (t.val - 1) (by omega)]

/-- The decoded action at an epoch is unchanged after retaining every step up to and including
that epoch. For [the sample size](hyp:n), [the observed-state count](hyp:nX),
[the hidden-state count](hyp:nH), [the fallback state](hyp:fallback), [the state](hyp:s),
[the path](hyp:path), [the history length](hyp:k), [the epoch index](hyp:t), and
[the epoch index assumption](hyp:ht), this establishes
[the decode segment take action at of strict bound result](goal). -/
-- @node: decodeSegment_take_actionAt_of_lt
lemma decodeSegment_take_actionAt_of_lt {n nX nH : Nat}
    (fallback s : JointState nX nH)
    (path : List (Bool × ℝ × JointState nX nH)) (k : Nat) (t : Fin n)
    (ht : t.val < k) :
    actionAt t (decodeSegment fallback (s, path.take k)) =
      actionAt t (decodeSegment fallback (s, path)) := by
  change ((path.take k).getD t.val (false, 0, fallback)).1 =
    (path.getD t.val (false, 0, fallback)).1
  rw [segment_getD_take_of_lt path k t.val ht]

/-- The decoded reward at an epoch is unchanged after retaining every step up to and including
that epoch. For [the sample size](hyp:n), [the observed-state count](hyp:nX),
[the hidden-state count](hyp:nH), [the fallback state](hyp:fallback), [the state](hyp:s),
[the path](hyp:path), [the history length](hyp:k), [the epoch index](hyp:t), and
[the epoch index assumption](hyp:ht), this establishes
[the decode segment take reward at of strict bound result](goal). -/
-- @node: decodeSegment_take_rewardAt_of_lt
lemma decodeSegment_take_rewardAt_of_lt {n nX nH : Nat}
    (fallback s : JointState nX nH)
    (path : List (Bool × ℝ × JointState nX nH)) (k : Nat) (t : Fin n)
    (ht : t.val < k) :
    rewardAt t (decodeSegment fallback (s, path.take k)) =
      rewardAt t (decodeSegment fallback (s, path)) := by
  change ((path.take k).getD t.val (false, 0, fallback)).2.1 =
    (path.getD t.val (false, 0, fallback)).2.1
  rw [segment_getD_take_of_lt path k t.val ht]

/-- The decoded successor state at an epoch is unchanged after retaining every step up to and
including that epoch. For [the sample size](hyp:n), [the observed-state count](hyp:nX),
[the hidden-state count](hyp:nH), [the fallback state](hyp:fallback), [the state](hyp:s),
[the path](hyp:path), [the history length](hyp:k), [the epoch index](hyp:t), and
[the epoch index assumption](hyp:ht), this establishes
[the decode segment take next state of strict bound result](goal). -/
-- @node: decodeSegment_take_nextState_of_lt
lemma decodeSegment_take_nextState_of_lt {n nX nH : Nat}
    (fallback s : JointState nX nH)
    (path : List (Bool × ℝ × JointState nX nH)) (k : Nat) (t : Fin n)
    (ht : t.val < k) :
    nextState t (decodeSegment fallback (s, path.take k)) =
      nextState t (decodeSegment fallback (s, path)) := by
  change ((path.take k).getD t.val (false, 0, fallback)).2.2 =
    (path.getD t.val (false, 0, fallback)).2.2
  rw [segment_getD_take_of_lt path k t.val ht]

/-- The full state-history coordinate is determined by the first `t + 1` generated steps. For
[the sample size](hyp:n), [the observed-state count](hyp:nX), [the hidden-state count](hyp:nH),
[the fallback state](hyp:fallback), [the state](hyp:s), [the path](hyp:path), and
[the epoch index](hyp:t), this establishes
[the decode segment take hist state view result](goal). -/
-- @node: decodeSegment_take_histStateView
lemma decodeSegment_take_histStateView {n nX nH : Nat}
    (fallback s : JointState nX nH)
    (path : List (Bool × ℝ × JointState nX nH)) (t : Fin n) :
    histStateView t (decodeSegment fallback (s, path.take (t.val + 1))) =
      histStateView t (decodeSegment fallback (s, path)) := by
  unfold histStateView
  apply Prod.ext
  · apply Prod.ext
    · funext j
      exact decodeSegment_take_curState_of_lt fallback s path (t.val + 1)
        (prefixIndex t j) (by dsimp [prefixIndex]; omega)
    · funext j
      apply Prod.ext
      · exact decodeSegment_take_actionAt_of_lt fallback s path (t.val + 1)
          (prefixIndex t j) (by dsimp [prefixIndex]; omega)
      · exact decodeSegment_take_rewardAt_of_lt fallback s path (t.val + 1)
          (prefixIndex t j) (by dsimp [prefixIndex]; omega)
  · exact decodeSegment_take_curState_of_lt fallback s path (t.val + 1) t (by omega)

/-- The state-history/action coordinate is determined by the first `t + 1` generated steps. For
[the sample size](hyp:n), [the observed-state count](hyp:nX), [the hidden-state count](hyp:nH),
[the fallback state](hyp:fallback), [the state](hyp:s), [the path](hyp:path), and
[the epoch index](hyp:t), this establishes
[the decode segment take hist action pair result](goal). -/
-- @node: decodeSegment_take_histActionPair
lemma decodeSegment_take_histActionPair {n nX nH : Nat}
    (fallback s : JointState nX nH)
    (path : List (Bool × ℝ × JointState nX nH)) (t : Fin n) :
    histActionPair t (decodeSegment fallback (s, path.take (t.val + 1))) =
      histActionPair t (decodeSegment fallback (s, path)) := by
  apply Prod.ext
  · exact decodeSegment_take_histStateView fallback s path t
  · exact decodeSegment_take_actionAt_of_lt fallback s path (t.val + 1) t (by omega)

/-- The state-history/action/reward-successor coordinate is determined by the first `t + 1`
generated steps. For [the sample size](hyp:n), [the observed-state count](hyp:nX),
[the hidden-state count](hyp:nH), [the fallback state](hyp:fallback), [the state](hyp:s),
[the path](hyp:path), and [the epoch index](hyp:t), this establishes
[the decode segment take hist next pair result](goal). -/
-- @node: decodeSegment_take_histNextPair
lemma decodeSegment_take_histNextPair {n nX nH : Nat}
    (fallback s : JointState nX nH)
    (path : List (Bool × ℝ × JointState nX nH)) (t : Fin n) :
    histNextPair t (decodeSegment fallback (s, path.take (t.val + 1))) =
      histNextPair t (decodeSegment fallback (s, path)) := by
  apply Prod.ext
  · exact decodeSegment_take_histActionPair fallback s path t
  · apply Prod.ext
    · exact decodeSegment_take_rewardAt_of_lt fallback s path (t.val + 1) t (by omega)
    · exact decodeSegment_take_nextState_of_lt fallback s path (t.val + 1) t (by omega)

end CausalSmith.Stat.PomdpPolicyclassRegret

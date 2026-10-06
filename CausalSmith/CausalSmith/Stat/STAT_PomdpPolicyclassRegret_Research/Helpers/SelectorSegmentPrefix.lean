module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.BlockSegmentMoments
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorSegmentSplit

/-!
# Prefix transport for structural selector segments

Truncating a decoded trajectory commutes with decoding a truncated generated
list.  Consequently, the structural law at a longer horizon has the expected
shorter structural law as its prefix marginal.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax

/-- Restrict a full trajectory to its first `k` epochs. -/
@[no_expose]
def segmentTrajectoryTake {k n nX nH : Nat} (hk : k ≤ n) :
    FullTrajectory n nX nH → FullTrajectory k nX nH := fun w ↦
  ((fun i ↦ w.1 (Fin.castLE (Nat.succ_le_succ hk) i)),
    fun t ↦ w.2 (Fin.castLE hk t))

/-- For [the history length](hyp:k), [the sample size](hyp:n),
[the observed-state count](hyp:nX), [the hidden-state count](hyp:nH), and
[the history length assumption](hyp:hk), this establishes
[the segment trajectory take measurability result](goal). -/
@[fun_prop]
-- @node: segmentTrajectoryTake_measurable
lemma segmentTrajectoryTake_measurable {k n nX nH : Nat} (hk : k ≤ n) :
    Measurable (segmentTrajectoryTake (nX := nX) (nH := nH) hk) := by
  unfold segmentTrajectoryTake
  fun_prop

/-- Decoding commutes pointwise with restriction to a shorter horizon. For
[the history length](hyp:k), [the sample size](hyp:n), [the observed-state count](hyp:nX),
[the hidden-state count](hyp:nH), [the history length assumption](hyp:hk),
[the fallback state](hyp:fallback), [the state](hyp:s), and [the path](hyp:path), this
establishes [the segment trajectory take decode segment result](goal). -/
-- @node: segmentTrajectoryTake_decodeSegment
lemma segmentTrajectoryTake_decodeSegment {k n nX nH : Nat} (hk : k ≤ n)
    (fallback s : JointState nX nH)
    (path : List (Bool × ℝ × JointState nX nH)) :
    segmentTrajectoryTake hk (decodeSegment (n := n) fallback (s, path)) =
      decodeSegment (n := k) fallback (s, path.take k) := by
  apply Prod.ext
  · funext i
    unfold segmentTrajectoryTake decodeSegment
    change (if i.val = 0 then s else
        (path.getD (i.val - 1) (false, 0, fallback)).2.2) =
      (if i.val = 0 then s else
        ((path.take k).getD (i.val - 1) (false, 0, fallback)).2.2)
    split_ifs with hi
    · rfl
    · have hik : i.val - 1 < k := by omega
      simp only [List.getD]
      rw [List.getElem?_take_of_lt hik]
  · funext t
    unfold segmentTrajectoryTake decodeSegment
    change ((path.getD t.val (false, 0, fallback)).1,
        (path.getD t.val (false, 0, fallback)).2.1) =
      (((path.take k).getD t.val (false, 0, fallback)).1,
        ((path.take k).getD t.val (false, 0, fallback)).2.1)
    simp only [List.getD]
    rw [List.getElem?_take_of_lt t.isLt]

/-- A state-history coordinate at `t` is unchanged after restricting the trajectory to the first
`t+1` epochs. For [the sample size](hyp:n), [the observed-state count](hyp:nX),
[the hidden-state count](hyp:nH), [the epoch index](hyp:t), and [the observed word](hyp:w), this
establishes [the hist state view segment trajectory take result](goal). -/
-- @node: histStateView_segmentTrajectoryTake
lemma histStateView_segmentTrajectoryTake {n nX nH : Nat} (t : Fin n)
    (w : FullTrajectory n nX nH) :
    histStateView (Fin.last t.val)
        (segmentTrajectoryTake (Nat.succ_le_iff.2 t.isLt) w) =
      histStateView t w := by
  unfold histStateView curState segmentTrajectoryTake prefixIndex
  apply Prod.ext
  · apply Prod.ext <;> funext j
    · apply congrArg w.1
      apply Fin.ext
      rfl
    · apply congrArg w.2
      apply Fin.ext
      rfl
  · apply congrArg w.1
    apply Fin.ext
    rfl

/-- The history-action coordinate is unchanged by restriction to its minimal supporting horizon.
For [the sample size](hyp:n), [the observed-state count](hyp:nX),
[the hidden-state count](hyp:nH), [the epoch index](hyp:t), and [the observed word](hyp:w), this
establishes [the hist action pair segment trajectory take result](goal). -/
-- @node: histActionPair_segmentTrajectoryTake
lemma histActionPair_segmentTrajectoryTake {n nX nH : Nat} (t : Fin n)
    (w : FullTrajectory n nX nH) :
    histActionPair (Fin.last t.val)
        (segmentTrajectoryTake (Nat.succ_le_iff.2 t.isLt) w) =
      histActionPair t w := by
  unfold histActionPair
  apply Prod.ext
  · exact histStateView_segmentTrajectoryTake t w
  · unfold actionAt segmentTrajectoryTake
    rfl

/-- The history-next-step coordinate is unchanged by restriction to its minimal supporting
horizon. For [the sample size](hyp:n), [the observed-state count](hyp:nX),
[the hidden-state count](hyp:nH), [the epoch index](hyp:t), and [the observed word](hyp:w), this
establishes [the hist next pair segment trajectory take result](goal). -/
-- @node: histNextPair_segmentTrajectoryTake
lemma histNextPair_segmentTrajectoryTake {n nX nH : Nat} (t : Fin n)
    (w : FullTrajectory n nX nH) :
    histNextPair (Fin.last t.val)
        (segmentTrajectoryTake (Nat.succ_le_iff.2 t.isLt) w) =
      histNextPair t w := by
  unfold histNextPair histView
  apply Prod.ext
  · exact histActionPair_segmentTrajectoryTake t w
  · apply Prod.ext
    · unfold rewardAt segmentTrajectoryTake
      rfl
    · unfold nextState segmentTrajectoryTake
      rfl

/-- The prefix marginal of a structural segment is the structural segment at that shorter
horizon. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the history length](hyp:k), [the sample size](hyp:n), [the model](hyp:m),
[the finite assumption](hyp:hFinite), [the behavior policy assumption](hyp:hb),
[the initial distribution](hyp:nu), and [the history length assumption](hyp:hk), this
establishes [the segment law map trajectory take result](goal). -/
-- @node: segmentLaw_map_trajectoryTake
lemma segmentLaw_map_trajectoryTake {T M k n : Nat} (m : ModelIndex T M)
    (hFinite : FiniteState m) (hb : PolicyVector m.Mx.b)
    (nu : JointState m.nX m.nH → ℝ) (hk : k ≤ n) :
    (segmentLaw m hFinite nu n).map (segmentTrajectoryTake hk) =
      segmentLaw m hFinite nu k := by
  let fallback : JointState m.nX m.nH :=
    (⟨0, hFinite.1⟩, ⟨0, hFinite.2⟩)
  rw [segmentLaw_eq_sum_fixed_start, segmentLaw_eq_sum_fixed_start,
    ← Measure.sum_fintype,
    Measure.map_sum (segmentTrajectoryTake_measurable hk).aemeasurable,
    Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro s _
  rw [Measure.map_smul,
    Measure.map_map (segmentTrajectoryTake_measurable hk) (by fun_prop)]
  have hcomp :
      segmentTrajectoryTake hk ∘
          (fun path ↦ decodeSegment (n := n) fallback (s, path)) =
        (fun path ↦ decodeSegment (n := k) fallback (s, path)) ∘
          (fun path ↦ path.take k) := by
    funext path
    exact segmentTrajectoryTake_decodeSegment hk fallback s path
  rw [hcomp, ← Measure.map_map (by fun_prop) (segment_list_take_measurable k),
    segmentFrom_map_take m hb n k hk s]

/-- The state-history marginal at an arbitrary epoch is the terminal state-history marginal of
the minimal prefix law. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the model](hyp:m), [the finite assumption](hyp:hFinite),
[the behavior policy assumption](hyp:hb), [the initial distribution](hyp:nu), and
[the epoch index](hyp:t), this establishes
[the segment law map hist state view equality prefix result](goal). -/
-- @node: segmentLaw_map_histStateView_eq_prefix
lemma segmentLaw_map_histStateView_eq_prefix {T M : Nat} (m : ModelIndex T M)
    (hFinite : FiniteState m) (hb : PolicyVector m.Mx.b)
    (nu : JointState m.nX m.nH → ℝ) (t : Fin T) :
    (segmentLaw m hFinite nu T).map (histStateView t) =
      (segmentLaw m hFinite nu (t.val + 1)).map
        (histStateView (Fin.last t.val)) := by
  let ht : t.val + 1 ≤ T := Nat.succ_le_iff.2 t.isLt
  have htake := segmentLaw_map_trajectoryTake m hFinite hb nu ht
  rw [← htake, Measure.map_map (by unfold histStateView curState prefixIndex; fun_prop)
    (segmentTrajectoryTake_measurable ht)]
  apply Measure.map_congr
  filter_upwards [] with w
  exact (histStateView_segmentTrajectoryTake t w).symm

/-- The history-action marginal at an arbitrary epoch is the terminal history-action marginal of
the minimal prefix law. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the model](hyp:m), [the finite assumption](hyp:hFinite),
[the behavior policy assumption](hyp:hb), [the initial distribution](hyp:nu), and
[the epoch index](hyp:t), this establishes
[the segment law map hist action pair equality prefix result](goal). -/
-- @node: segmentLaw_map_histActionPair_eq_prefix
lemma segmentLaw_map_histActionPair_eq_prefix {T M : Nat} (m : ModelIndex T M)
    (hFinite : FiniteState m) (hb : PolicyVector m.Mx.b)
    (nu : JointState m.nX m.nH → ℝ) (t : Fin T) :
    (segmentLaw m hFinite nu T).map (histActionPair t) =
      (segmentLaw m hFinite nu (t.val + 1)).map
        (histActionPair (Fin.last t.val)) := by
  let ht : t.val + 1 ≤ T := Nat.succ_le_iff.2 t.isLt
  have htake := segmentLaw_map_trajectoryTake m hFinite hb nu ht
  rw [← htake, Measure.map_map (by
      unfold histActionPair histStateView curState actionAt prefixIndex
      fun_prop) (segmentTrajectoryTake_measurable ht)]
  apply Measure.map_congr
  filter_upwards [] with w
  exact (histActionPair_segmentTrajectoryTake t w).symm

/-- The history-next-step marginal at an arbitrary epoch is the terminal history-next-step
marginal of the minimal prefix law. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m), [the finite assumption](hyp:hFinite),
[the behavior policy assumption](hyp:hb), [the initial distribution](hyp:nu), and
[the epoch index](hyp:t), this establishes
[the segment law map hist next pair equality prefix result](goal). -/
-- @node: segmentLaw_map_histNextPair_eq_prefix
lemma segmentLaw_map_histNextPair_eq_prefix {T M : Nat} (m : ModelIndex T M)
    (hFinite : FiniteState m) (hb : PolicyVector m.Mx.b)
    (nu : JointState m.nX m.nH → ℝ) (t : Fin T) :
    (segmentLaw m hFinite nu T).map (histNextPair t) =
      (segmentLaw m hFinite nu (t.val + 1)).map
        (histNextPair (Fin.last t.val)) := by
  let ht : t.val + 1 ≤ T := Nat.succ_le_iff.2 t.isLt
  have htake := segmentLaw_map_trajectoryTake m hFinite hb nu ht
  rw [← htake, Measure.map_map (by
      unfold histNextPair histView histActionPair histStateView curState
        actionAt rewardAt nextState prefixIndex
      fun_prop) (segmentTrajectoryTake_measurable ht)]
  apply Measure.map_congr
  filter_upwards [] with w
  exact (histNextPair_segmentTrajectoryTake t w).symm

end CausalSmith.Stat.PomdpPolicyclassRegret

module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.BlockPathMeans
public import Mathlib.Data.List.GetD

/-!
# Decoding chronological PHIW windows

These identities connect the structural path functionals to the coordinate
windows used by the observable estimator. Padding disappears on valid indices;
reward clipping disappears on the kernel's unit reward support.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators ENNReal

/-- State before an epoch of a generated list, including its initial state. -/
-- @node: phiwPathState
def phiwPathState {S : Type*} (fallback s : S)
    (path : List (Bool × ℝ × S)) (i : Nat) : S :=
  if i = 0 then s else (path.getD (i - 1) (false, 0, fallback)).2.2

/-- Padding choices agree when the coordinate is present. For [the first event](hyp:A),
[the path](hyp:path), [the i](hyp:i), [the i assumption](hyp:hi), [the action](hyp:a), and
[the behavior policy](hyp:b), this establishes
[the partial-history importance-weighted get d default irrel result](goal). -/
-- @node: phiw_getD_default_irrel
lemma phiw_getD_default_irrel {A : Type*} (path : List A) (i : Nat)
    (hi : i < path.length) (a b : A) : path.getD i a = path.getD i b := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi]

/-- Removing the first step shifts every valid full-state coordinate. For
[the index subset](hyp:S), [the fallback state](hyp:fallback), [the state](hyp:s),
[the step](hyp:step), [the tail](hyp:tail), and [the i](hyp:i), this establishes
[the partial-history importance-weighted path state cons succ result](goal). -/
-- @node: phiwPathState_cons_succ
lemma phiwPathState_cons_succ {S : Type*} (fallback s : S)
    (step : Bool × ℝ × S) (tail : List (Bool × ℝ × S)) (i : Nat) :
    phiwPathState fallback s (step :: tail) (i + 1) =
      phiwPathState fallback step.2.2 tail i := by
  cases i <;> simp [phiwPathState]

/-- A shifted path functional evaluates at the decoded state and suffix. The prefix must be
present; no distributional assumption is used. For [the index subset](hyp:S), [the f](hyp:f),
[the fallback state](hyp:fallback), [the state](hyp:s), [the path](hyp:path),
[the reward symbol](hyp:r), and [the reward symbol assumption](hyp:hr), this establishes
[the partial-history importance-weighted path shift equality suffix result](goal). -/
-- @node: phiwPathShift_eq_suffix
lemma phiwPathShift_eq_suffix {S : Type*}
    (f : S → List (Bool × ℝ × S) → ℝ) (fallback s : S)
    (path : List (Bool × ℝ × S)) (r : Nat) (hr : r ≤ path.length) :
    phiwPathShift f r s path =
      f (phiwPathState fallback s path r) (path.drop r) := by
  induction r generalizing s path with
  | zero => simp [phiwPathShift, phiwPathState]
  | succ r ih =>
    cases path with
    | nil => simp at hr
    | cons step tail =>
      simp only [phiwPathShift, List.getD_cons_zero, List.drop_succ_cons,
        List.drop_zero]
      rw [ih step.2.2 tail (by simpa using hr)]
      rw [phiwPathState_cons_succ]

/-- A chronological weighted reward is the product of its coordinate ratios and the clipped
terminal reward. All coordinates used are present. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m), [the candidate index](hyp:j),
[the fallback state](hyp:fallback), [the state](hyp:s), [the path](hyp:path),
[the history length](hyp:k), and [the history length assumption](hyp:hk), this establishes
[the partial-history importance-weighted path reward equality coordinate product result](goal). -/
-- @node: phiwPathReward_eq_coordinate_product
lemma phiwPathReward_eq_coordinate_product {T M : Nat} (m : ModelIndex T M)
    (j : Fin M) (fallback s : JointState m.nX m.nH)
    (path : List (Bool × ℝ × JointState m.nX m.nH))
    (k : Nat) (hk : k < path.length) :
    phiwPathReward m j k s path =
      (∏ i ∈ Finset.range (k + 1),
        ratio m.Mx.b (m.Mx.E j) (phiwPathState fallback s path i).1
          (path.getD i (false, 0, fallback)).1) *
      clipUnit01 (path.getD k (false, 0, fallback)).2.1 := by
  induction k generalizing s path with
  | zero =>
    cases path with
    | nil => simp at hk
    | cons step tail => simp [phiwPathReward, phiwPathState]
  | succ k ih =>
    cases path with
    | nil => simp at hk
    | cons step tail =>
      simp only [phiwPathReward, List.getD_cons_zero, List.drop_succ_cons,
        List.drop_zero]
      rw [ih step.2.2 tail (by simpa using hk)]
      conv_rhs => rw [Finset.prod_range_succ']
      simp only [phiwPathState_cons_succ, List.getD_cons_succ]
      rw [show phiwPathState fallback s (step :: tail) 0 = s from rfl,
        List.getD_cons_zero]
      ring

/-- Decoded state coordinates commute with removing a prefix. For [the index subset](hyp:S),
[the fallback state](hyp:fallback), [the state](hyp:s), [the path](hyp:path),
[the reward symbol](hyp:r), and [the i](hyp:i), this establishes
[the partial-history importance-weighted path state drop result](goal). -/
-- @node: phiwPathState_drop
lemma phiwPathState_drop {S : Type*} (fallback s : S)
    (path : List (Bool × ℝ × S)) (r i : Nat) :
    phiwPathState fallback (phiwPathState fallback s path r) (path.drop r) i =
      phiwPathState fallback s path (r + i) := by
  cases i with
  | zero => simp [phiwPathState]
  | succ i => simp [phiwPathState, List.getD]

/-- A shifted reward uses exactly the ratios on its contiguous interval. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the model](hyp:m),
[the candidate index](hyp:j), [the fallback state](hyp:fallback), [the state](hyp:s),
[the path](hyp:path), [the reward symbol](hyp:r), [the history length](hyp:k), and
[the history length assumption](hyp:hk), this establishes
[the partial-history importance-weighted path shift reward equality coordinate product result](goal). -/
-- @node: phiwPathShift_reward_eq_coordinate_product
lemma phiwPathShift_reward_eq_coordinate_product {T M : Nat} (m : ModelIndex T M)
    (j : Fin M) (fallback s : JointState m.nX m.nH)
    (path : List (Bool × ℝ × JointState m.nX m.nH))
    (r k : Nat) (hk : r + k < path.length) :
    phiwPathShift (phiwPathReward m j k) r s path =
      (∏ i ∈ Finset.range (k + 1),
        ratio m.Mx.b (m.Mx.E j) (phiwPathState fallback s path (r + i)).1
          (path.getD (r + i) (false, 0, fallback)).1) *
      clipUnit01 (path.getD (r + k) (false, 0, fallback)).2.1 := by
  rw [phiwPathShift_eq_suffix _ fallback s path r (by omega),
    phiwPathReward_eq_coordinate_product m j fallback _ _ k
      (by simp only [List.length_drop]; omega)]
  simp only [phiwPathState_drop, List.getD, List.getElem?_drop]

/-- The subtraction-based window predicate enumerates the chronological ratios at offsets zero
through the chosen history depth. For [the sample size](hyp:n),
[the observed-state count](hyp:nX), [the hidden-state count](hyp:nH),
[the fallback state](hyp:fallback), [the state](hyp:s), [the path](hyp:path),
[the behavior policy](hyp:b), [the target policy](hyp:e), [the reward symbol](hyp:r),
[the history length](hyp:k), and [the epoch index assumption](hyp:ht), this establishes
[the partial-history importance-weighted decoded window product result](goal). -/
-- @node: phiw_decoded_window_product
lemma phiw_decoded_window_product {n nX nH : Nat} (fallback s : JointState nX nH)
    (path : List (Bool × ℝ × JointState nX nH)) (b e : Policy nX)
    (r k : Nat) (ht : r + k < n) :
    (∏ u ∈ Finset.univ.filter
        (fun u : Fin n ↦ u.val ≤ r + k ∧ r + k - u.val ≤ k),
      ratio b e (obsProj (decodeSegment (n := n) fallback (s, path)) u).1
        (obsProj (decodeSegment (n := n) fallback (s, path)) u).2.1) =
      ∏ i ∈ Finset.range (k + 1),
        ratio b e (phiwPathState fallback s path (r + i)).1
          (path.getD (r + i) (false, 0, fallback)).1 := by
  classical
  symm
  apply Finset.prod_bij (fun i hi ↦ (⟨r + i, by
    have := Finset.mem_range.mp hi
    omega⟩ : Fin n))
  · intro i hi
    have := Finset.mem_range.mp hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by omega, by omega⟩
  · intro i _ j _ hij
    have hv := congrArg Fin.val hij
    dsimp at hv
    omega
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    refine ⟨u.val - r, Finset.mem_range.mpr (by omega), ?_⟩
    apply Fin.ext
    dsimp
    omega
  · intro i _
    rfl

/-- A supported terminal reward makes the decoded observable score equal to the structural
window functional. No reward-successor independence is used. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the sample size](hyp:n), [the model](hyp:m),
[the candidate index](hyp:j), [the fallback state](hyp:fallback), [the state](hyp:s),
[the path](hyp:path), [the reward symbol](hyp:r), [the history length](hyp:k),
[the epoch index assumption](hyp:ht), [the len assumption](hyp:hlen), and
[the y assumption](hyp:hy), this establishes
[the partial-history importance-weighted score decode segment equality path reward result](goal). -/
-- @node: phiwScore_decodeSegment_eq_path_reward
lemma phiwScore_decodeSegment_eq_path_reward {T M n : Nat} (m : ModelIndex T M)
    (j : Fin M) (fallback s : JointState m.nX m.nH)
    (path : List (Bool × ℝ × JointState m.nX m.nH)) (r k : Nat)
    (ht : r + k < n) (hlen : path.length = n)
    (hy : (path.getD (r + k) (false, 0, fallback)).2.1 ∈ Set.Icc (0 : ℝ) 1) :
    phiwScore k m.Mx.b (m.Mx.E j)
      (obsProj (decodeSegment (n := n) fallback (s, path))) ⟨r + k, ht⟩ =
      phiwPathShift (phiwPathReward m j k) r s path := by
  rw [phiwPathShift_reward_eq_coordinate_product m j fallback s path r k
    (by omega)]
  unfold phiwScore
  rw [phiw_decoded_window_product fallback s path m.Mx.b (m.Mx.E j) r k ht]
  change (path.getD (r + k) (false, 0, fallback)).2.1 * _ = _
  rw [show clipUnit01 (path.getD (r + k) (false, 0, fallback)).2.1 =
    (path.getD (r + k) (false, 0, fallback)).2.1 by
      rw [clipUnit01, min_eq_right hy.2, max_eq_right hy.1]]
  exact mul_comm _ _

end CausalSmith.Stat.PomdpPolicyclassRegret

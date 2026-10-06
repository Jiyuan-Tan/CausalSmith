module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorSegmentEndpoint
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorSegmentSplit
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorTrajectoryBridge

/-!
# Past-event bounds for whole structural segments

Iterating the structural joint-step recursion transports a uniform future
segment bound through any measurable prefix event. Rewards and successor
states are integrated jointly throughout this argument.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped ENNReal

/-- A uniform future-segment probability bound holds after every measurable prefix event, with
its probability as a multiplicative factor. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m),
[the behavior policy assumption](hyp:hb), [the action](hyp:a), [the sample size](hyp:n),
[the fallback state](hyp:fallback), [the state](hyp:s), [the past](hyp:past),
[the bad](hyp:bad), [the past assumption](hyp:hpast), [the bad assumption](hyp:hbad),
[the q](hyp:q), and [the q assumption](hyp:hq), this establishes
[the segment from past future bound result](goal). -/
-- @node: segmentFrom_past_future_le
lemma segmentFrom_past_future_le {T M : Nat} (m : ModelIndex T M)
    (hb : PolicyVector m.Mx.b) (a n : Nat)
    (fallback : Bool × ℝ × JointState m.nX m.nH)
    (s : JointState m.nX m.nH)
    (past : Set (List (Bool × ℝ × JointState m.nX m.nH)))
    (bad : Set (JointState m.nX m.nH ×
      List (Bool × ℝ × JointState m.nX m.nH)))
    (hpast : MeasurableSet past) (hbad : MeasurableSet bad)
    (q : ℝ≥0∞)
    (hq : ∀ s', (segmentFrom m n s') {xs | (s', xs) ∈ bad} ≤ q) :
    (segmentFrom m (a + n) s)
      {xs | xs.take a ∈ past ∧
        (segmentPathEnd a fallback s xs, xs.drop a) ∈ bad} ≤
      q * (segmentFrom m (a + n) s) {xs | xs.take a ∈ past} := by
  induction a generalizing s past with
  | zero =>
    letI : IsProbabilityMeasure (segmentFrom m n s) := segmentFrom_isProbability m hb n s
    by_cases hp : [] ∈ past
    · simpa only [Nat.zero_add, List.take_zero, List.drop_zero,
        segmentPathEnd, hp, true_and, Set.setOf_true, measure_univ, mul_one] using hq s
    · simp [hp]
  | succ a ih =>
    have hE : MeasurableSet {xs : List (Bool × ℝ × JointState m.nX m.nH) |
        xs.take (a + 1) ∈ past ∧
          (segmentPathEnd (a + 1) fallback s xs, xs.drop (a + 1)) ∈ bad} :=
      (segment_list_take_measurable (a + 1) hpast).inter
        ((((segmentPathEnd_measurable (a + 1) fallback).comp
          ((measurable_const (a := s)).prodMk measurable_id)).prodMk
            (segment_list_drop_measurable (a + 1))) hbad)
    have hP : MeasurableSet {xs : List (Bool × ℝ × JointState m.nX m.nH) |
        xs.take (a + 1) ∈ past} := segment_list_take_measurable (a + 1) hpast
    rw [show a + 1 + n = (a + n) + 1 by omega, segmentFrom,
      Measure.bind_apply hE (segmentFrom_cons_family_measurable m hb (a + n)).aemeasurable,
      Measure.bind_apply hP (segmentFrom_cons_family_measurable m hb (a + n)).aemeasurable]
    calc
      _ ≤ ∫⁻ step, q * ((segmentFrom m (a + n) step.2.2).map
          (fun tail ↦ step :: tail)) {xs | xs.take (a + 1) ∈ past}
          ∂segmentStepLaw m s := by
        apply lintegral_mono
        intro step
        have hcons : Measurable (fun tail : List (Bool × ℝ × JointState m.nX m.nH) ↦
            step :: tail) := segment_list_cons_measurable.comp (measurable_prodMk_left (x := step))
        dsimp only
        rw [Measure.map_apply hcons hE, Measure.map_apply hcons hP]
        simpa only [Set.preimage_setOf_eq, Set.mem_setOf_eq, List.take_succ_cons, List.drop_succ_cons,
          segmentPathEnd_cons] using
          ih step.2.2 {tail | step :: tail ∈ past} (hcons hpast)
      _ = _ := by
        simpa only [Function.comp_apply] using
          lintegral_const_mul q ((Measure.measurable_coe hP).comp
            (segmentFrom_cons_family_measurable m hb (a + n)))

/-- A positive-horizon endpoint is the successor in the last padded step. For
[the index subset](hyp:S), [the action](hyp:a), [the fallback state](hyp:fallback),
[the state](hyp:s), and [the xs](hyp:xs), this establishes
[the segment path end succ equality get d result](goal). -/
-- @node: segmentPathEnd_succ_eq_getD
lemma segmentPathEnd_succ_eq_getD {S : Type*} (a : Nat)
    (fallback : Bool × ℝ × S) (s : S) (xs : List (Bool × ℝ × S)) :
    segmentPathEnd (a + 1) fallback s xs = (xs.getD a fallback).2.2 := by
  induction a generalizing s xs with
  | zero => rfl
  | succ a ih =>
    rw [segmentPathEnd, ih]
    simp [List.getD, List.getElem?_drop, Nat.add_comm]

/-- A point-start decoded segment is the structural law with a point-mass initial probability
vector. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the sample size](hyp:n), [the model](hyp:m), [the finite assumption](hyp:hFinite), and
[the state](hyp:s), this establishes [the segment law point equality fixed start result](goal). -/
-- @node: segmentLaw_point_eq_fixed_start
lemma segmentLaw_point_eq_fixed_start {T M n : Nat} (m : ModelIndex T M)
    (hFinite : FiniteState m) (s : JointState m.nX m.nH) :
    segmentLaw m hFinite (fun s' ↦ if s' = s then 1 else 0) n =
      (segmentFrom m n s).map (fun xs ↦ decodeSegment (n := n)
        (⟨0, hFinite.1⟩, ⟨0, hFinite.2⟩) (s, xs)) := by
  classical
  rw [segmentLaw_eq_sum_fixed_start, Finset.sum_eq_single s]
  · rw [if_pos rfl, ENNReal.ofReal_one, one_smul]
  · intro s' _ hne
    rw [if_neg hne, ENNReal.ofReal_zero, zero_smul]
  · simp

/-- The arbitrary-start whole-block tail estimate applies directly to a fixed-start structural
list, after decoding and observation. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the sample size](hyp:n), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), [the history length](hyp:k),
[the history length assumption](hyp:hk), [the sample size assumption](hyp:hn),
[the state](hyp:s), [the observed state](hyp:x), and [the observed state assumption](hyp:hx),
this establishes [the selector fixed start block chebyshev result](goal). -/
-- @node: selector_fixed_start_block_chebyshev
lemma selector_fixed_start_block_chebyshev {T M n : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (j : Fin M) (k : Nat) (hk : 2 * k ≤ n) (hn : 4 ≤ n)
    (s : JointState m.nX m.nH) (x : ℝ) (hx : 0 < x) :
    (segmentFrom m n s) {xs | mixingAlpha t0 ^ k *
      (overlapRadius C + 1 / ((n - k : Nat) * (1 - mixingAlpha t0))) + x <
        |phiwRaw k m.Mx.b (m.Mx.E j)
          (obsProj (decodeSegment (n := n)
            (⟨0, hClass.finite_state.1⟩, ⟨0, hClass.finite_state.2⟩) (s, xs))) -
              policyValue m j|} ≤
      ENNReal.ofReal (((1 + 2 / (policyFactor zeta - 1) +
        4 / (1 - mixingAlpha t0)) * policyFactor zeta ^ (k + 1) /
          (n - k : Nat)) / x ^ 2) := by
  have htail := selector_block_chebyshev t0 zeta C m hClass
    hClass.t0_pos hClass.zeta_pos j k hk hn
    (fun s' ↦ if s' = s then 1 else 0) (selector_point_probabilityVector s) x hx
  have hraw : Measurable (phiwRaw (T := n) k m.Mx.b (m.Mx.E j)) := by
    unfold phiwRaw
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro t ht
    exact phiwScore_measurable k m.Mx.b (m.Mx.E j) t
  have hbad : MeasurableSet {w : ObsView n m.nX | mixingAlpha t0 ^ k *
      (overlapRadius C + 1 / ((n - k : Nat) * (1 - mixingAlpha t0))) + x <
        |phiwRaw k m.Mx.b (m.Mx.E j) w - policyValue m j|} :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (hraw.sub_const _))
  rw [segmentLaw_point_eq_fixed_start, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_apply (by fun_prop) hbad] at htail
  exact htail

/-- A decoded finite segment is unchanged by discarding list coordinates beyond its horizon. For
[the sample size](hyp:n), [the observed-state count](hyp:nX), [the hidden-state count](hyp:nH),
[the fallback state](hyp:fallback), [the state](hyp:s), and [the xs](hyp:xs), this establishes
[the decode segment take self result](goal). -/
-- @node: decodeSegment_take_self
lemma decodeSegment_take_self {n nX nH : Nat}
    (fallback s : JointState nX nH)
    (xs : List (Bool × ℝ × JointState nX nH)) :
    decodeSegment (n := n) fallback (s, xs.take n) =
      decodeSegment (n := n) fallback (s, xs) := by
  apply Prod.ext
  · funext i
    simp only [decodeSegment, Prod.fst]
    split_ifs with hi
    · rfl
    · simp [List.getD, show i.val - 1 < n by omega]
  · funext t
    simp [decodeSegment, List.getD, t.isLt]

/-- Additional future epochs do not change a fixed-start block's tail bound; the prefix marginal
is the exact structural block law. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the sample size](hyp:n), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), [the history length](hyp:k),
[the history length assumption](hyp:hk), [the sample size assumption](hyp:hn),
[the extra](hyp:extra), [the state](hyp:s), [the observed state](hyp:x), and
[the observed state assumption](hyp:hx), this establishes
[the selector fixed start block chebyshev extended result](goal). -/
-- @node: selector_fixed_start_block_chebyshev_extended
lemma selector_fixed_start_block_chebyshev_extended {T M n : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (j : Fin M) (k : Nat) (hk : 2 * k ≤ n) (hn : 4 ≤ n)
    (extra : Nat) (s : JointState m.nX m.nH) (x : ℝ) (hx : 0 < x) :
    (segmentFrom m (n + extra) s) {xs | mixingAlpha t0 ^ k *
      (overlapRadius C + 1 / ((n - k : Nat) * (1 - mixingAlpha t0))) + x <
        |phiwRaw k m.Mx.b (m.Mx.E j)
          (obsProj (decodeSegment (n := n)
            (⟨0, hClass.finite_state.1⟩, ⟨0, hClass.finite_state.2⟩) (s, xs))) -
              policyValue m j|} ≤
      ENNReal.ofReal (((1 + 2 / (policyFactor zeta - 1) +
        4 / (1 - mixingAlpha t0)) * policyFactor zeta ^ (k + 1) /
          (n - k : Nat)) / x ^ 2) := by
  have htail := selector_fixed_start_block_chebyshev t0 zeta C m hClass j k hk hn s x hx
  have hraw : Measurable (phiwRaw (T := n) k m.Mx.b (m.Mx.E j)) := by
    unfold phiwRaw
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro t ht
    exact phiwScore_measurable k m.Mx.b (m.Mx.E j) t
  have hbad : MeasurableSet {xs : List (Bool × ℝ × JointState m.nX m.nH) |
      mixingAlpha t0 ^ k *
        (overlapRadius C + 1 / ((n - k : Nat) * (1 - mixingAlpha t0))) + x <
          |phiwRaw k m.Mx.b (m.Mx.E j)
            (obsProj (decodeSegment (n := n)
              (⟨0, hClass.finite_state.1⟩, ⟨0, hClass.finite_state.2⟩) (s, xs))) -
                policyValue m j|} := by
    apply measurableSet_lt measurable_const
    exact continuous_abs.measurable.comp
      ((hraw.comp (phiw_obsProj_measurable.comp ((decodeSegment_measurable _).comp
        (measurable_prodMk_left (x := s))))).sub_const _)
  rw [← segmentFrom_map_take m hClass.sequential_ignorability.1 (n + extra) n
    (by omega) s, Measure.map_apply (segment_list_take_measurable n) hbad] at htail
  simpa only [Set.preimage_setOf_eq, decodeSegment_take_self] using htail

/-- Equation (10) on the structural path: any measurable past event before an entire future
block multiplies its arbitrary-start Chebyshev tail. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the sample size](hyp:n), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the action](hyp:a), [the state](hyp:s),
[the past](hyp:past), [the past assumption](hyp:hpast), [the candidate index](hyp:j),
[the history length](hyp:k), [the history length assumption](hyp:hk),
[the sample size assumption](hyp:hn), [the observed state](hyp:x), and
[the observed state assumption](hyp:hx), this establishes
[the selector structural block chebyshev past result](goal). -/
-- @node: selector_structural_block_chebyshev_past
lemma selector_structural_block_chebyshev_past {T M n : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (a : Nat) (s : JointState m.nX m.nH)
    (past : Set (List (Bool × ℝ × JointState m.nX m.nH)))
    (hpast : MeasurableSet past) (j : Fin M) (k : Nat)
    (hk : 2 * k ≤ n) (hn : 4 ≤ n) (x : ℝ) (hx : 0 < x) :
    (segmentFrom m (a + n) s) {xs | xs.take a ∈ past ∧
      mixingAlpha t0 ^ k *
        (overlapRadius C + 1 / ((n - k : Nat) * (1 - mixingAlpha t0))) + x <
          |phiwRaw k m.Mx.b (m.Mx.E j)
            (obsProj (decodeSegment (n := n)
              (⟨0, hClass.finite_state.1⟩, ⟨0, hClass.finite_state.2⟩)
              (segmentPathEnd a
                (false, 0, (⟨0, hClass.finite_state.1⟩, ⟨0, hClass.finite_state.2⟩))
                s xs, xs.drop a))) - policyValue m j|} ≤
      ENNReal.ofReal (((1 + 2 / (policyFactor zeta - 1) +
        4 / (1 - mixingAlpha t0)) * policyFactor zeta ^ (k + 1) /
          (n - k : Nat)) / x ^ 2) *
            (segmentFrom m (a + n) s) {xs | xs.take a ∈ past} := by
  let bad : Set (JointState m.nX m.nH ×
      List (Bool × ℝ × JointState m.nX m.nH)) := {p |
    mixingAlpha t0 ^ k *
      (overlapRadius C + 1 / ((n - k : Nat) * (1 - mixingAlpha t0))) + x <
        |phiwRaw k m.Mx.b (m.Mx.E j)
          (obsProj (decodeSegment (n := n)
            (⟨0, hClass.finite_state.1⟩, ⟨0, hClass.finite_state.2⟩) p)) - policyValue m j|}
  have hraw : Measurable (phiwRaw (T := n) k m.Mx.b (m.Mx.E j)) := by
    unfold phiwRaw
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro t ht
    exact phiwScore_measurable k m.Mx.b (m.Mx.E j) t
  have hbad : MeasurableSet bad := by
    apply measurableSet_lt measurable_const
    exact continuous_abs.measurable.comp
      ((hraw.comp (phiw_obsProj_measurable.comp (decodeSegment_measurable _))).sub_const _)
  apply segmentFrom_past_future_le m hClass.sequential_ignorability.1 a n
    (false, 0, (⟨0, hClass.finite_state.1⟩, ⟨0, hClass.finite_state.2⟩))
    s past bad hpast hbad
  intro s'
  exact selector_fixed_start_block_chebyshev t0 zeta C m hClass j k hk hn s' x hx

/-- The structural past-event block bound also holds inside a longer path; all epochs after the
tested block are integrated out. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the sample size](hyp:n), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the action](hyp:a), [the extra](hyp:extra),
[the state](hyp:s), [the past](hyp:past), [the past assumption](hyp:hpast),
[the candidate index](hyp:j), [the history length](hyp:k),
[the history length assumption](hyp:hk), [the sample size assumption](hyp:hn),
[the observed state](hyp:x), and [the observed state assumption](hyp:hx), this establishes
[the selector structural block chebyshev past extended result](goal). -/
-- @node: selector_structural_block_chebyshev_past_extended
lemma selector_structural_block_chebyshev_past_extended {T M n : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (a extra : Nat) (s : JointState m.nX m.nH)
    (past : Set (List (Bool × ℝ × JointState m.nX m.nH)))
    (hpast : MeasurableSet past) (j : Fin M) (k : Nat)
    (hk : 2 * k ≤ n) (hn : 4 ≤ n) (x : ℝ) (hx : 0 < x) :
    (segmentFrom m (a + (n + extra)) s) {xs | xs.take a ∈ past ∧
      mixingAlpha t0 ^ k *
        (overlapRadius C + 1 / ((n - k : Nat) * (1 - mixingAlpha t0))) + x <
          |phiwRaw k m.Mx.b (m.Mx.E j)
            (obsProj (decodeSegment (n := n)
              (⟨0, hClass.finite_state.1⟩, ⟨0, hClass.finite_state.2⟩)
              (segmentPathEnd a
                (false, 0, (⟨0, hClass.finite_state.1⟩, ⟨0, hClass.finite_state.2⟩))
                s xs, xs.drop a))) - policyValue m j|} ≤
      ENNReal.ofReal (((1 + 2 / (policyFactor zeta - 1) +
        4 / (1 - mixingAlpha t0)) * policyFactor zeta ^ (k + 1) /
          (n - k : Nat)) / x ^ 2) *
            (segmentFrom m (a + (n + extra)) s) {xs | xs.take a ∈ past} := by
  let bad : Set (JointState m.nX m.nH ×
      List (Bool × ℝ × JointState m.nX m.nH)) := {p |
    mixingAlpha t0 ^ k *
      (overlapRadius C + 1 / ((n - k : Nat) * (1 - mixingAlpha t0))) + x <
        |phiwRaw k m.Mx.b (m.Mx.E j)
          (obsProj (decodeSegment (n := n)
            (⟨0, hClass.finite_state.1⟩, ⟨0, hClass.finite_state.2⟩) p)) - policyValue m j|}
  have hraw : Measurable (phiwRaw (T := n) k m.Mx.b (m.Mx.E j)) := by
    unfold phiwRaw
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro t ht
    exact phiwScore_measurable k m.Mx.b (m.Mx.E j) t
  have hbad : MeasurableSet bad := by
    apply measurableSet_lt measurable_const
    exact continuous_abs.measurable.comp
      ((hraw.comp (phiw_obsProj_measurable.comp (decodeSegment_measurable _))).sub_const _)
  apply segmentFrom_past_future_le m hClass.sequential_ignorability.1 a (n + extra)
    (false, 0, (⟨0, hClass.finite_state.1⟩, ⟨0, hClass.finite_state.2⟩))
    s past bad hpast hbad
  intro s'
  exact selector_fixed_start_block_chebyshev_extended t0 zeta C m hClass j k hk hn extra s' x hx

end CausalSmith.Stat.PomdpPolicyclassRegret

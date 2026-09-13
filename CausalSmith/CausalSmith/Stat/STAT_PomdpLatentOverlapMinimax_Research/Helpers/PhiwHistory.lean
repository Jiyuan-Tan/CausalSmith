import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.Weights
import Mathlib.Probability.Moments.Variance

set_option linter.style.longLine false

/-! # Observable PHIW score moment substrate

This file isolates the pathwise and measure-theoretic bookkeeping used by the PHIW bias and
variance calculation.  The chronological likelihood-ratio cancellation itself requires a
history-marginal recursion; the lemmas below provide its measurable and integrable envelope.
-/

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- The full-to-observed trajectory projection is measurable. [the stated conclusion](goal). -/
lemma measurable_obsProj {T nX nH : Nat} :
    Measurable (@obsProj T nX nH) := by
  unfold obsProj curState actionAt rewardAt
  measurability

/-- The successor epoch associated with a nonterminal epoch. -/
def nextEpoch {T : Nat} (t : Fin T) (ht : t.val + 1 < T) : Fin T :=
  ⟨t.val + 1, ht⟩

/-- Appending the current action/reward and successor state turns the kernel-conditioning
carrier at `t` into the state-history carrier at `t+1`. -/
def succStateHistoryEquiv {T nX nH : Nat} (t : Fin T) (ht : t.val + 1 < T) :
    (ActionHistoryView T nX nH t × Step nX nH) ≃
      StateHistoryView T nX nH (nextEpoch t ht) where
  toFun z :=
    ((Fin.snoc z.1.1.1.1 z.1.1.2,
      Fin.snoc z.1.1.1.2 (z.1.2, z.2.1)), z.2.2)
  invFun h :=
    ((((Fin.init h.1.1, Fin.init h.1.2), h.1.1 (Fin.last t.val)),
      (h.1.2 (Fin.last t.val)).1),
      ((h.1.2 (Fin.last t.val)).2, h.2))
  left_inv z := by
    rcases z with ⟨⟨⟨⟨xs, ys⟩, s⟩, a⟩, r, s'⟩
    ext <;> simp [Fin.init, Fin.snoc]
  right_inv h := by
    rcases h with ⟨⟨xs, ys⟩, s⟩
    dsimp [nextEpoch] at xs ys ⊢
    apply Prod.ext
    · apply Prod.ext
      · exact Fin.snoc_init_self xs
      · exact Fin.snoc_init_self ys
    · rfl

/-- The successor-history equivalence is measurable in the forward direction. [the ht condition](hyp:ht). [the stated conclusion](goal). -/
lemma measurable_succStateHistoryEquiv {T nX nH : Nat} (t : Fin T)
    (ht : t.val + 1 < T) :
    Measurable (succStateHistoryEquiv (nX := nX) (nH := nH) t ht) := by
  change Measurable (fun z : ActionHistoryView T nX nH t × Step nX nH ↦
    ((@Fin.snoc t.val (fun _ ↦ JointState nX nH)
        (z.1.1.1.1 : Fin t.val → JointState nX nH) z.1.1.2,
      @Fin.snoc t.val (fun _ ↦ Bool × ℝ)
        (z.1.1.1.2 : Fin t.val → Bool × ℝ) (z.1.2, z.2.1)), z.2.2))
  measurability

/-- The successor-history equivalence is measurable in the reverse direction. [the ht condition](hyp:ht). [the stated conclusion](goal). -/
lemma measurable_succStateHistoryEquiv_symm {T nX nH : Nat} (t : Fin T)
    (ht : t.val + 1 < T) :
    Measurable (succStateHistoryEquiv (nX := nX) (nH := nH) t ht).symm := by
  change Measurable (fun h : StateHistoryView T nX nH (nextEpoch t ht) ↦
    ((((Fin.init h.1.1, Fin.init h.1.2), h.1.1 (Fin.last t.val)),
      (h.1.2 (Fin.last t.val)).1), ((h.1.2 (Fin.last t.val)).2, h.2)))
  fun_prop

/-- On full trajectories, appending the epoch-`t` kernel output is exactly the state history at
the successor epoch. [the ht condition](hyp:ht). [the stated conclusion](goal). -/
lemma succStateHistoryEquiv_histNextPair {T nX nH : Nat} (t : Fin T)
    (ht : t.val + 1 < T) (tau : FullTrajectory T nX nH) :
    succStateHistoryEquiv (nX := nX) (nH := nH) t ht (histNextPair t tau) =
      histStateView (nextEpoch t ht) tau := by
  change
    ((Fin.snoc (fun j ↦ curState (prefixIndex t j) tau) (curState t tau),
      Fin.snoc (fun j ↦ tau.2 (prefixIndex t j)) (actionAt t tau, rewardAt t tau)),
        nextState t tau) = histStateView (nextEpoch t ht) tau
  apply Prod.ext
  · apply Prod.ext
    · funext j
      refine Fin.lastCases ?_ (fun i ↦ ?_) j
      · simp [histStateView, nextEpoch, curState, prefixIndex]
        congr 1
      · simp [histStateView, nextEpoch, curState, prefixIndex]
    · funext j
      refine Fin.lastCases ?_ (fun i ↦ ?_) j
      · simp [histStateView, nextEpoch, rewardAt, actionAt, prefixIndex]
      · simp [histStateView, nextEpoch, rewardAt, actionAt, prefixIndex]
  · rfl

/-- The kernel-output and successor-state-history projections are measurable. [the stated conclusion](goal). -/
lemma measurable_histNextPair {T nX nH : Nat} (t : Fin T) :
    Measurable (@histNextPair T nX nH t) := by
  unfold histNextPair histView histActionPair histStateView curState actionAt rewardAt nextState
  measurability

/-- [the measurable hist State View assertion holds](goal). -/
lemma measurable_histStateView {T nX nH : Nat} (t : Fin T) :
    Measurable (@histStateView T nX nH t) := by
  unfold histStateView curState
  measurability

/-- [the measurable hist Action Pair assertion holds](goal). -/
lemma measurable_histActionPair {T nX nH : Nat} (t : Fin T) :
    Measurable (@histActionPair T nX nH t) := by
  unfold histActionPair
  exact (measurable_histStateView t).prodMk (by
    unfold actionAt
    measurability)

/-- Successor state-history marginals are the measurable-equivalence image of the preceding
kernel-output marginal. [the ht condition](hyp:ht). [the stated conclusion](goal). -/
lemma map_histStateView_next {T nX nH : Nat} (M : RawPomdpExperiment T nX nH)
    (t : Fin T) (ht : t.val + 1 < T) :
    M.law.map (histStateView (nextEpoch t ht)) =
      (M.law.map (histNextPair t)).map
        (succStateHistoryEquiv (nX := nX) (nH := nH) t ht) := by
  rw [Measure.map_map (measurable_succStateHistoryEquiv t ht)
    (measurable_histNextPair t)]
  apply Measure.map_congr
  filter_upwards with tau
  exact (succStateHistoryEquiv_histNextPair t ht tau).symm

/-- Product of ratios from epoch `lo` through the epoch immediately preceding `t`, represented
on the state-history carrier at `t`. -/
noncomputable def stateHistoryRatioBlock {T nX nH : Nat} (M : RawPomdpExperiment T nX nH)
    (lo : Nat) (t : Fin T) (h : StateHistoryView T nX nH t) : ℝ :=
  ∏ j : Fin t.val, if lo ≤ j.val then ratio M.b M.e (h.1.1 j).1 (h.1.2 j).1 else 1

/-- The same chronological block with the current action ratio appended. -/
noncomputable def actionHistoryRatioBlock {T nX nH : Nat} (M : RawPomdpExperiment T nX nH)
    (lo : Nat) (t : Fin T) (z : ActionHistoryView T nX nH t) : ℝ :=
  stateHistoryRatioBlock M lo t z.1 * ratio M.b M.e (currentObsState t z.1) z.2

/-- [the measurable state History Ratio Block assertion holds](goal). -/
lemma measurable_stateHistoryRatioBlock {T nX nH : Nat} (M : RawPomdpExperiment T nX nH)
    (lo : Nat) (t : Fin T) : Measurable (stateHistoryRatioBlock M lo t) := by
  classical
  unfold stateHistoryRatioBlock
  apply Finset.measurable_prod
  intro j _
  by_cases hj : lo ≤ j.val
  · simp only [hj, if_true]
    have hx : Measurable (fun h : StateHistoryView T nX nH t ↦ (h.1.1 j).1) :=
      measurable_fst.comp ((measurable_pi_apply j).comp (measurable_fst.comp measurable_fst))
    have ha : Measurable (fun h : StateHistoryView T nX nH t ↦ (h.1.2 j).1) :=
      measurable_fst.comp ((measurable_pi_apply j).comp (measurable_snd.comp measurable_fst))
    exact (measurable_of_finite (fun xa : Fin nX × Bool ↦ ratio M.b M.e xa.1 xa.2)).comp
      (hx.prodMk ha)
  · simp [hj]

/-- [the measurable action History Ratio Block assertion holds](goal). -/
lemma measurable_actionHistoryRatioBlock {T nX nH : Nat} (M : RawPomdpExperiment T nX nH)
    (lo : Nat) (t : Fin T) : Measurable (actionHistoryRatioBlock M lo t) := by
  unfold actionHistoryRatioBlock
  apply ((measurable_stateHistoryRatioBlock M lo t).comp measurable_fst).mul
  exact (measurable_of_finite (fun xa : Fin nX × Bool ↦ ratio M.b M.e xa.1 xa.2)).comp
    (((measurable_currentObsState t).comp measurable_fst).prodMk measurable_snd)

/-- Assuming [the hign condition](hyp:hign), [the hoverlap condition](hyp:hoverlap), [the h L condition](hyp:hL), [the state History Ratio Block mem Icc assertion holds](goal). -/
lemma stateHistoryRatioBlock_mem_Icc {T nX nH : Nat} {M : RawPomdpExperiment T nX nH}
    {L : ℝ} (hign : SequentialIgnorability M) (hoverlap : PolicyOverlap L M)
    (hL : 1 ≤ L) (lo : Nat) (t : Fin T) (h : StateHistoryView T nX nH t) :
    stateHistoryRatioBlock M lo t h ∈ Set.Icc 0 (L ^ t.val) := by
  unfold stateHistoryRatioBlock
  constructor
  · exact Finset.prod_nonneg fun j _ ↦ by
      split_ifs
      · exact (ratio_mem hign.1 hoverlap.1 hoverlap.2 (zero_le_one.trans hL) _ _).1
      · norm_num
  · calc
      _ ≤ ∏ _j : Fin t.val, L := by
        apply Finset.prod_le_prod
        · intro j _
          split_ifs
          · exact (ratio_mem hign.1 hoverlap.1 hoverlap.2 (zero_le_one.trans hL) _ _).1
          · norm_num
        · intro j _
          split_ifs
          · exact (ratio_mem hign.1 hoverlap.1 hoverlap.2 (zero_le_one.trans hL) _ _).2
          · exact hL
      _ = _ := by simp

/-- Assuming [the hign condition](hyp:hign), [the hoverlap condition](hyp:hoverlap), [the h L condition](hyp:hL), [the integrable state History Ratio Block assertion holds](goal). -/
lemma integrable_stateHistoryRatioBlock {T nX nH : Nat} {M : RawPomdpExperiment T nX nH}
    {L : ℝ} (hign : SequentialIgnorability M) (hoverlap : PolicyOverlap L M)
    (hL : 1 ≤ L) (lo : Nat) (t : Fin T) :
    Integrable (stateHistoryRatioBlock M lo t) (M.law.map (histStateView t)) := by
  letI : IsProbabilityMeasure (M.law.map (histStateView t)) :=
    Measure.isProbabilityMeasure_map (measurable_histStateView t).aemeasurable
  apply Integrable.of_bound (measurable_stateHistoryRatioBlock M lo t).aestronglyMeasurable
    (L ^ t.val)
  filter_upwards with h
  rw [Real.norm_eq_abs, abs_of_nonneg (stateHistoryRatioBlock_mem_Icc hign hoverlap hL lo t h).1]
  exact (stateHistoryRatioBlock_mem_Icc hign hoverlap hL lo t h).2

/-- Under the successor-history equivalence, the past block at `t+1` is exactly the block at
`t` with its current ratio appended. [the ht condition](hyp:ht); and [the hlo condition](hyp:hlo). [the stated conclusion](goal). -/
lemma stateHistoryRatioBlock_succEquiv {T nX nH : Nat}
    (M : RawPomdpExperiment T nX nH) (lo : Nat) (t : Fin T)
    (ht : t.val + 1 < T) (hlo : lo ≤ t.val)
    (q : ActionHistoryView T nX nH t × Step nX nH) :
    stateHistoryRatioBlock M lo (nextEpoch t ht)
        (succStateHistoryEquiv (nX := nX) (nH := nH) t ht q) =
      actionHistoryRatioBlock M lo t q.1 := by
  unfold stateHistoryRatioBlock actionHistoryRatioBlock
  change (∏ j : Fin (t.val + 1), if lo ≤ j.val then
      ratio M.b M.e
        ((@Fin.snoc t.val (fun _ ↦ JointState nX nH)
          q.1.1.1.1 q.1.1.2) j).1
        ((@Fin.snoc t.val (fun _ ↦ Bool × ℝ)
          q.1.1.1.2 (q.1.2, q.2.1)) j).1 else 1) = _
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_last, hlo, if_true]
  rfl

/-- A successor state-history ratio block integrates to the preceding action-history block.
The appended reward and next state form a probability-kernel fibre and hence disappear. [the hign condition](hyp:hign); and [the hoverlap condition](hyp:hoverlap); and [the h L condition](hyp:hL); and [the h K condition](hyp:hK); and [the ht condition](hyp:ht); and [the hlo condition](hyp:hlo). [the stated conclusion](goal). -/
lemma integral_stateHistoryRatioBlock_next {T nX nH : Nat}
    {M : RawPomdpExperiment T nX nH} {L : ℝ}
    (hign : SequentialIgnorability M) (hoverlap : PolicyOverlap L M)
    (hL : 1 ≤ L) (hK : PomdpKernelLaw M) (lo : Nat) (t : Fin T)
    (ht : t.val + 1 < T) (hlo : lo ≤ t.val) :
    ∫ h, stateHistoryRatioBlock M lo (nextEpoch t ht) h
        ∂(M.law.map (histStateView (nextEpoch t ht))) =
      ∫ z, actionHistoryRatioBlock M lo t z
        ∂(M.law.map (histActionPair t)) := by
  have hf : Integrable
      (fun q : ActionHistoryView T nX nH t × Step nX nH ↦
        stateHistoryRatioBlock M lo (nextEpoch t ht)
          (succStateHistoryEquiv (nX := nX) (nH := nH) t ht q))
      (M.law.map (histNextPair t)) := by
    have hs := integrable_stateHistoryRatioBlock hign hoverlap hL lo (nextEpoch t ht)
    rw [map_histStateView_next M t ht] at hs
    exact (integrable_map_measure
      (measurable_stateHistoryRatioBlock M lo (nextEpoch t ht)).aestronglyMeasurable
      (measurable_succStateHistoryEquiv t ht).aemeasurable).mp hs
  rw [map_histStateView_next M t ht,
    integral_map (measurable_succStateHistoryEquiv t ht).aemeasurable
      (measurable_stateHistoryRatioBlock M lo (nextEpoch t ht)).aestronglyMeasurable,
    integral_kernel_step hK t _ hf]
  apply integral_congr_ae
  filter_upwards with z
  haveI : IsProbabilityMeasure (M.K z.1.2 z.2) := hK.1 z.1.2 z.2
  simp_rw [stateHistoryRatioBlock_succEquiv M lo t ht hlo]
  simp

/-- If the block starts at or after the current epoch, its past-history part is empty. [the hlo condition](hyp:hlo). [the stated conclusion](goal). -/
lemma stateHistoryRatioBlock_eq_one_of_le {T nX nH : Nat}
    (M : RawPomdpExperiment T nX nH) (lo : Nat) (t : Fin T)
    (hlo : t.val ≤ lo) (h : StateHistoryView T nX nH t) :
    stateHistoryRatioBlock M lo t h = 1 := by
  unfold stateHistoryRatioBlock
  apply Finset.prod_eq_one
  intro j _
  simp only [ite_eq_right_iff]
  intro hloj
  omega

/-- Cancelling the current behavior action against its likelihood ratio leaves the unchanged
past ratio block. [the hign condition](hyp:hign); and [the hoverlap condition](hyp:hoverlap); and [the h L condition](hyp:hL). [the stated conclusion](goal). -/
lemma integral_actionHistoryRatioBlock_eq_state {T nX nH : Nat}
    {M : RawPomdpExperiment T nX nH} {L : ℝ}
    (hign : SequentialIgnorability M) (hoverlap : PolicyOverlap L M)
    (hL : 1 ≤ L) (lo : Nat) (t : Fin T) :
    ∫ z, actionHistoryRatioBlock M lo t z
        ∂(M.law.map (histActionPair t)) =
      ∫ h, stateHistoryRatioBlock M lo t h
        ∂(M.law.map (histStateView t)) := by
  have hf : Integrable
      (fun z : StateHistoryView T nX nH t × Bool ↦
        stateHistoryRatioBlock M lo t z.1)
      (M.law.map (histActionPair t)) := by
    letI : IsProbabilityMeasure (M.law.map (histActionPair t)) :=
      Measure.isProbabilityMeasure_map (measurable_histActionPair t).aemeasurable
    apply Integrable.of_bound
      ((measurable_stateHistoryRatioBlock M lo t).comp measurable_fst).aestronglyMeasurable
      (L ^ t.val)
    filter_upwards with z
    change |stateHistoryRatioBlock M lo t z.1| ≤ L ^ t.val
    rw [abs_of_nonneg
      (stateHistoryRatioBlock_mem_Icc hign hoverlap hL lo t z.1).1]
    exact (stateHistoryRatioBlock_mem_Icc hign hoverlap hL lo t z.1).2
  have h := integral_ratio_step hign hoverlap (zero_le_one.trans hL) t
    (fun z ↦ stateHistoryRatioBlock M lo t z.1) hf
  calc
    _ = ∫ z, ratio M.b M.e (currentObsState t z.1) z.2 *
          stateHistoryRatioBlock M lo t z.1
          ∂(M.law.map (histActionPair t)) := by
        apply integral_congr_ae
        filter_upwards with z
        simp [actionHistoryRatioBlock, mul_comm]
    _ = _ := h
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with z
      rw [← Finset.sum_mul]
      rw [(hoverlap.1 (currentObsState t z)).2]
      simp

/-- Every contiguous chronological likelihood-ratio block has behavior expectation one. [the hign condition](hyp:hign); and [the hoverlap condition](hyp:hoverlap); and [the h L condition](hyp:hL); and [the h K condition](hyp:hK). [the stated conclusion](goal). -/
lemma integral_actionHistoryRatioBlock_eq_one {T nX nH : Nat}
    {M : RawPomdpExperiment T nX nH} {L : ℝ}
    (hign : SequentialIgnorability M) (hoverlap : PolicyOverlap L M)
    (hL : 1 ≤ L) (hK : PomdpKernelLaw M) (lo : Nat) (t : Fin T) :
    ∫ z, actionHistoryRatioBlock M lo t z
        ∂(M.law.map (histActionPair t)) = 1 := by
  have main : ∀ n : Nat, ∀ hn : n < T,
      ∫ z, actionHistoryRatioBlock M lo (⟨n, hn⟩ : Fin T) z
          ∂(M.law.map (histActionPair (⟨n, hn⟩ : Fin T))) = 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hn
        by_cases hlo : lo < n
        · let p : Fin T := ⟨n - 1, by omega⟩
          have hp : p.val + 1 < T := by dsimp [p]; omega
          have hpt : nextEpoch p hp = (⟨n, hn⟩ : Fin T) := by
            apply Fin.ext
            dsimp [nextEpoch, p]
            omega
          rw [integral_actionHistoryRatioBlock_eq_state hign hoverlap hL]
          rw [← hpt, integral_stateHistoryRatioBlock_next hign hoverlap hL hK lo p hp (by
            dsimp [p]
            omega)]
          exact ih (n - 1) (by omega) p.isLt
        · have htnlo : (⟨n, hn⟩ : Fin T).val ≤ lo := by
            change n ≤ lo
            omega
          rw [integral_actionHistoryRatioBlock_eq_state hign hoverlap hL]
          simp_rw [stateHistoryRatioBlock_eq_one_of_le M lo (⟨n, hn⟩ : Fin T) htnlo]
          letI : IsProbabilityMeasure
              (M.law.map (histStateView (⟨n, hn⟩ : Fin T))) :=
            Measure.isProbabilityMeasure_map
              (measurable_histStateView (⟨n, hn⟩ : Fin T)).aemeasurable
          simp
  exact main t.val t.isLt


end CausalSmith.Stat.PomdpLatentOverlapMinimax

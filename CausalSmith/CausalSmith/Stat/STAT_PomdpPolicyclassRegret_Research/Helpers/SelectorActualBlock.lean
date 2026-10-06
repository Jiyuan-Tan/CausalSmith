module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorBlockHistory
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorSegmentGenerated
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorSegmentPast

/-! # Whole-block tails on the actual observed trajectory

The stationary structural-law identity transports the arbitrary-start block
Chebyshev bound through every measurable observed prefix event.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped ENNReal

/-- Read an observed window of a trajectory without padding. -/
-- @node: selectorObservedWindow
def selectorObservedWindow {T nX : Nat} (a n : Nat) (h : a + n ≤ T)
    (w : ObsView T nX) : ObsView n nX :=
  fun t ↦ w ⟨a + t.val, by omega⟩

/-- Reading a fixed observed window is measurable. For [the time horizon](hyp:T),
[the observed-state count](hyp:nX), [the action](hyp:a), [the sample size](hyp:n), and
[the stated assumption](hyp:h), this establishes
[the selector observed window measurability result](goal). -/
@[fun_prop]
-- @node: selectorObservedWindow_measurable
lemma selectorObservedWindow_measurable {T nX : Nat} (a n : Nat) (h : a + n ≤ T) :
    Measurable (selectorObservedWindow (nX := nX) a n h) := by
  unfold selectorObservedWindow
  fun_prop

/-- Decoding after the window start agrees with taking the corresponding observations from the
full decoded path, even for padded lists. For [the time horizon](hyp:T),
[the observed-state count](hyp:nX), [the hidden-state count](hyp:nH), [the action](hyp:a),
[the sample size](hyp:n), [the stated assumption](hyp:h), [the fallback state](hyp:fallback),
[the state](hyp:s), and [the xs](hyp:xs), this establishes
[the selector observed window decode segment result](goal). -/
-- @node: selectorObservedWindow_decodeSegment
lemma selectorObservedWindow_decodeSegment {T nX nH : Nat} (a n : Nat)
    (h : a + n ≤ T) (fallback s : JointState nX nH)
    (xs : List (Bool × ℝ × JointState nX nH)) :
    selectorObservedWindow a n h (obsProj (decodeSegment (n := T) fallback (s, xs))) =
      obsProj (decodeSegment (n := n) fallback
        (segmentPathEnd a (false, 0, fallback) s xs, xs.drop a)) := by
  funext t
  unfold selectorObservedWindow obsProj curState actionAt rewardAt decodeSegment
  simp only [Fin.coe_castSucc]
  have hget (i : Nat) : (xs.drop a).getD i (false, 0, fallback) =
      xs.getD (a + i) (false, 0, fallback) := by
    simp [List.getD, List.getElem?_drop]
  simp only [hget]
  by_cases ht : t.val = 0
  · simp only [ht, Nat.add_zero, ↓reduceIte]
    cases a with
    | zero => simp [ht, segmentPathEnd]
    | succ a => simp [ht, segmentPathEnd_succ_eq_getD]
  · have he : a + t.val - 1 = a + (t.val - 1) := by omega
    simp only [ht, he, show ¬ a + t.val = 0 by omega, ↓reduceIte]

/-- A structural observed prefix depends only on the prefix of the list. For
[the time horizon](hyp:T), [the observed-state count](hyp:nX), [the hidden-state count](hyp:nH),
[the action](hyp:a), [the stated assumption](hyp:h), [the fallback state](hyp:fallback),
[the state](hyp:s), and [the xs](hyp:xs), this establishes
[the selector observed window prefix decode segment result](goal). -/
-- @node: selectorObservedWindow_prefix_decodeSegment
lemma selectorObservedWindow_prefix_decodeSegment {T nX nH : Nat} (a : Nat)
    (h : 0 + a ≤ T) (fallback s : JointState nX nH)
    (xs : List (Bool × ℝ × JointState nX nH)) :
    selectorObservedWindow 0 a h (obsProj (decodeSegment (n := T) fallback (s, xs))) =
      obsProj (decodeSegment (n := a) fallback (s, xs.take a)) := by
  rw [selectorObservedWindow_decodeSegment]
  simp only [segmentPathEnd, List.drop_zero, decodeSegment_take_self]

/-- Every event in the observed past can be represented by a measurable set of the corresponding
finite prefix word. For [the time horizon](hyp:T), [the observed-state count](hyp:nX),
[the action](hyp:a), [the action assumption](hyp:ha), [the past](hyp:past), and
[the past assumption](hyp:hpast), this establishes
[the selector observed past event prefix result](goal). -/
-- @node: selectorObservedPast_event_prefix
lemma selectorObservedPast_event_prefix {T nX a : Nat} (ha : a ≤ T)
    (past : Set (ObsView T nX)) (hpast : MeasurableSet[selectorObservedPast T nX a] past) :
    ∃ P : Set (ObsView a nX), MeasurableSet P ∧
      past = {w | selectorObservedWindow 0 a (by omega) w ∈ P} := by
  obtain ⟨P, hP, he⟩ := hpast
  let read := fun v : ObsView a nX ↦ fun t : {t : Fin T // t.val < a} ↦
    v ⟨t.1.val, t.2⟩
  refine ⟨read ⁻¹' P, (by fun_prop : Measurable read) hP, ?_⟩
  rw [← he]
  ext w
  change ((fun t : {t : Fin T // t.val < a} ↦ w t.1) ∈ P) ↔
    read (selectorObservedWindow 0 a (by omega) w) ∈ P
  have hread : read (selectorObservedWindow 0 a (by omega) w) =
      (fun t : {t : Fin T // t.val < a} ↦ w t.1) := by
    funext t
    simp [read, selectorObservedWindow]
  rw [hread]

/-- Every complete selector block lies within the observed trajectory. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), and [the block index](hyp:ell),
this establishes [the selector block end bound result](goal). -/
-- @node: selector_block_end_le
lemma selector_block_end_le (T M : Nat) (ell : Fin (numBlocks M)) :
    ell.val * blockLen T M + blockLen T M ≤ T := by
  calc
    _ = (ell.val + 1) * blockLen T M := by ring
    _ ≤ numBlocks M * blockLen T M := Nat.mul_le_mul_right _ ell.isLt
    _ ≤ T := by simpa [blockLen, Nat.mul_comm] using Nat.div_mul_le_self T (numBlocks M)

/-- The selector's explicit chronological score is the raw PHIW average of its observed window.
This preserves all partial-history ratios. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the observed-state count](hyp:nX),
[the history length](hyp:k), [the behavior policy](hyp:b), [the target policy](hyp:e),
[the block index](hyp:ell), and [the observed word](hyp:w), this establishes
[the selector block score equality partial-history importance-weighted raw window result](goal). -/
-- @node: selector_blockScore_eq_phiwRaw_window
lemma selector_blockScore_eq_phiwRaw_window (T M nX k : Nat) (b e : Policy nX)
    (ell : Fin (numBlocks M)) (w : ObsView T nX) :
    blockScore T M nX k b e ell w =
      phiwRaw k b e (selectorObservedWindow (ell.val * blockLen T M)
        (blockLen T M) (selector_block_end_le T M ell) w) := by
  classical
  have hb := selector_block_end_le T M ell
  unfold blockScore phiwRaw
  dsimp only
  congr 1
  symm
  apply Finset.sum_bij (fun t _ ↦ t.val)
  · intro t ht
    simpa using (Finset.mem_filter.mp ht).2
  · intro t ht u hu he
    exact Fin.ext he
  · intro t ht
    have ht' := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
    exact ⟨⟨t, ht'⟩, by simpa using (Finset.mem_filter.mp ht).2, rfl⟩
  · intro t ht
    have hT : ell.val * blockLen T M + t.val < T := by omega
    simp only [dif_pos hT, phiwScore, selectorObservedWindow]
    congr 1
    apply Finset.prod_bij (fun r _ ↦ r.val)
    · intro r hr
      simpa using (Finset.mem_filter.mp hr).2
    · intro r hr u hu he
      exact Fin.ext he
    · intro r hr
      have hr' := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
      refine ⟨⟨r, hr'⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      exact (Finset.mem_filter.mp hr).2
    · intro r hr
      have hR : ell.val * blockLen T M + r.val < T := by omega
      simp only [dif_pos hR]

/-- Equation (10), with any measurable observed prefix event, under the actual observation law.
This is the direct chronological input to medians. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the sample size](hyp:n), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the action](hyp:a), [the action assumption](hyp:ha),
[the past](hyp:past), [the past assumption](hyp:hpast), [the candidate index](hyp:j),
[the history length](hyp:k), [the history length assumption](hyp:hk),
[the sample size assumption](hyp:hn), [the observed state](hyp:x), and
[the observed state assumption](hyp:hx), this establishes
[the selector actual observed window chebyshev past result](goal). -/
-- @node: selector_actual_observed_window_chebyshev_past
lemma selector_actual_observed_window_chebyshev_past {T M n : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (a : Nat) (ha : a + n ≤ T) (past : Set (ObsView a m.nX))
    (hpast : MeasurableSet past) (j : Fin M) (k : Nat)
    (hk : 2 * k ≤ n) (hn : 4 ≤ n) (x : ℝ) (hx : 0 < x) :
    (obsLaw m.Mx.toRawB) {w |
      selectorObservedWindow 0 a (by omega) w ∈ past ∧
      mixingAlpha t0 ^ k *
        (overlapRadius C + 1 / ((n - k : Nat) * (1 - mixingAlpha t0))) + x <
          |phiwRaw k m.Mx.b (m.Mx.E j) (selectorObservedWindow a n ha w) -
            policyValue m j|} ≤
      ENNReal.ofReal (((1 + 2 / (policyFactor zeta - 1) +
        4 / (1 - mixingAlpha t0)) * policyFactor zeta ^ (k + 1) /
          (n - k : Nat)) / x ^ 2) *
      (obsLaw m.Mx.toRawB) {w | selectorObservedWindow 0 a (by omega) w ∈ past} := by
  have hraw : Measurable (phiwRaw (T := n) k m.Mx.b (m.Mx.E j)) := by
    unfold phiwRaw
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro t ht
    exact phiwScore_measurable k m.Mx.b (m.Mx.E j) t
  have hP : MeasurableSet {w : ObsView T m.nX |
      selectorObservedWindow 0 a (by omega) w ∈ past} :=
    (selectorObservedWindow_measurable 0 a (by omega)) hpast
  have hE : MeasurableSet {w : ObsView T m.nX |
      selectorObservedWindow 0 a (by omega) w ∈ past ∧
      mixingAlpha t0 ^ k *
        (overlapRadius C + 1 / ((n - k : Nat) * (1 - mixingAlpha t0))) + x <
          |phiwRaw k m.Mx.b (m.Mx.E j) (selectorObservedWindow a n ha w) -
            policyValue m j|} := by
    exact hP.inter (measurableSet_lt measurable_const
      (continuous_abs.measurable.comp
        ((hraw.comp (selectorObservedWindow_measurable a n ha)).sub_const _)))
  unfold obsLaw
  rw [Measure.map_apply (by fun_prop) hE, Measure.map_apply (by fun_prop) hP]
  change m.Mx.law _ ≤ _ * m.Mx.law _
  rw [selector_actual_law_eq_stationary_segment t0 zeta C m hClass,
    segmentLaw_eq_sum_fixed_start]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hdecode : Measurable (fun xs ↦ decodeSegment (n := T)
      (⟨0, hClass.finite_state.1⟩, ⟨0, hClass.finite_state.2⟩) (s, xs)) := by fun_prop
  rw [Measure.map_apply hdecode ((by fun_prop : Measurable (obsProj (T := T))) hE),
    Measure.map_apply hdecode ((by fun_prop : Measurable (obsProj (T := T))) hP)]
  have htail := selector_structural_block_chebyshev_past_extended t0 zeta C m hClass
    a (T - (a + n)) s
    {ys | obsProj (decodeSegment (n := a)
      (⟨0, hClass.finite_state.1⟩, ⟨0, hClass.finite_state.2⟩) (s, ys)) ∈ past}
    (by exact ((by fun_prop : Measurable (fun ys ↦ obsProj (decodeSegment (n := a)
      (⟨0, hClass.finite_state.1⟩, ⟨0, hClass.finite_state.2⟩) (s, ys))))) hpast)
    j k hk hn x hx
  rw [show a + (n + (T - (a + n))) = T by omega] at htail
  simp only [Set.preimage_ofPred_eq, selectorObservedWindow_prefix_decodeSegment]
  simp only [selectorObservedWindow_decodeSegment]
  calc
    _ ≤ ENNReal.ofReal (stationaryLaw (policyKernel m.Mx.toRawB m.Mx.b) s) *
        (ENNReal.ofReal (((1 + 2 / (policyFactor zeta - 1) +
          4 / (1 - mixingAlpha t0)) * policyFactor zeta ^ (k + 1) /
            (n - k : Nat)) / x ^ 2) * _) := by
          gcongr
          exact htail
    _ = _ := by
      simp only [Set.mem_ofPred_eq]
      ac_rfl

/-- The actual block score satisfies equation (10) after any event measurable before its block
start. No block independence or conditional-law choice is used. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the block index](hyp:ell), [the past](hyp:past),
[the past assumption](hyp:hpast), [the candidate index](hyp:j), [the history length](hyp:k),
[the history length assumption](hyp:hk), [the sample size assumption](hyp:hn),
[the observed state](hyp:x), and [the observed state assumption](hyp:hx), this establishes
[the selector actual block chebyshev past result](goal). -/
-- @node: selector_actual_block_chebyshev_past
lemma selector_actual_block_chebyshev_past {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (ell : Fin (numBlocks M)) (past : Set (ObsView T m.nX))
    (hpast : MeasurableSet[selectorObservedPast T m.nX
      (ell.val * blockLen T M)] past) (j : Fin M) (k : Nat)
    (hk : 2 * k ≤ blockLen T M) (hn : 4 ≤ blockLen T M) (x : ℝ) (hx : 0 < x) :
    (obsLaw m.Mx.toRawB) (past ∩ {w |
      mixingAlpha t0 ^ k *
        (overlapRadius C + 1 / ((blockLen T M - k : Nat) * (1 - mixingAlpha t0))) + x <
          |blockScore T M m.nX k m.Mx.b (m.Mx.E j) ell w - policyValue m j|}) ≤
      ENNReal.ofReal (((1 + 2 / (policyFactor zeta - 1) +
        4 / (1 - mixingAlpha t0)) * policyFactor zeta ^ (k + 1) /
          (blockLen T M - k : Nat)) / x ^ 2) * (obsLaw m.Mx.toRawB) past := by
  have hbound := selector_block_end_le T M ell
  obtain ⟨P, hP, he⟩ := selectorObservedPast_event_prefix (by omega) past hpast
  have htail := selector_actual_observed_window_chebyshev_past t0 zeta C m hClass
    (ell.val * blockLen T M) hbound P hP j k hk hn x hx
  simpa only [he, selector_blockScore_eq_phiwRaw_window, ← Set.ofPred_and] using htail

/-- Real-valued form of the actual block past-event tail, for chronological products and the
simultaneous median inequality. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the block index](hyp:ell), [the past](hyp:past),
[the past assumption](hyp:hpast), [the candidate index](hyp:j), [the history length](hyp:k),
[the history length assumption](hyp:hk), [the sample size assumption](hyp:hn),
[the observed state](hyp:x), and [the observed state assumption](hyp:hx), this establishes
[the selector actual block chebyshev past real result](goal). -/
-- @node: selector_actual_block_chebyshev_past_real
lemma selector_actual_block_chebyshev_past_real {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (ell : Fin (numBlocks M)) (past : Set (ObsView T m.nX))
    (hpast : MeasurableSet[selectorObservedPast T m.nX
      (ell.val * blockLen T M)] past) (j : Fin M) (k : Nat)
    (hk : 2 * k ≤ blockLen T M) (hn : 4 ≤ blockLen T M) (x : ℝ) (hx : 0 < x) :
    ((obsLaw m.Mx.toRawB) (past ∩ {w |
      mixingAlpha t0 ^ k *
        (overlapRadius C + 1 / ((blockLen T M - k : Nat) * (1 - mixingAlpha t0))) + x <
          |blockScore T M m.nX k m.Mx.b (m.Mx.E j) ell w - policyValue m j|})).toReal ≤
      (((1 + 2 / (policyFactor zeta - 1) +
        4 / (1 - mixingAlpha t0)) * policyFactor zeta ^ (k + 1) /
          (blockLen T M - k : Nat)) / x ^ 2) * ((obsLaw m.Mx.toRawB) past).toReal := by
  letI : IsProbabilityMeasure (obsLaw m.Mx.toRawB) := by
    unfold obsLaw
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hL : 1 < policyFactor zeta := by
    unfold policyFactor
    exact Real.one_lt_exp_iff.mpr hClass.zeta_pos
  have hα : mixingAlpha t0 < 1 := by
    unfold mixingAlpha
    apply Real.exp_lt_one_iff.mpr
    exact neg_neg_of_pos (one_div_pos.mpr hClass.t0_pos)
  have hnonneg : 0 ≤ (((1 + 2 / (policyFactor zeta - 1) +
      4 / (1 - mixingAlpha t0)) * policyFactor zeta ^ (k + 1) /
        (blockLen T M - k : Nat)) / x ^ 2) := by positivity
  have htail := selector_actual_block_chebyshev_past t0 zeta C m hClass
    ell past hpast j k hk hn x hx
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) htail
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hnonneg] using hr

end CausalSmith.Stat.PomdpPolicyclassRegret

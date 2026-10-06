module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorChronologicalPast

/-! # Observed histories before selector blocks

The prefix sigma algebra contains every score from an earlier block. This
supplies the chronological measurability input without an independence premise.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax

/-- Observations strictly before a specified epoch generate the past. -/
-- @node: selectorObservedPast
abbrev selectorObservedPast (T nX a : Nat) : MeasurableSpace (ObsView T nX) :=
  MeasurableSpace.comap
    (fun w : ObsView T nX ↦ fun t : {t : Fin T // t.val < a} ↦ w t.1)
    inferInstance

/-- The observed prefix uses only measurable trajectory coordinates. For
[the time horizon](hyp:T), [the observed-state count](hyp:nX), and [the action](hyp:a), this
establishes [the selector observed past bound result](goal). -/
-- @node: selectorObservedPast_le
lemma selectorObservedPast_le (T nX a : Nat) :
    selectorObservedPast T nX a ≤ (inferInstance : MeasurableSpace (ObsView T nX)) := by
  apply Measurable.comap_le
  fun_prop

/-- Increasing the observed cutoff increases the available information. For
[the time horizon](hyp:T), [the observed-state count](hyp:nX), [the action](hyp:a),
[the a'](hyp:a'), and [the stated assumption](hyp:h), this establishes
[the selector observed past mono result](goal). -/
-- @node: selectorObservedPast_mono
lemma selectorObservedPast_mono (T nX a a' : Nat) (h : a ≤ a') :
    selectorObservedPast T nX a ≤ selectorObservedPast T nX a' := by
  let f := fun w : ObsView T nX ↦ fun t : {t : Fin T // t.val < a} ↦ w t.1
  let g := fun w : ObsView T nX ↦ fun t : {t : Fin T // t.val < a'} ↦ w t.1
  let restrict := fun v : ({i : Fin T // i.val < a'} → Fin nX × Bool × ℝ) ↦
    fun t : {t : Fin T // t.val < a} ↦ v ⟨t.1, t.2.trans_le h⟩
  have hg : Measurable[selectorObservedPast T nX a'] g := comap_measurable g
  have hr : Measurable restrict := by fun_prop
  exact (hr.comp hg).comap_le

/-- Every coordinate strictly before the cutoff is measurable in the past. For
[the time horizon](hyp:T), [the observed-state count](hyp:nX), [the action](hyp:a),
[the epoch index](hyp:t), and [the epoch index assumption](hyp:ht), this establishes
[the selector observed past eval result](goal). -/
@[fun_prop]
-- @node: selectorObservedPast_eval
lemma selectorObservedPast_eval {T nX a : Nat} (t : Fin T) (ht : t.val < a) :
    Measurable[selectorObservedPast T nX a] (fun w : ObsView T nX ↦ w t) := by
  let f := fun w : ObsView T nX ↦ fun i : {i : Fin T // i.val < a} ↦ w i.1
  have hf : Measurable[selectorObservedPast T nX a] f := comap_measurable f
  exact (show Measurable (fun v : ({i : Fin T // i.val < a} →
    Fin nX × Bool × ℝ) ↦ v ⟨t, ht⟩) from measurable_pi_apply _).comp hf

/-- All coordinates of an earlier block precede the later block start. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the block index](hyp:ell),
[the ell'](hyp:ell'), [the stated assumption](hyp:h), [the reward symbol](hyp:r), and
[the reward symbol assumption](hyp:hr), this establishes
[the selector earlier block index strict bound result](goal). -/
-- @node: selector_earlier_block_index_lt
lemma selector_earlier_block_index_lt {T M : Nat}
    (ell ell' : Fin (numBlocks M)) (h : ell < ell')
    (r : Nat) (hr : r < blockLen T M) :
    ell.val * blockLen T M + r < ell'.val * blockLen T M := by
  calc
    _ < ell.val * blockLen T M + blockLen T M := Nat.add_lt_add_left hr _
    _ = (ell.val + 1) * blockLen T M := by ring
    _ ≤ ell'.val * blockLen T M := Nat.mul_le_mul_right _ h

/-- An earlier score is measurable at the next block start, including its partial-history
products and its zero-valued out-of-range branches. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the observed-state count](hyp:nX),
[the history length](hyp:k), [the behavior policy](hyp:b), [the target policy](hyp:e),
[the block index](hyp:ell), [the ell'](hyp:ell'), and [the stated assumption](hyp:h), this
establishes [the selector block score measurability past result](goal). -/
@[fun_prop]
-- @node: selector_blockScore_measurable_past
lemma selector_blockScore_measurable_past (T M nX k : Nat) (b e : Policy nX)
    (ell ell' : Fin (numBlocks M)) (h : ell < ell') :
    Measurable[selectorObservedPast T nX (ell'.val * blockLen T M)]
      (blockScore T M nX k b e ell) := by
  unfold blockScore
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro t ht
  have ht' := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
  split_ifs with hT
  · have hcoord := selectorObservedPast_eval (nX := nX)
      (⟨ell.val * blockLen T M + t, hT⟩ : Fin T)
      (selector_earlier_block_index_lt ell ell' h t ht')
    apply Measurable.mul
    · exact hcoord.snd.snd
    · apply Finset.measurable_prod
      intro r hr
      have hr' := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
      split_ifs with hR
      · have hcoordR := selectorObservedPast_eval (nX := nX)
          (⟨ell.val * blockLen T M + r, hR⟩ : Fin T)
          (selector_earlier_block_index_lt ell ell' h r hr')
        exact (measurable_of_finite (fun xa : Fin nX × Bool ↦ ratio b e xa.1 xa.2)).comp
          (hcoordR.fst.prodMk hcoordR.snd.fst)
      · exact measurable_const
  · exact measurable_const

/-- Earlier bad-score events are measurable before each later block. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the observed-state count](hyp:nX), [the history length](hyp:k), [the behavior policy](hyp:b),
[the target policy](hyp:e), [the block index](hyp:ell), [the ell'](hyp:ell'),
[the stated assumption](hyp:h), [the δ](hyp:δ), and [the parameter](hyp:θ), this establishes
[the selector block bad measurability past result](goal). -/
-- @node: selector_block_bad_measurable_past
lemma selector_block_bad_measurable_past (T M nX k : Nat) (b e : Policy nX)
    (ell ell' : Fin (numBlocks M)) (h : ell < ell') (δ θ : ℝ) :
    MeasurableSet[selectorObservedPast T nX (ell'.val * blockLen T M)]
      {w | δ < |blockScore T M nX k b e ell w - θ|} := by
  apply measurableSet_lt measurable_const
  exact continuous_abs.measurable.comp
    ((selector_blockScore_measurable_past T M nX k b e ell ell' h).sub_const θ)

end CausalSmith.Stat.PomdpPolicyclassRegret

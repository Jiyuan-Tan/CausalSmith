module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorChronological

/-!
# Chronological concentration from past-event bounds

This module packages the median argument with a direct intersection bound for
every event measurable before the current block.  It lets trajectory-specific
Markov calculations avoid constructing a regular conditional distribution.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory
open scoped ENNReal

/-- A uniform intersection bound for every event known before the current index gives the
product bound for any specified chronological subset. For [the sample space](hyp:Ω),
[the ι](hyp:ι), [the m₀](hyp:m₀), [the measure](hyp:μ), [the observed history](hyp:history),
[the model assumption](hyp:hm), [the bad](hyp:bad), [the bad assumption](hyp:hbad),
[the before assumption](hyp:hbefore), [the policy](hyp:p), [the policy assumption](hyp:hp),
[the step assumption](hyp:hstep), and [the index subset](hyp:S), this establishes
[the selector joint bad probability real of past result](goal). -/
-- @node: selector_joint_bad_probability_real_of_past
lemma selector_joint_bad_probability_real_of_past {Ω ι : Type*}
    {m₀ : MeasurableSpace Ω} [LinearOrder ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (history : ι → MeasurableSpace Ω) (hm : ∀ i, history i ≤ m₀)
    (bad : ι → Set Ω) (hbad : ∀ i, MeasurableSet (bad i))
    (hbefore : ∀ i j, i < j → MeasurableSet[history j] (bad i))
    (p : ℝ) (hp : 0 ≤ p)
    (hstep : ∀ i past, MeasurableSet[history i] past →
      (μ (past ∩ bad i)).toReal ≤ p * (μ past).toReal)
    (S : Finset ι) :
    (μ {w | ∀ i ∈ S, w ∈ bad i}).toReal ≤ p ^ S.card := by
  classical
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert i S hlt ih =>
    have hi : i ∉ S := fun hi ↦ (lt_irrefl i) (hlt i hi)
    have hpast : MeasurableSet[history i] {w | ∀ j ∈ S, w ∈ bad j} := by
      have h := S.measurableSet_biInter (fun j hj ↦ hbefore j i (hlt j hj))
      have he : {w | ∀ j ∈ S, w ∈ bad j} = ⋂ j ∈ S, bad j := by
        ext w
        simp
      rw [he]
      exact h
    have hevent : {w | ∀ j ∈ insert i S, w ∈ bad j} =
        {w | ∀ j ∈ S, w ∈ bad j} ∩ bad i := by
      ext w
      simp only [Set.mem_ofPred_eq, Finset.mem_insert, Set.mem_inter_iff]
      constructor
      · intro h
        exact ⟨fun j hj ↦ h j (Or.inr hj), h i (Or.inl rfl)⟩
      · rintro ⟨hS, hi⟩ j (rfl | hj)
        · exact hi
        · exact hS j hj
    rw [hevent, Finset.card_insert_of_notMem hi, pow_succ]
    exact (hstep i _ hpast).trans
      (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left ih hp)

/-- The direct past-event form of the chronological product bound, expressed as an extended
nonnegative probability for use in median union bounds. For [the sample space](hyp:Ω),
[the ι](hyp:ι), [the m₀](hyp:m₀), [the measure](hyp:μ), [the observed history](hyp:history),
[the model assumption](hyp:hm), [the bad](hyp:bad), [the bad assumption](hyp:hbad),
[the before assumption](hyp:hbefore), [the policy](hyp:p), [the policy assumption](hyp:hp),
[the step assumption](hyp:hstep), and [the index subset](hyp:S), this establishes
[the selector joint bad probability of past result](goal). -/
-- @node: selector_joint_bad_probability_of_past
lemma selector_joint_bad_probability_of_past {Ω ι : Type*}
    {m₀ : MeasurableSpace Ω} [LinearOrder ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (history : ι → MeasurableSpace Ω) (hm : ∀ i, history i ≤ m₀)
    (bad : ι → Set Ω) (hbad : ∀ i, MeasurableSet (bad i))
    (hbefore : ∀ i j, i < j → MeasurableSet[history j] (bad i))
    (p : ℝ) (hp : 0 ≤ p)
    (hstep : ∀ i past, MeasurableSet[history i] past →
      (μ (past ∩ bad i)).toReal ≤ p * (μ past).toReal)
    (S : Finset ι) :
    μ {w | ∀ i ∈ S, w ∈ bad i} ≤ (ENNReal.ofReal p) ^ S.card := by
  have h := ENNReal.ofReal_le_ofReal
    (selector_joint_bad_probability_real_of_past μ history hm bad hbad hbefore
      p hp hstep S)
  simpa only [ENNReal.ofReal_toReal (measure_ne_top μ _), ENNReal.ofReal_pow hp] using h

/-- Adapted block errors with uniform past-event probability bounds give the dependent-block
median concentration bound, via chronological iteration. For [the sample space](hyp:Ω),
[the m₀](hyp:m₀), [the measure](hyp:μ), [the second event](hyp:B),
[the odd assumption](hyp:hodd), [the observed history](hyp:history),
[the model assumption](hyp:hm), [the candidate score](hyp:score), [the parameter](hyp:θ),
[the δ](hyp:δ), [the policy](hyp:p), [the policy assumption](hyp:hp),
[the bad assumption](hyp:hbad), [the before assumption](hyp:hbefore), and
[the step assumption](hyp:hstep), this establishes
[the selector median tail of past result](goal). -/
-- @node: selector_median_tail_of_past
lemma selector_median_tail_of_past {Ω : Type*} {m₀ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] {B : Nat} (hodd : B % 2 = 1)
    (history : Fin B → MeasurableSpace Ω) (hm : ∀ i, history i ≤ m₀)
    (score : Fin B → Ω → ℝ) (θ δ p : ℝ) (hp : 0 ≤ p)
    (hbad : ∀ i, MeasurableSet {w | δ < |score i w - θ|})
    (hbefore : ∀ i j, i < j →
      MeasurableSet[history j] {w | δ < |score i w - θ|})
    (hstep : ∀ i past, MeasurableSet[history i] past →
      (μ (past ∩ {w | δ < |score i w - θ|})).toReal ≤ p * (μ past).toReal) :
    μ {w | δ < |(⨆ S : {S : Finset (Fin B) // S.card = (B + 1) / 2},
      ⨅ ell : S.1, score ell.1 w) - θ|} ≤
      (2 : ℝ≥0∞) ^ B * (ENNReal.ofReal p) ^ ((B + 1) / 2) := by
  apply selector_median_tail_two_pow μ hodd score θ δ (ENNReal.ofReal p)
  intro S hS
  simpa only [hS, Set.mem_ofPred_eq] using selector_joint_bad_probability_of_past μ history hm
    (fun i ↦ {w | δ < |score i w - θ|}) hbad hbefore p hp hstep S

/-- Equation (11) for a single median, from the supplied adapted one-block bounds. The threshold
ratio is at most one; no independence is used. For [the sample space](hyp:Ω), [the m₀](hyp:m₀),
[the measure](hyp:μ), [the second event](hyp:B), [the odd assumption](hyp:hodd),
[the observed history](hyp:history), [the model assumption](hyp:hm),
[the candidate score](hyp:score), [the parameter](hyp:θ), [the δ](hyp:δ),
[the reward symbol](hyp:r), [the r0 assumption](hyp:hr0), [the r1 assumption](hyp:hr1),
[the bad assumption](hyp:hbad), [the before assumption](hyp:hbefore), and
[the step assumption](hyp:hstep), this establishes
[the selector median tail ratio of past result](goal). -/
-- @node: selector_median_tail_ratio_of_past
lemma selector_median_tail_ratio_of_past {Ω : Type*} {m₀ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] {B : Nat} (hodd : B % 2 = 1)
    (history : Fin B → MeasurableSpace Ω) (hm : ∀ i, history i ≤ m₀)
    (score : Fin B → Ω → ℝ) (θ δ r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hbad : ∀ i, MeasurableSet {w | δ < |score i w - θ|})
    (hbefore : ∀ i j, i < j →
      MeasurableSet[history j] {w | δ < |score i w - θ|})
    (hstep : ∀ i past, MeasurableSet[history i] past →
      (μ (past ∩ {w | δ < |score i w - θ|})).toReal ≤ r ^ 2 * (μ past).toReal) :
    μ {w | δ < |(⨆ S : {S : Finset (Fin B) // S.card = (B + 1) / 2},
      ⨅ ell : S.1, score ell.1 w) - θ|} ≤ ENNReal.ofReal ((2 * r) ^ B) := by
  have ht := selector_median_tail_of_past μ hodd history hm score θ δ
    (r ^ 2) (sq_nonneg r) hbad hbefore hstep
  rw [ENNReal.ofReal_pow hr0] at ht
  have hr : ENNReal.ofReal r ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hr1
  have halgebra := selector_odd_majority_power_le hodd (ENNReal.ofReal r) hr
  apply ht.trans
  simpa only [ENNReal.ofReal_pow (show 0 ≤ 2 * r by positivity),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] using halgebra

/-- A union bound over a finite list gives the simultaneous version of (11), after each
candidate's median bound has been proved chronologically. For [the sample space](hyp:Ω),
[the m₀](hyp:m₀), [the measure](hyp:μ), [the second event](hyp:B),
[the candidate-policy count](hyp:M), [the odd assumption](hyp:hodd),
[the observed history](hyp:history), [the model assumption](hyp:hm),
[the candidate score](hyp:score), [the parameter](hyp:θ), [the δ](hyp:δ),
[the reward symbol](hyp:r), [the r0 assumption](hyp:hr0), [the r1 assumption](hyp:hr1),
[the bad assumption](hyp:hbad), [the before assumption](hyp:hbefore), and
[the step assumption](hyp:hstep), this establishes
[the selector simultaneous median tail of past result](goal). -/
-- @node: selector_simultaneous_median_tail_of_past
lemma selector_simultaneous_median_tail_of_past {Ω : Type*}
    {m₀ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {B M : Nat} (hodd : B % 2 = 1)
    (history : Fin B → MeasurableSpace Ω) (hm : ∀ i, history i ≤ m₀)
    (score : Fin M → Fin B → Ω → ℝ) (θ : Fin M → ℝ)
    (δ r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hbad : ∀ j i, MeasurableSet {w | δ < |score j i w - θ j|})
    (hbefore : ∀ j i i', i < i' →
      MeasurableSet[history i'] {w | δ < |score j i w - θ j|})
    (hstep : ∀ j i past, MeasurableSet[history i] past →
      (μ (past ∩ {w | δ < |score j i w - θ j|})).toReal ≤
        r ^ 2 * (μ past).toReal) :
    μ {w | ∃ j, δ < |(⨆ S : {S : Finset (Fin B) // S.card = (B + 1) / 2},
      ⨅ ell : S.1, score j ell.1 w) - θ j|} ≤
      (M : ℝ≥0∞) * ENNReal.ofReal ((2 * r) ^ B) := by
  have hevent : {w | ∃ j, δ < |(⨆ S :
      {S : Finset (Fin B) // S.card = (B + 1) / 2},
      ⨅ ell : S.1, score j ell.1 w) - θ j|} =
      ⋃ j, {w | δ < |(⨆ S : {S : Finset (Fin B) // S.card = (B + 1) / 2},
        ⨅ ell : S.1, score j ell.1 w) - θ j|} := by
    ext w
    simp
  rw [hevent]
  calc
    _ ≤ ∑ j : Fin M, μ {w | δ < |(⨆ S :
        {S : Finset (Fin B) // S.card = (B + 1) / 2},
        ⨅ ell : S.1, score j ell.1 w) - θ j|} := measure_iUnion_fintype_le μ _
    _ ≤ ∑ _j : Fin M, ENNReal.ofReal ((2 * r) ^ B) :=
      Finset.sum_le_sum fun j _ ↦ selector_median_tail_ratio_of_past μ hodd
        history hm (score j) (θ j) δ r hr0 hr1 (hbad j) (hbefore j) (hstep j)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end CausalSmith.Stat.PomdpPolicyclassRegret

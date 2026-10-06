module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorMedianWitness
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Chronological joint bad-event bounds

The conditional one-block probability bound implies a product bound for any
specified subset of blocks by integrating over the past event and inducting
from the latest selected block. This implements the iterated-conditioning
step between (10) and (11), without any independence assumption. The actual
trajectory must still supply the adapted events and conditional block law.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory
open scoped ENNReal

/-- A conditional bad-event bound multiplies the probability of any past event by the same
bound. Both events may be dependent. For [the sample space](hyp:Ω), [the m₀](hyp:m₀),
[the measure](hyp:μ), [the model](hyp:m), [the model assumption](hyp:hm), [the past](hyp:past),
[the bad](hyp:bad), [the past assumption](hyp:hpast), [the bad assumption](hyp:hbad),
[the policy](hyp:p), and [the cond assumption](hyp:hcond), this establishes
[the selector inter probability of cond exp bound result](goal). -/
-- @node: selector_inter_probability_of_condExp_le
lemma selector_inter_probability_of_condExp_le {Ω : Type*}
    {m₀ : MeasurableSpace Ω} (μ : Measure Ω) [IsFiniteMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    (past bad : Set Ω) (hpast : MeasurableSet[m] past)
    (hbad : MeasurableSet[m₀] bad) (p : ℝ)
    (hcond : μ[bad.indicator (fun _ ↦ (1 : ℝ)) | m] ≤ᵐ[μ] fun _ ↦ p) :
    (μ (past ∩ bad)).toReal ≤ p * (μ past).toReal := by
  have hI : Integrable (bad.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const 1).indicator hbad
  have heq : ∫ w in past, bad.indicator (fun _ ↦ (1 : ℝ)) w ∂μ =
      (μ (past ∩ bad)).toReal := by
    rw [integral_indicator hbad, setIntegral_const]
    simp only [Measure.real, Measure.restrict_apply hbad, Set.inter_comm, smul_eq_mul, mul_one]
  calc
    (μ (past ∩ bad)).toReal =
        ∫ w in past, μ[bad.indicator (fun _ ↦ (1 : ℝ)) | m] w ∂μ := by
      rw [setIntegral_condExp hm hI hpast, heq]
    _ ≤ ∫ _ in past, p ∂μ :=
      setIntegral_mono_ae integrable_condExp.integrableOn (integrable_const p).integrableOn hcond
    _ = p * (μ past).toReal := by
      rw [setIntegral_const]
      simp only [Measure.real, smul_eq_mul, mul_comm]

/-- Uniform conditional bounds imply a product bound for a specified finite set of
chronologically ordered events. Earlier bad events are measurable in the history available
before each later event. For [the sample space](hyp:Ω), [the ι](hyp:ι), [the m₀](hyp:m₀),
[the measure](hyp:μ), [the observed history](hyp:history), [the model assumption](hyp:hm),
[the bad](hyp:bad), [the bad assumption](hyp:hbad), [the before assumption](hyp:hbefore),
[the policy](hyp:p), [the policy assumption](hyp:hp), [the cond assumption](hyp:hcond), and
[the index subset](hyp:S), this establishes
[the selector joint bad probability real result](goal). -/
-- @node: selector_joint_bad_probability_real
lemma selector_joint_bad_probability_real {Ω ι : Type*}
    {m₀ : MeasurableSpace Ω} [LinearOrder ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (history : ι → MeasurableSpace Ω) (hm : ∀ i, history i ≤ m₀)
    (bad : ι → Set Ω) (hbad : ∀ i, MeasurableSet (bad i))
    (hbefore : ∀ i j, i < j → MeasurableSet[history j] (bad i))
    (p : ℝ) (hp : 0 ≤ p)
    (hcond : ∀ i, μ[(bad i).indicator (fun _ ↦ (1 : ℝ)) | history i] ≤ᵐ[μ]
      fun _ ↦ p) (S : Finset ι) :
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
    exact (selector_inter_probability_of_condExp_le μ (history i) (hm i)
      _ (bad i) hpast (hbad i) p (hcond i)).trans
      (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left ih hp)

/-- The chronological product bound in extended nonnegative probabilities, in the form needed by
the median union bound. For [the sample space](hyp:Ω), [the ι](hyp:ι), [the m₀](hyp:m₀),
[the measure](hyp:μ), [the observed history](hyp:history), [the model assumption](hyp:hm),
[the bad](hyp:bad), [the bad assumption](hyp:hbad), [the before assumption](hyp:hbefore),
[the policy](hyp:p), [the policy assumption](hyp:hp), [the cond assumption](hyp:hcond), and
[the index subset](hyp:S), this establishes [the selector joint bad probability result](goal). -/
-- @node: selector_joint_bad_probability
lemma selector_joint_bad_probability {Ω ι : Type*}
    {m₀ : MeasurableSpace Ω} [LinearOrder ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (history : ι → MeasurableSpace Ω) (hm : ∀ i, history i ≤ m₀)
    (bad : ι → Set Ω) (hbad : ∀ i, MeasurableSet (bad i))
    (hbefore : ∀ i j, i < j → MeasurableSet[history j] (bad i))
    (p : ℝ) (hp : 0 ≤ p)
    (hcond : ∀ i, μ[(bad i).indicator (fun _ ↦ (1 : ℝ)) | history i] ≤ᵐ[μ]
      fun _ ↦ p) (S : Finset ι) :
    μ {w | ∀ i ∈ S, w ∈ bad i} ≤ (ENNReal.ofReal p) ^ S.card := by
  have h := ENNReal.ofReal_le_ofReal
    (selector_joint_bad_probability_real μ history hm bad hbad hbefore p hp hcond S)
  simpa only [ENNReal.ofReal_toReal (measure_ne_top μ _), ENNReal.ofReal_pow hp] using h

/-- Adapted block errors with uniform conditional probability bounds give the dependent-block
median concentration bound, via chronological iteration. For [the sample space](hyp:Ω),
[the m₀](hyp:m₀), [the measure](hyp:μ), [the second event](hyp:B),
[the odd assumption](hyp:hodd), [the observed history](hyp:history),
[the model assumption](hyp:hm), [the candidate score](hyp:score), [the parameter](hyp:θ),
[the δ](hyp:δ), [the policy](hyp:p), [the policy assumption](hyp:hp),
[the bad assumption](hyp:hbad), [the before assumption](hyp:hbefore), and
[the cond assumption](hyp:hcond), this establishes
[the selector median tail of cond exp result](goal). -/
-- @node: selector_median_tail_of_condExp
lemma selector_median_tail_of_condExp {Ω : Type*} {m₀ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] {B : Nat} (hodd : B % 2 = 1)
    (history : Fin B → MeasurableSpace Ω) (hm : ∀ i, history i ≤ m₀)
    (score : Fin B → Ω → ℝ) (θ δ p : ℝ) (hp : 0 ≤ p)
    (hbad : ∀ i, MeasurableSet {w | δ < |score i w - θ|})
    (hbefore : ∀ i j, i < j →
      MeasurableSet[history j] {w | δ < |score i w - θ|})
    (hcond : ∀ i, μ[({w | δ < |score i w - θ|}).indicator
      (fun _ ↦ (1 : ℝ)) | history i] ≤ᵐ[μ] fun _ ↦ p) :
    μ {w | δ < |(⨆ S : {S : Finset (Fin B) // S.card = (B + 1) / 2},
      ⨅ ell : S.1, score ell.1 w) - θ|} ≤
      (2 : ℝ≥0∞) ^ B * (ENNReal.ofReal p) ^ ((B + 1) / 2) := by
  apply selector_median_tail_two_pow μ hodd score θ δ (ENNReal.ofReal p)
  intro S hS
  simpa only [hS, Set.mem_ofPred_eq] using selector_joint_bad_probability μ history hm
    (fun i ↦ {w | δ < |score i w - θ|}) hbad hbefore p hp hcond S

/-- The extra bad block in an odd majority improves the binomial union bound when the one-block
probability is the square of a ratio at most one. For [the second event](hyp:B),
[the odd assumption](hyp:hodd), [the reward symbol](hyp:r), and
[the reward symbol assumption](hyp:hr), this establishes
[the selector odd majority power bound result](goal). -/
-- @node: selector_odd_majority_power_le
lemma selector_odd_majority_power_le {B : Nat} (hodd : B % 2 = 1)
    (r : ℝ≥0∞) (hr : r ≤ 1) :
    (2 : ℝ≥0∞) ^ B * (r ^ 2) ^ ((B + 1) / 2) ≤ (2 * r) ^ B := by
  have hcount : 2 * ((B + 1) / 2) = B + 1 := by omega
  rw [← pow_mul, hcount, pow_succ, mul_pow]
  calc
    (2 : ℝ≥0∞) ^ B * (r ^ B * r) ≤ 2 ^ B * (r ^ B * 1) := by gcongr
    _ = _ := by rw [mul_one]

/-- Equation (11) for a single median, conditional on the supplied adapted one-block bounds. The
threshold ratio is at most one; no independence is used. For [the sample space](hyp:Ω),
[the m₀](hyp:m₀), [the measure](hyp:μ), [the second event](hyp:B),
[the odd assumption](hyp:hodd), [the observed history](hyp:history),
[the model assumption](hyp:hm), [the candidate score](hyp:score), [the parameter](hyp:θ),
[the δ](hyp:δ), [the reward symbol](hyp:r), [the r0 assumption](hyp:hr0),
[the r1 assumption](hyp:hr1), [the bad assumption](hyp:hbad),
[the before assumption](hyp:hbefore), and [the cond assumption](hyp:hcond), this establishes
[the selector median tail ratio of cond exp result](goal). -/
-- @node: selector_median_tail_ratio_of_condExp
lemma selector_median_tail_ratio_of_condExp {Ω : Type*} {m₀ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] {B : Nat} (hodd : B % 2 = 1)
    (history : Fin B → MeasurableSpace Ω) (hm : ∀ i, history i ≤ m₀)
    (score : Fin B → Ω → ℝ) (θ δ r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hbad : ∀ i, MeasurableSet {w | δ < |score i w - θ|})
    (hbefore : ∀ i j, i < j →
      MeasurableSet[history j] {w | δ < |score i w - θ|})
    (hcond : ∀ i, μ[({w | δ < |score i w - θ|}).indicator
      (fun _ ↦ (1 : ℝ)) | history i] ≤ᵐ[μ] fun _ ↦ r ^ 2) :
    μ {w | δ < |(⨆ S : {S : Finset (Fin B) // S.card = (B + 1) / 2},
      ⨅ ell : S.1, score ell.1 w) - θ|} ≤ ENNReal.ofReal ((2 * r) ^ B) := by
  have ht := selector_median_tail_of_condExp μ hodd history hm score θ δ
    (r ^ 2) (sq_nonneg r) hbad hbefore hcond
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
[the cond assumption](hyp:hcond), this establishes
[the selector simultaneous median tail of cond exp result](goal). -/
-- @node: selector_simultaneous_median_tail_of_condExp
lemma selector_simultaneous_median_tail_of_condExp {Ω : Type*}
    {m₀ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {B M : Nat} (hodd : B % 2 = 1)
    (history : Fin B → MeasurableSpace Ω) (hm : ∀ i, history i ≤ m₀)
    (score : Fin M → Fin B → Ω → ℝ) (θ : Fin M → ℝ)
    (δ r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hbad : ∀ j i, MeasurableSet {w | δ < |score j i w - θ j|})
    (hbefore : ∀ j i i', i < i' →
      MeasurableSet[history i'] {w | δ < |score j i w - θ j|})
    (hcond : ∀ j i, μ[({w | δ < |score j i w - θ j|}).indicator
      (fun _ ↦ (1 : ℝ)) | history i] ≤ᵐ[μ] fun _ ↦ r ^ 2) :
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
      Finset.sum_le_sum fun j _ ↦ selector_median_tail_ratio_of_condExp μ hodd
        history hm (score j) (θ j) δ r hr0 hr1 (hbad j) (hbefore j) (hcond j)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end CausalSmith.Stat.PomdpPolicyclassRegret

module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.LargeAlphabet.CollisionProbability
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Squared-loss consequences of the common randomized threshold test. -/

public section
open MeasureTheory ProbabilityTheory Set
namespace CausalSmith.Stat.MarRareqLogfrontier

/-- Given [the specified inputs and assumptions](hyp:Z,Q,κ,t), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabet_joint_loss_integrable
lemma largeAlphabet_joint_loss_integrable
    {Z : Type*} [Finite Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (Q : Measure Z) [IsProbabilityMeasure Q] (κ : BoundedKernel Z) (t : ℝ) :
    Integrable (fun z : Z × ℝ => (z.2 - t) ^ 2) (Q ⊗ₘ κ.1) := by
  let : IsMarkovKernel κ.1 := κ.2.1
  apply (Measure.integrable_compProd_iff (by fun_prop)).mpr
  refine ⟨?_, Integrable.of_finite⟩
  filter_upwards [] with o
  have hb : ∀ᵐ w ∂(κ.1 o), w ∈ Icc (-1 : ℝ) 1 :=
    (ae_mem_iff_measure_eq (μ := κ.1 o) measurableSet_Icc.nullMeasurableSet).2
      (by simpa only [measure_univ] using κ.2.2 o)
  have hm : AEStronglyMeasurable (fun w : ℝ => w) (κ.1 o) := by fun_prop
  exact ((memLp_of_bounded hb hm 2).sub (memLp_const t)).integrable_sq

/-- Given [the specified inputs and assumptions](hyp:Z,Q,κ,t,b,E,hE,hdom), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabet_kernel_event_loss
lemma largeAlphabet_kernel_event_loss
    {Z : Type*} [Finite Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (Q : Measure Z) [IsProbabilityMeasure Q] (κ : BoundedKernel Z)
    (t b : ℝ) (E : Set (Z × ℝ)) (hE : MeasurableSet E)
    (hdom : ∀ z ∈ E, b ≤ (z.2 - t) ^ 2) :
    b * (Q ⊗ₘ κ.1).real E ≤ ∫ o, ∫ w, (w - t) ^ 2 ∂κ.1 o ∂Q := by
  let : IsMarkovKernel κ.1 := κ.2.1
  have hi := largeAlphabet_joint_loss_integrable Q κ t
  have hmono : ∫ z, E.indicator (fun _ => b) z ∂(Q ⊗ₘ κ.1) ≤
      ∫ z : Z × ℝ, (z.2 - t) ^ 2 ∂(Q ⊗ₘ κ.1) := by
    apply integral_mono ((integrable_const b).indicator hE) hi
    intro z
    by_cases hz : z ∈ E
    · simpa only [indicator_of_mem hz] using hdom z hz
    · simp only [indicator_of_notMem hz]
      exact sq_nonneg _
  rw [integral_indicator_const b hE, smul_eq_mul, mul_comm,
    Measure.integral_compProd hi] at hmono
  exact hmono

/-- Given [the specified inputs and assumptions](hyp:a,h,t,w,hh,ht,hw), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabet_good_target_test_loss
lemma largeAlphabet_good_target_test_loss (a h t w : ℝ) (hh : 0 ≤ h)
    (ht : |t - a| ≤ h / 4) (hw : w ≤ a - h / 2) :
    h ^ 2 / 16 ≤ (w - t) ^ 2 := by
  have htlow := (abs_le.mp ht).1
  have herr : h / 4 ≤ t - w := by linarith
  nlinarith [sq_nonneg (t - w - h / 4)]

/-- Given [the specified inputs and assumptions](hyp:a,h,w,hh,hw), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabet_comparison_test_loss
lemma largeAlphabet_comparison_test_loss (a h w : ℝ) (hh : 0 ≤ h)
    (hw : a - h / 2 < w) :
    h ^ 2 / 16 ≤ (w - (a - h)) ^ 2 := by
  have herr : h / 2 ≤ w - (a - h) := by linarith
  nlinarith [sq_nonneg (w - (a - h) - h / 2)]

/-- Given [the specified inputs and assumptions](hyp:Z,Q,κ,a,h,t,hh), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabet_member_test_risk
lemma largeAlphabet_member_test_risk
    {Z : Type*} [Finite Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (Q : Measure Z) [IsProbabilityMeasure Q] (κ : BoundedKernel Z)
    (a h t : ℝ) (hh : 0 ≤ h) :
    (h ^ 2 / 16) * (Q ⊗ₘ κ.1).real {z | z.2 ≤ a - h / 2} ≤
      (∫ o, ∫ w, (w - t) ^ 2 ∂κ.1 o ∂Q) +
        (if h / 4 < |t - a| then h ^ 2 / 16 else 0) := by
  let : IsMarkovKernel κ.1 := κ.2.1
  by_cases ht : h / 4 < |t - a|
  · rw [if_pos ht]
    have hp : (Q ⊗ₘ κ.1).real {z | z.2 ≤ a - h / 2} ≤ 1 :=
      measureReal_le_one
    have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ h ^ 2 / 16)
    have hr : 0 ≤ ∫ o, ∫ w, (w - t) ^ 2 ∂κ.1 o ∂Q :=
      integral_nonneg (fun _ => integral_nonneg (fun _ => sq_nonneg _))
    linarith
  · rw [if_neg ht, add_zero]
    apply largeAlphabet_kernel_event_loss Q κ t (h ^ 2 / 16) _
      (by measurability)
    intro z hz
    exact largeAlphabet_good_target_test_loss a h t z.2 hh (le_of_not_gt ht) hz

/-- Given [the specified inputs and assumptions](hyp:Z,Q,κ,a,h,hh), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabet_comparison_test_risk
lemma largeAlphabet_comparison_test_risk
    {Z : Type*} [Finite Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (Q : Measure Z) [IsProbabilityMeasure Q] (κ : BoundedKernel Z)
    (a h : ℝ) (hh : 0 ≤ h) :
    (h ^ 2 / 16) * (Q ⊗ₘ κ.1).real {z | ¬ z.2 ≤ a - h / 2} ≤
      ∫ o, ∫ w, (w - (a - h)) ^ 2 ∂κ.1 o ∂Q := by
  apply largeAlphabet_kernel_event_loss Q κ (a - h) (h ^ 2 / 16) _
    (by measurability)
  intro z hz
  exact largeAlphabet_comparison_test_loss a h z.2 hh (lt_of_not_ge hz)

end CausalSmith.Stat.MarRareqLogfrontier

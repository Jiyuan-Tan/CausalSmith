module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentOccupancy
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Conditional chi-square comparison and common-design integration for the copula experiment. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- On the roadmap's good event the exponential remainder is at most twice its argument. This statement assumes [the hx condition](hyp:hx), [the hsmall condition](hyp:hsmall). [This is the stated conclusion](goal). -/
-- @node: copula_exp_sub_one_le_twice
lemma copula_exp_sub_one_le_twice (x : ℝ) (hx : 0 ≤ x) (hsmall : x ≤ 1/256) :
    Real.exp x - 1 ≤ 2*x := by
  have hden : 0 < 1-x := by linarith
  have he := Real.exp_bound_div_one_sub_of_interval hx (by linarith : x < 1)
  have hratio : 1/(1-x) ≤ 1+2*x := by
    apply (div_le_iff₀ hden).2
    nlinarith
  linarith

/-- The actual finite label laws admit the chi-square-to-TV comparison without extra regularity. This statement assumes [the hac condition](hyp:hac), [the hx condition](hyp:hx), [the hsmall condition](hyp:hsmall), [the hchi condition](hyp:hchi). [This is the stated conclusion](goal). -/
-- @node: copula_finite_label_tv_le
lemma copula_finite_label_tv_le (n : ℕ) (P Q : Measure (Labels n))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hac : P ≪ Q)
    (x : ℝ) (hx : 0 ≤ x) (hsmall : x ≤ 1/256)
    (hchi : 1+Causalean.Stat.chiSqDiv P Q ≤ Real.exp x) :
    Causalean.Stat.tvDist P Q ≤ (1/2)*Real.sqrt (2*x) := by
  have ht := Causalean.Stat.tvDist_le_half_sqrt_chiSqDiv P Q hac
    (Integrable.of_finite : Integrable (fun l => ((P.rnDeriv Q l).toReal-1)^2) Q)
  have hc : Causalean.Stat.chiSqDiv P Q ≤ 2*x := by
    linarith [copula_exp_sub_one_le_twice x hx hsmall]
  exact ht.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hc) (by norm_num))

/-- Two conditional comparisons imply the roadmap's square-root good-event bound. This statement assumes [the hac0 condition](hyp:hac0), [the hac1 condition](hyp:hac1), [the hA condition](hyp:hA), [the hB condition](hyp:hB), [the hsmall condition](hyp:hsmall), [the hchi0 condition](hyp:hchi0), [the hchi1 condition](hyp:hchi1). [This is the stated conclusion](goal). -/
-- @node: copula_conditional_tv_good
lemma copula_conditional_tv_good (n : ℕ) (P0 P1 Q : Measure (Labels n))
    [IsProbabilityMeasure P0] [IsProbabilityMeasure P1] [IsProbabilityMeasure Q]
    (hac0 : Q ≪ P0) (hac1 : P1 ≪ Q) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hsmall : A+B ≤ 1/256)
    (hchi0 : 1+Causalean.Stat.chiSqDiv Q P0 ≤ Real.exp A)
    (hchi1 : 1+Causalean.Stat.chiSqDiv P1 Q ≤ Real.exp B) :
    Causalean.Stat.tvDist P0 P1 ≤ Real.sqrt (A+B) := by
  have ht0 := copula_finite_label_tv_le n Q P0 hac0 A hA (by linarith) hchi0
  have ht1 := copula_finite_label_tv_le n P1 Q hac1 B hB (by linarith) hchi1
  rw [Causalean.Stat.tvDist_symm Q P0] at ht0
  rw [Causalean.Stat.tvDist_symm P1 Q] at ht1
  have htriangle : Causalean.Stat.tvDist P0 P1 ≤
      Causalean.Stat.tvDist P0 Q+Causalean.Stat.tvDist Q P1 := by
    unfold Causalean.Stat.tvDist
    apply ciSup_le
    intro S
    exact (abs_sub_le (P0.real S.1) (Q.real S.1) (P1.real S.1)).trans
      (add_le_add (Causalean.Stat.abs_measureReal_sub_le_tvDist S.2)
        (Causalean.Stat.abs_measureReal_sub_le_tvDist S.2))
  have hroot : (1/2)*Real.sqrt (2*A)+(1/2)*Real.sqrt (2*B) ≤ Real.sqrt (A+B) := by
    have ha := Real.sq_sqrt (show 0 ≤ 2*A by positivity)
    have hb := Real.sq_sqrt (show 0 ≤ 2*B by positivity)
    have hab := Real.sq_sqrt (show 0 ≤ A+B by positivity)
    nlinarith [Real.sqrt_nonneg (2*A), Real.sqrt_nonneg (2*B),
      Real.sqrt_nonneg (A+B), sq_nonneg (Real.sqrt (2*A)-Real.sqrt (2*B))]
  exact (htriangle.trans (add_le_add ht0 ht1)).trans hroot

/-- Good-event comparison and the bad-event Markov envelope retain every disclosed design. [This is the stated conclusion](goal). -/
-- @node: copula_conditional_tv_envelope
lemma copula_conditional_tv_envelope (n K M : ℕ) (a u ε L : ℝ)
    (h : CopulaDomain n K M a u ε L) :
    ∀ᵐ aug ∂commonAugmentation n K M ε,
      Causalean.Stat.tvDist (nullConditionalLaw n K M a u aug)
        (alternativeConditionalLaw n K M a u aug) ≤
          1/16+256*(activityA n K M a u aug+activityB n K M a u aug) := by
  have hpos : 0 < K := by have := h.2.2.2.1; have := h.2.2.2.2.1; omega
  have ha := h.2.2.2.2.2.1
  have hu := h.2.2.2.2.2.2.1
  filter_upwards [conditional_component_comparisons n K M a u ε L h] with aug hc
  let : IsProbabilityMeasure (nullConditionalLaw n K M a u aug) := hc.2.1
  let : IsProbabilityMeasure (alternativeConditionalLaw n K M a u aug) := hc.2.2.1
  let : IsProbabilityMeasure (intermediateConditionalLaw n K M a u aug) := hc.1
  have hac0 : intermediateConditionalLaw n K M a u aug ≪ nullConditionalLaw n K M a u aug := by
    apply fairLabelMeasure_absolutelyContinuous n
    intro l
    unfold nullConditionalDensity
    apply Finset.prod_pos
    intro C _
    exact lt_of_lt_of_le (by positivity) (component_denominator_bounds n K M a u hpos ha hu aug C l).1
  have hac1 : alternativeConditionalLaw n K M a u aug ≪ intermediateConditionalLaw n K M a u aug := by
    apply fairLabelMeasure_absolutelyContinuous n
    intro l
    unfold intermediateDensity
    apply Finset.prod_pos
    intro C _
    exact lt_of_lt_of_le (by positivity) (component_denominator_bounds n K M a u hpos ha hu aug C l).2
  have hnon := conditional_activities_nonneg n K M a u ε L h aug
  by_cases hg : activityA n K M a u aug+activityB n K M a u aug ≤ 1/256
  · have ht := copula_conditional_tv_good n _ _ _ hac0 hac1 _ _ hnon.1 hnon.2 hg
      hc.2.2.2.2.2.1 hc.2.2.2.2.2.2
    have hr : Real.sqrt (activityA n K M a u aug+activityB n K M a u aug) ≤ 1/16 := by
      have := Real.sqrt_le_sqrt hg
      have hs : Real.sqrt (1/256 : ℝ) = 1/16 := by
        nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 1/256 by norm_num),
          Real.sqrt_nonneg (1/256:ℝ)]
      rwa [hs] at this
    exact (ht.trans hr).trans (by nlinarith [hnon.1, hnon.2])
  · have ht := Causalean.Stat.tvDist_le_one (μ := nullConditionalLaw n K M a u aug)
      (ν := alternativeConditionalLaw n K M a u aug)
    exact ht.trans (by linarith)

/-- Integrating an almost-sure conditional TV envelope bounds the joint common-design law. This statement assumes [the hf condition](hyp:hf), [the henv condition](hyp:henv). [This is the stated conclusion](goal). -/
-- @node: copula_compProd_tv_of_envelope
lemma copula_compProd_tv_of_envelope {D E : Type*} [MeasurableSpace D] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (P Q : Kernel D E)
    [IsMarkovKernel P] [IsMarkovKernel Q] (f : D → ℝ) (hf : Integrable f μ)
    (henv : ∀ᵐ x ∂μ, Causalean.Stat.tvDist (P x) (Q x) ≤ f x) :
    Causalean.Stat.tvDist (μ ⊗ₘ P) (μ ⊗ₘ Q) ≤ ∫ x, f x ∂μ := by
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  intro S
  have hsection (κ : Kernel D E) [IsMarkovKernel κ] :
      (μ ⊗ₘ κ).real S.1 = ∫ x, (κ x).real (Prod.mk x ⁻¹' S.1) ∂μ := by
    rw [measureReal_def, Measure.compProd_apply S.2]
    exact (integral_toReal (Kernel.measurable_kernel_prodMk_left S.2).aemeasurable
      (Filter.Eventually.of_forall (fun x => measure_lt_top (κ x) _))).symm
  have hi (κ : Kernel D E) [IsMarkovKernel κ] :
      Integrable (fun x => (κ x).real (Prod.mk x ⁻¹' S.1)) μ := by
    apply Integrable.of_bound
      (Kernel.measurable_kernel_prodMk_left S.2).ennreal_toReal.aestronglyMeasurable 1
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact (measureReal_mono (Set.subset_univ _) (measure_ne_top (κ x) _)).trans
      (by simp)
  rw [hsection P, hsection Q, ← integral_sub (hi P) (hi Q)]
  calc
    _ ≤ ∫ x, |(P x).real (Prod.mk x ⁻¹' S.1)-(Q x).real (Prod.mk x ⁻¹' S.1)| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, f x ∂μ := by
      apply integral_mono_ae ((hi P).sub (hi Q)).abs hf
      filter_upwards [henv] with x hx
      exact (Causalean.Stat.abs_measureReal_sub_le_tvDist
        (S.2.preimage measurable_prodMk_left)).trans hx

/-- The two occupancy budgets imply TV at most 17/256 for the actual augmented laws. This statement assumes [the hK condition](hyp:hK), [the hP0 condition](hyp:hP0), [the hP1 condition](hyp:hP1), [the hsmall condition](hyp:hsmall). [This is the stated conclusion](goal). -/
-- @node: copula_augmented_tv_budget
lemma copula_augmented_tv_budget (n K M : ℕ) (a u ε L : ℝ)
    (h : CopulaDomain n K M a u ε L) (hK : 2^40*n ≤ K)
    (P0 P1 : Kernel (Augmentation n K) (Labels n))
    (hP0 : ∀ aug, P0 aug = nullConditionalLaw n K M a u aug)
    (hP1 : ∀ aug, P1 aug = alternativeConditionalLaw n K M a u aug)
    [IsProbabilityMeasure (commonAugmentation n K M ε)]
    [IsMarkovKernel P0] [IsMarkovKernel P1]
    (hsmall : activityBudgetA n K a u ε+activityBudgetB n K M a u ε ≤ (2:ℝ)^(-16:ℤ)) :
    Causalean.Stat.tvDist (commonAugmentation n K M ε ⊗ₘ P0)
      (commonAugmentation n K M ε ⊗ₘ P1) ≤ 17/256 := by
  have hb := component_occupancy_budgets n K M a u ε L h hK
  have hiA := hb.2.2.1
  have hiB := hb.2.2.2.1
  have hi : Integrable (fun aug => 1/16+256*(activityA n K M a u aug+activityB n K M a u aug))
      (commonAugmentation n K M ε) :=
    (integrable_const _).add ((hiA.add hiB).const_mul 256)
  have he := copula_conditional_tv_envelope n K M a u ε L h
  simp_rw [← hP0, ← hP1] at he
  have ht := copula_compProd_tv_of_envelope (commonAugmentation n K M ε) P0 P1 _ hi he
  have hint : (∫ aug, 1/16+256*(activityA n K M a u aug+activityB n K M a u aug)
      ∂commonAugmentation n K M ε) =
      1/16+256*((∫ aug, activityA n K M a u aug ∂commonAugmentation n K M ε)+
        ∫ aug, activityB n K M a u aug ∂commonAugmentation n K M ε) := by
    integral_linearity
    simp
  rw [hint] at ht
  norm_num at hsmall
  linarith [hb.2.2.2.2.1, hb.2.2.2.2.2]

/-- The projection to all original records is measurable, including both zero and signed marks. [This is the stated conclusion](goal). -/
-- @node: measurable_augmentedObserve
@[fun_prop] lemma measurable_augmentedObserve (n K : ℕ) (L : ℝ) :
    Measurable (augmentedObserve n K L) := by
  unfold augmentedObserve
  apply measurable_pi_lambda
  intro i
  apply Measurable.prodMk (by fun_prop)
  apply Measurable.prodMk (by fun_prop)
  apply Measurable.ite
  · exact (measurableSet_singleton true).preimage (by fun_prop)
  · fun_prop
  · fun_prop

/-- Forgetting auxiliary design and disclosure cannot increase total variation. This statement assumes [the hg condition](hyp:hg). [This is the stated conclusion](goal). -/
-- @node: copula_tv_map_le
lemma copula_tv_map_le {D E : Type*} [MeasurableSpace D] [MeasurableSpace E]
    (P Q : Measure D) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (g : D → E) (hg : Measurable g) :
    Causalean.Stat.tvDist (P.map g) (Q.map g) ≤ Causalean.Stat.tvDist P Q := by
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  intro S
  simp only [measureReal_def, Measure.map_apply hg S.2]
  exact Causalean.Stat.abs_measureReal_sub_le_tvDist (S.2.preimage hg)

end CausalSmith.Stat.FinitepHomogeneityDensegamma

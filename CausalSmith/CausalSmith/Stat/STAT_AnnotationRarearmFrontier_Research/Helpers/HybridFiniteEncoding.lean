module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.BaselinePoolEncoding

/-!
Ordered three-pool count readback and conditional averaging for the finite hybrid rule.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram

/-- The ideal ordered statistic retains the outcome, pilot, and factorial pools separately. -/
-- @node: hybridOrderedPrefixStatistic
noncomputable def hybridOrderedPrefixStatistic {d : Nat} (tun : HybridTuning)
    (s : FiniteSample (Obs d) × FiniteSample (AuxObs d) × FiniteSample (AuxObs d)) : Real :=
  let Z := fun a j => finiteSampleHistogram s.1.points (j,a,true)
  let J := fun a j => finiteSampleHistogram s.2.1.points (j,a)
  let K := fun a j => finiteSampleHistogram s.2.2.points (j,a)
  max (-1) (min 1 (∑ j : Fin d, (
    hybridCellValue tun.L tun.B tun.k0 tun.u tun.t (Z true j) (J true j)
      (K true j) (K false j) -
    hybridCellValue tun.L tun.B tun.k0 tun.u tun.t (Z false j) (J false j)
      (K false j) (K true j))))

/-- [Under the stated inputs and conditions](hyp:eps,s,h0,hp,hap,hf,haf,n,m,d,r0,rp,rf), Ordered histograms recover exactly the three original array counters.  This gives [the stated result](goal).-/
-- @node: hybrid_prefix_statistic_eq_ordered
lemma hybrid_prefix_statistic_eq_ordered {n m d : Nat} (eps : Real) (s : Sample n m d)
    (r0 rp rf : Nat)
    (h0 : 0 + r0 ≤ n)
    (hp : (hybridTuning n m eps).h0 + min rp (hybridTuning n m eps).hp ≤ n)
    (hap : 0 + (rp - (hybridTuning n m eps).hp) ≤ m)
    (hf : (hybridTuning n m eps).h0 + (hybridTuning n m eps).hp +
      min rf (hybridTuning n m eps).hf ≤ n)
    (haf : m / 2 + (rf - (hybridTuning n m eps).hf) ≤ m) :
    hybridPrefixStatistic eps r0 rp rf s =
      hybridOrderedPrefixStatistic (hybridTuning n m eps)
        (baselineBlockPrefix s.1 0 r0 h0,
          baselineAuxiliaryPrefix s (hybridTuning n m eps).h0
            (hybridTuning n m eps).hp 0 rp hp hap,
          baselineAuxiliaryPrefix s ((hybridTuning n m eps).h0 +
            (hybridTuning n m eps).hp) (hybridTuning n m eps).hf (m / 2) rf hf haf) := by
  unfold hybridOrderedPrefixStatistic
  simp only [baseline_labeled_block_histogram, baseline_pooled_arm_histogram]
  rfl

/-- [Under the stated hypotheses](hyp:hr0,hrp,hrf), The count bridge applies to every retained triple, with no extra array-bound premises.  This gives [the stated result](goal). -/
-- @node: hybrid_valid_prefix_statistic_eq_ordered
lemma hybrid_valid_prefix_statistic_eq_ordered {n m d : Nat} (eps : Real)
    (s : Sample n m d) (r0 rp rf : Nat)
    (hr0 : r0 ≤ (hybridTuning n m eps).h0)
    (hrp : rp ≤ (hybridTuning n m eps).Mp)
    (hrf : rf ≤ (hybridTuning n m eps).Mf) :
    ∃ (h0 : 0 + r0 ≤ n)
      (hp : (hybridTuning n m eps).h0 + min rp (hybridTuning n m eps).hp ≤ n)
      (hap : 0 + (rp - (hybridTuning n m eps).hp) ≤ m)
      (hf : (hybridTuning n m eps).h0 + (hybridTuning n m eps).hp +
        min rf (hybridTuning n m eps).hf ≤ n)
      (haf : m / 2 + (rf - (hybridTuning n m eps).hf) ≤ m),
    hybridPrefixStatistic eps r0 rp rf s =
      hybridOrderedPrefixStatistic (hybridTuning n m eps)
        (baselineBlockPrefix s.1 0 r0 h0,
          baselineAuxiliaryPrefix s (hybridTuning n m eps).h0
            (hybridTuning n m eps).hp 0 rp hp hap,
          baselineAuxiliaryPrefix s ((hybridTuning n m eps).h0 +
            (hybridTuning n m eps).hp) (hybridTuning n m eps).hf (m / 2) rf hf haf) := by
  have h0 : 0 + r0 ≤ n := by dsimp [hybridTuning] at hr0; omega
  have hp : (hybridTuning n m eps).h0 + min rp (hybridTuning n m eps).hp ≤ n := by
    dsimp [hybridTuning]; omega
  have hap : 0 + (rp - (hybridTuning n m eps).hp) ≤ m := by
    dsimp [hybridTuning] at hrp ⊢; omega
  have hf : (hybridTuning n m eps).h0 + (hybridTuning n m eps).hp +
      min rf (hybridTuning n m eps).hf ≤ n := by dsimp [hybridTuning]; omega
  have haf : m / 2 + (rf - (hybridTuning n m eps).hf) ≤ m := by
    dsimp [hybridTuning] at hrf ⊢; omega
  exact ⟨h0, hp, hap, hf, haf, hybrid_prefix_statistic_eq_ordered eps s r0 rp rf
    h0 hp hap hf haf⟩

/-- [Under the stated inputs and conditions](hyp:F,u,tp,t,h,p,f), Integrating a capped triple gives the exact product of the three Poisson weights.  This gives [the stated result](goal).-/
-- @node: hybrid_truncated_poisson_integral
lemma hybrid_truncated_poisson_integral (u tp t : NNReal) (h p f : Nat)
    (F : Nat → Nat → Nat → Real) :
    (∫ k : Nat × Nat × Nat, if k.1 ≤ h ∧ k.2.1 ≤ p ∧ k.2.2 ≤ f then
      F k.1 k.2.1 k.2.2 else 0
      ∂((poissonMeasure u).prod ((poissonMeasure tp).prod (poissonMeasure t)))) =
      ∑ r0 ∈ Finset.range (h + 1), ∑ rp ∈ Finset.range (p + 1),
        ∑ rf ∈ Finset.range (f + 1),
          Real.exp (-(u : Real) - (tp : Real) - (t : Real)) *
            ((u : Real) ^ r0 / (r0.factorial : Real)) *
            ((tp : Real) ^ rp / (rp.factorial : Real)) *
            ((t : Real) ^ rf / (rf.factorial : Real)) * F r0 rp rf := by
  classical
  let s := (Finset.range (h + 1)).product
    ((Finset.range (p + 1)).product (Finset.range (f + 1)))
  have hind : (fun k : Nat × Nat × Nat =>
      if k.1 ≤ h ∧ k.2.1 ≤ p ∧ k.2.2 ≤ f then F k.1 k.2.1 k.2.2 else 0) =
      (s : Set (Nat × Nat × Nat)).indicator (fun k => F k.1 k.2.1 k.2.2) := by
    funext k
    simp [s, Set.indicator]
  rw [hind, integral_indicator s.measurableSet, setIntegral_finset s IntegrableOn.finset]
  dsimp only [s]
  simp only [Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro r0 _
  apply Finset.sum_congr rfl
  intro rp _
  apply Finset.sum_congr rfl
  intro rf _
  have hmass : ((poissonMeasure u).prod
      ((poissonMeasure tp).prod (poissonMeasure t))).real {(r0,rp,rf)} =
      (poissonMeasure u).real {r0} *
        ((poissonMeasure tp).real {rp} * (poissonMeasure t).real {rf}) := by
    simp only [Measure.real_def, ← Set.singleton_prod_singleton,
      Measure.prod_prod, ENNReal.toReal_mul]
  rw [smul_eq_mul, hmass, poissonMeasure_real_singleton,
    poissonMeasure_real_singleton, poissonMeasure_real_singleton]
  rw [show -(u : Real) - (tp : Real) - (t : Real) =
    -(u : Real) + -(tp : Real) + -(t : Real) by ring, Real.exp_add, Real.exp_add]
  ring

/-- Each Poisson request is independent, with the exact public pool intensity. -/
-- @node: hybridRequestLaw
noncomputable def hybridRequestLaw (n m : Nat) (eps : Real) : Measure (Nat × Nat × Nat) :=
  (poissonMeasure ((hybridTuning n m eps).h0 / 8 : NNReal)).prod
    ((poissonMeasure ((hybridTuning n m eps).Mp / 8 : NNReal)).prod
      (poissonMeasure ((hybridTuning n m eps).Mf / 8 : NNReal)))

/-- The independent request law has total mass one, also when a pool is empty. -/
-- @node: hybridRequestLaw_probability
instance hybridRequestLaw_probability (n m : Nat) (eps : Real) :
    IsProbabilityMeasure (hybridRequestLaw n m eps) := by
  unfold hybridRequestLaw
  infer_instance

/-- Overflow in any of the three pools returns zero. -/
-- @node: hybridCappedArrayStatistic
noncomputable def hybridCappedArrayStatistic {n m d : Nat} (eps : Real)
    (s : Sample n m d) (k : Nat × Nat × Nat) : Real :=
  let tun := hybridTuning n m eps
  if k.1 ≤ tun.h0 ∧ k.2.1 ≤ tun.Mp ∧ k.2.2 ≤ tun.Mf then
    hybridPrefixStatistic eps k.1 k.2.1 k.2.2 s else 0

/-- [Under the stated inputs and conditions](hyp:eps,s,k,n,m,d), Both valid-prefix clipping and zero overflow lie in the required interval.  This gives [the stated result](goal).-/
-- @node: hybrid_capped_array_mem_Icc
lemma hybrid_capped_array_mem_Icc {n m d : Nat} (eps : Real) (s : Sample n m d)
    (k : Nat × Nat × Nat) : hybridCappedArrayStatistic eps s k ∈ Set.Icc (-1) 1 := by
  unfold hybridCappedArrayStatistic
  dsimp only
  split_ifs
  · exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  · norm_num

/-- [Under the stated inputs and conditions](hyp:eps,s,hS,n,m,d), The estimator's finite sum is exactly conditional averaging of the capped statistic.  This gives [the stated result](goal).-/
-- @node: hybrid_estimator_eq_poisson_integral
lemma hybrid_estimator_eq_poisson_integral {n m d : Nat} (eps : Real) (s : Sample n m d)
    (hS : Real.exp 4096 ≤ (n : Real) * eps) :
    hybridEstimator n m d eps s =
      ∫ k, hybridCappedArrayStatistic eps s k ∂hybridRequestLaw n m eps := by
  unfold hybridRequestLaw hybridCappedArrayStatistic
  dsimp only
  rw [hybrid_truncated_poisson_integral _ _ _ _ _ _
    (fun r0 rp rf => hybridPrefixStatistic eps r0 rp rf s)]
  simp only [hybridEstimator, if_neg (not_lt.mpr hS), hybridTuning,
    NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_ofNat]

/-- [Under the stated inputs and conditions](hyp:eps,s,hS,n,theta,m,d), Jensen's inequality contracts the squared loss at each fixed original sample.  This gives [the stated result](goal).-/
-- @node: hybrid_averaging_sq_loss_le
lemma hybrid_averaging_sq_loss_le {n m d : Nat} (eps : Real) (s : Sample n m d)
    (hS : Real.exp 4096 ≤ (n : Real) * eps) (theta : Real) :
    (hybridEstimator n m d eps s - theta) ^ 2 ≤
      ∫ k, (hybridCappedArrayStatistic eps s k - theta) ^ 2
        ∂hybridRequestLaw n m eps := by
  have hm : Measurable (hybridCappedArrayStatistic eps s) := by fun_prop
  have hb : Causalean.Stat.UniformlyBounded (hybridCappedArrayStatistic eps s) :=
    ⟨1, by norm_num, fun k => abs_le.mpr (hybrid_capped_array_mem_Icc eps s k)⟩
  have hj := Causalean.Stat.sqLoss_kernelMean_le
    (Kernel.const Unit (hybridRequestLaw n m eps)) hm hb theta ()
  rw [hybrid_estimator_eq_poisson_integral eps s hS]
  simpa only [Causalean.Stat.kernelMean, Kernel.const_apply] using hj

/-- [Under the stated inputs and conditions](hyp:eps,P,hS,n,m,d), Conditional averaging contracts risk under the original product data law.  This gives [the stated result](goal).-/
-- @node: hybrid_averaging_sq_risk_le
lemma hybrid_averaging_sq_risk_le {n m d : Nat} (eps : Real) (P : DiscreteLaw d)
    (hS : Real.exp 4096 ≤ (n : Real) * eps) :
    Causalean.Stat.sqRisk (annotationLaw P n m) (hybridEstimator n m d eps)
      (ateFunctional P) ≤
    Causalean.Stat.sqRisk ((annotationLaw P n m).prod (hybridRequestLaw n m eps))
      (fun z => hybridCappedArrayStatistic eps z.1 z.2) (ateFunctional P) := by
  let : IsProbabilityMeasure (annotationLaw P n m) := by
    unfold annotationLaw labeledProductLaw auxProductLaw
    infer_instance
  have htheta := ateFunctional_mem_Icc P
  have hm : Measurable (fun z : Sample n m d × (Nat × Nat × Nat) =>
      (hybridCappedArrayStatistic eps z.1 z.2 - ateFunctional P) ^ 2) := by fun_prop
  have hi : Integrable (fun z : Sample n m d × (Nat × Nat × Nat) =>
      (hybridCappedArrayStatistic eps z.1 z.2 - ateFunctional P) ^ 2)
      ((annotationLaw P n m).prod (hybridRequestLaw n m eps)) := by
    apply Integrable.of_bound hm.aestronglyMeasurable 4
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hc := hybrid_capped_array_mem_Icc eps z.1 z.2
    nlinarith [hc.1, hc.2, htheta.1, htheta.2]
  unfold Causalean.Stat.sqRisk
  rw [integral_prod _ hi]
  exact integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) hi.integral_prod_left
    (Filter.Eventually.of_forall (fun s => hybrid_averaging_sq_loss_le eps s hS _))

/-- [Under the stated inputs and conditions](hyp:eps,P,n,m,d), The independent seed leaves the data-only hybrid rule's risk unchanged.  This gives [the stated result](goal).-/
-- @node: hybrid_ruleRisk_eq_sqRisk
lemma hybrid_ruleRisk_eq_sqRisk (n m d : Nat) (eps : Real) (P : DiscreteLaw d) :
    ruleRisk (liftRule (hybridEstimator n m d eps)) P =
      Causalean.Stat.sqRisk (annotationLaw P n m) (hybridEstimator n m d eps)
        (ateFunctional P) := by
  let : IsProbabilityMeasure seedLaw := ⟨by
    norm_num [seedLaw, Real.volume_Icc]⟩
  let : IsProbabilityMeasure (annotationLaw P n m) := by
    unfold annotationLaw labeledProductLaw auxProductLaw
    infer_instance
  have hm : Measurable (fun z : Sample n m d × Real =>
      (hybridEstimator n m d eps z.1 - ateFunctional P) ^ 2) := by fun_prop
  have hi : Integrable (fun z : Sample n m d × Real =>
      (hybridEstimator n m d eps z.1 - ateFunctional P) ^ 2)
      ((annotationLaw P n m).prod seedLaw) := by
    apply Integrable.of_bound hm.aestronglyMeasurable 4
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hc := hybridEstimator_mem_Icc n m d eps z.1
    have ht := ateFunctional_mem_Icc P
    nlinarith [hc.1, hc.2, ht.1, ht.2]
  unfold ruleRisk liftRule Causalean.Stat.sqRisk
  rw [integral_prod _ hi]
  simp

/-- [Under the stated inputs and conditions](hyp:eps,P,hS,n,m,d), The original rule risk is bounded by its unaveraged, zero-overflow prefix risk.  This gives [the stated result](goal).-/
-- @node: hybrid_ruleRisk_le_capped_array_risk
lemma hybrid_ruleRisk_le_capped_array_risk {n m d : Nat} (eps : Real) (P : DiscreteLaw d)
    (hS : Real.exp 4096 ≤ (n : Real) * eps) :
    ruleRisk (liftRule (hybridEstimator n m d eps)) P ≤
      Causalean.Stat.sqRisk ((annotationLaw P n m).prod (hybridRequestLaw n m eps))
        (fun z => hybridCappedArrayStatistic eps z.1 z.2) (ateFunctional P) := by
  rw [hybrid_ruleRisk_eq_sqRisk]
  exact hybrid_averaging_sq_risk_le eps P hS

end CausalSmith.Stat.AnnotationRarearmFrontier

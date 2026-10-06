module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.CommonMarginalCalibration
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.CommonMarginalPoissonPrior
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.ParametricCommonMarginalRecipe
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.ParametricLabelFloor
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Depoissonization
public import Causalean.Stat.Concentration.Chebyshev
public import Causalean.Stat.Concentration.Poisson.SelfNormalized.Chernoff
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.RandomScaleTransfer.Main
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram.HistogramReconstruction
public import Causalean.Stat.Minimax.FuzzyHypotheses
public import Causalean.Stat.Minimax.Mixture
public import Causalean.Stat.Minimax.TotalVariation

/-! Loss, clipping, and minimax-risk bridges for common-marginal transfer. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram
open Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.RandomScaleMinimaxTransfer

-- @node: helper:common-marginal-transfer-clip
/-- [the stated conditions](hyp:z) defines [the specified object](goal). -/
noncomputable def commonMarginalTransferClip (z : Real) : Real :=
  max (-1) (min 1 z)

-- @node: helper:common-marginal-transfer-loss
/-- [the stated conditions](hyp:eps) defines [the specified object](goal). -/
noncomputable def commonMarginalTransferLoss {d : Nat} (eps : Real) :
    DiscreteLaw d → Real → ENNReal := by
  classical
  exact fun P z =>
    if ModelClass d eps P then
      ENNReal.ofReal ((commonMarginalTransferClip z - ateFunctional P) ^ 2)
    else 0

-- @node: helper:common-marginal-fixed-kernel
/-- [the stated conditions](hyp:n,m,d) defines [the specified object](goal). -/
noncomputable def commonMarginalFixedKernel (n m d : Nat) :
    Kernel (DiscreteLaw d) (Sample n m d) where
  toFun P := annotationLaw P n m
  measurable' := measurable_from_top

-- @node: helper:common-marginal-transfer-loss-measurable
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma commonMarginalTransferLoss_measurable {d : Nat} (eps : Real) :
    Measurable (Function.uncurry (commonMarginalTransferLoss (d := d) eps)) := by
  have hat : Measurable (ateFunctional : DiscreteLaw d → Real) := measurable_from_top
  unfold commonMarginalTransferLoss Function.uncurry
  apply Measurable.ite
  · exact measurable_fst MeasurableSpace.measurableSet_top
  · apply ENNReal.measurable_ofReal.comp
    apply Measurable.pow_const
    exact (measurable_const.max (measurable_const.min measurable_snd)).sub
      (hat.comp measurable_fst)
  · exact measurable_const

-- @node: helper:common-marginal-transfer-loss-bound
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma commonMarginalTransferLoss_le_four {d : Nat} (eps : Real)
    (P : DiscreteLaw d) (z : Real) :
    commonMarginalTransferLoss eps P z ≤ (4 : ENNReal) := by
  unfold commonMarginalTransferLoss
  split_ifs with hP
  · rw [show (4 : ENNReal) = ENNReal.ofReal 4 by norm_num]
    apply ENNReal.ofReal_le_ofReal
    have hz0 : -1 ≤ commonMarginalTransferClip z := le_max_left _ _
    have hz1 : commonMarginalTransferClip z ≤ 1 :=
      max_le (by norm_num) (min_le_left _ _)
    have ht := ateFunctional_mem_Icc_neg_one_one P hP.overlap
    have hd : |commonMarginalTransferClip z - ateFunctional P| ≤ 2 :=
      abs_le.2 ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hs : (commonMarginalTransferClip z - ateFunctional P) ^ 2 ≤
        (2 : Real) ^ 2 := (sq_le_sq).2 (by simpa using hd)
    norm_num at hs ⊢
    exact hs
  · simp

-- @node: helper:common-marginal-clipped-loss-lintegral
/-- [the stated conditions](hyp:hP,hrule) establishes [the stated conclusion](goal). -/
lemma commonMarginal_clippedLoss_lintegral {n m d : Nat} {eps : Real}
    (P : DiscreteLaw d) (hP : ModelClass d eps P)
    (rule : Sample n m d → Real) (hrule : Measurable rule) :
    decisionRisk (commonMarginalFixedKernel n m d)
        (commonMarginalTransferLoss eps) rule P =
      ENNReal.ofReal (twoSampleMSE (annotationLaw P n m)
        (fun z => commonMarginalTransferClip (rule z)) (ateFunctional P)) := by
  classical
  letI : IsProbabilityMeasure (annotationLaw P n m) := by
    unfold annotationLaw labeledProductLaw auxProductLaw
    infer_instance
  have hclip : Measurable (fun z => commonMarginalTransferClip (rule z)) := by
    exact (measurable_const.max (measurable_const.min hrule))
  have ht := ateFunctional_mem_Icc_neg_one_one P hP.overlap
  have hclip_mem (z : Sample n m d) :
      commonMarginalTransferClip (rule z) ∈ Set.Icc (-1 : Real) 1 := by
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_left _ _)
  have hsqInt : Integrable
      (fun z => (commonMarginalTransferClip (rule z) - ateFunctional P) ^ 2)
      (annotationLaw P n m) := by
    apply Integrable.of_bound
      ((hclip.sub measurable_const).pow_const 2).aestronglyMeasurable 4
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (commonMarginalTransferClip (rule z) - ateFunctional P) ^ 2 ≤ 4
    rcases hclip_mem z with ⟨hz0, hz1⟩
    rcases ht with ⟨ht0, ht1⟩
    nlinarith [sq_nonneg (commonMarginalTransferClip (rule z) - ateFunctional P - 2),
      sq_nonneg (commonMarginalTransferClip (rule z) - ateFunctional P + 2)]
  unfold decisionRisk commonMarginalFixedKernel commonMarginalTransferLoss
  simp only [if_pos hP]
  change (∫⁻ z, ENNReal.ofReal
      ((commonMarginalTransferClip (rule z) - ateFunctional P) ^ 2)
      ∂annotationLaw P n m) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hsqInt
    (Filter.Eventually.of_forall fun z => sq_nonneg _)]
  rfl

-- @node: helper:common-marginal-transfer-clip-risk
/-- [the stated conditions](hyp:htheta) establishes [the stated conclusion](goal). -/
lemma commonMarginalTransferClip_sq_sub_le (z theta : Real)
    (htheta : theta ∈ Set.Icc (-1 : Real) 1) :
    (commonMarginalTransferClip z - theta) ^ 2 ≤ (z - theta) ^ 2 := by
  unfold commonMarginalTransferClip
  by_cases hz1 : z ≤ 1
  · rw [min_eq_right hz1]
    by_cases hzm : -1 ≤ z
    · rw [max_eq_right hzm]
    · rw [max_eq_left (le_of_not_ge hzm)]
      nlinarith [htheta.1, sq_nonneg (z - theta)]
  · rw [min_eq_left (le_of_not_ge hz1), max_eq_right (by norm_num)]
    nlinarith [htheta.2, sq_nonneg (z - theta)]

-- @node: helper:common-marginal-clipping-mse
/-- [the stated conditions](hyp:hP) establishes [the stated conclusion](goal). -/
lemma commonMarginal_clipping_mse_le {eps : Real} {n m d : Nat}
    (P : DiscreteLaw d) (hP : ModelClass d eps P)
    (rule : Sample n m d → Real) :
    twoSampleMSE (annotationLaw P n m)
        (fun z => commonMarginalTransferClip (rule z)) (ateFunctional P) ≤
      twoSampleMSE (annotationLaw P n m) rule (ateFunctional P) := by
  letI : IsProbabilityMeasure (annotationLaw P n m) := by
    unfold annotationLaw labeledProductLaw auxProductLaw
    infer_instance
  unfold twoSampleMSE
  have hleft : Integrable
      (fun z => (commonMarginalTransferClip (rule z) - ateFunctional P) ^ 2)
      (annotationLaw P n m) := (MemLp.of_discrete (p := 1)).integrable (by norm_num)
  have hright : Integrable (fun z => (rule z - ateFunctional P) ^ 2)
      (annotationLaw P n m) := (MemLp.of_discrete (p := 1)).integrable (by norm_num)
  apply integral_mono hleft hright
  intro z
  exact commonMarginalTransferClip_sq_sub_le _ _
    (ateFunctional_mem_Icc_neg_one_one P hP.overlap)

-- @node: helper:common-marginal-class-gated-worst-case
/-- [the stated conditions](hyp:hrule) establishes [the stated conclusion](goal). -/
lemma commonMarginal_classGated_worstCase_le {n m d : Nat} {eps : Real}
    (rule : Sample n m d → Real) (hrule : Measurable rule) :
    worstCaseDecisionRisk (commonMarginalFixedKernel n m d)
        (commonMarginalTransferLoss eps) rule ≤
      ⨆ P : ClassLaw d eps,
        ENNReal.ofReal (twoSampleMSE (annotationLaw P.1 n m)
          rule (ateFunctional P.1)) := by
  classical
  unfold worstCaseDecisionRisk
  apply iSup_le
  intro P
  by_cases hP : ModelClass d eps P
  · rw [commonMarginal_clippedLoss_lintegral P hP rule hrule]
    refine (ENNReal.ofReal_le_ofReal
      (commonMarginal_clipping_mse_le P hP rule)).trans ?_
    exact le_iSup (fun Q : ClassLaw d eps =>
      ENNReal.ofReal (twoSampleMSE (annotationLaw Q.1 n m)
        rule (ateFunctional Q.1))) ⟨P, hP⟩
  · unfold decisionRisk commonMarginalTransferLoss commonMarginalFixedKernel
    simp [hP]

-- @node: helper:common-marginal-mse-bounded-above
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma commonMarginal_mse_bddAbove {n m d : Nat} {eps : Real}
    (rule : Sample n m d → Real) :
    BddAbove (Set.range fun P : ClassLaw d eps =>
      twoSampleMSE (annotationLaw P.1 n m) rule (ateFunctional P.1)) := by
  let M : Real := ∑ z : Sample n m d, |rule z| + 1
  refine ⟨M ^ 2, ?_⟩
  rintro value ⟨P, rfl⟩
  letI : IsProbabilityMeasure (annotationLaw P.1 n m) := by
    unfold annotationLaw labeledProductLaw auxProductLaw
    infer_instance
  have hM0 : 0 ≤ M := by
    dsimp [M]
    positivity
  have hruleM (z : Sample n m d) : |rule z| + 1 ≤ M := by
    have hz : |rule z| ≤ ∑ w : Sample n m d, |rule w| := by
      exact Finset.single_le_sum (f := fun w : Sample n m d => |rule w|)
        (fun w _ => abs_nonneg (rule w)) (Finset.mem_univ z)
    dsimp [M]
    linarith
  have hpoint (z : Sample n m d) :
      (rule z - ateFunctional P.1) ^ 2 ≤ M ^ 2 := by
    have ht := ateFunctional_mem_Icc_neg_one_one P.1 P.2.overlap
    have habs : |rule z - ateFunctional P.1| ≤ M := by
      calc
        |rule z - ateFunctional P.1| ≤ |rule z| + |ateFunctional P.1| :=
          abs_sub _ _
        _ ≤ M := by
          have hat : |ateFunctional P.1| ≤ 1 := abs_le.2 ht
          linarith [hruleM z, hat]
    rw [sq_le_sq, abs_of_nonneg hM0]
    exact habs
  unfold twoSampleMSE
  calc
    ∫ z, (rule z - ateFunctional P.1) ^ 2 ∂annotationLaw P.1 n m ≤
        ∫ _z, M ^ 2 ∂annotationLaw P.1 n m := by
      apply integral_mono
      · exact (MemLp.of_discrete (p := 1)).integrable (by norm_num)
      · exact integrable_const _
      · exact hpoint
    _ = M ^ 2 := by simp

-- @node: helper:common-marginal-class-gated-minimax
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma commonMarginal_classGated_minimax_le (n m d : Nat) (eps : Real) :
    minimaxDecisionRisk (commonMarginalFixedKernel n m d)
        (commonMarginalTransferLoss eps) ≤
      ENNReal.ofReal (minimaxRisk n m d eps) := by
  letI : Nonempty {f : Sample n m d → Real // Measurable f} :=
    ⟨⟨fun _ => 0, measurable_const⟩⟩
  unfold minimaxDecisionRisk minimaxRisk
  rw [ENNReal.ofReal_iInf]
  apply iInf_mono
  intro est
  refine (commonMarginal_classGated_worstCase_le est.1 est.2).trans ?_
  apply iSup_le
  intro P
  apply ENNReal.ofReal_le_ofReal
  exact le_ciSup (commonMarginal_mse_bddAbove est.1) P

-- @node: helper:common-marginal-class-gated-rulewise-reverse
/-- [the stated conditions](hyp:hrule) establishes [the stated conclusion](goal). -/
lemma commonMarginal_ofReal_minimax_le_classGated_worstCase
    (n m d : Nat) (eps : Real)
    [Nonempty (ClassLaw d eps)]
    (rule : Sample n m d → Real) (hrule : Measurable rule) :
    ENNReal.ofReal (minimaxRisk n m d eps) ≤
      worstCaseDecisionRisk (commonMarginalFixedKernel n m d)
        (commonMarginalTransferLoss eps) rule := by
  let clipped : Sample n m d → Real :=
    fun z => commonMarginalTransferClip (rule z)
  have hclipped : Measurable clipped :=
    measurable_const.max (measurable_const.min hrule)
  have hmin : minimaxRisk n m d eps ≤
      ⨆ P : ClassLaw d eps,
        twoSampleMSE (annotationLaw P.1 n m) clipped (ateFunctional P.1) := by
    unfold minimaxRisk
    have hb : BddBelow (Set.range (fun est :
        {f : Sample n m d → Real // Measurable f} =>
      ⨆ P : ClassLaw d eps,
        twoSampleMSE (annotationLaw P.1 n m) est.1 (ateFunctional P.1))) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨est, rfl⟩
      have hmse : 0 ≤ twoSampleMSE
          (annotationLaw (Classical.arbitrary (ClassLaw d eps)).1 n m)
          est.1 (ateFunctional (Classical.arbitrary (ClassLaw d eps)).1) := by
        unfold twoSampleMSE
        exact integral_nonneg (fun z => sq_nonneg _)
      exact hmse.trans (le_ciSup (commonMarginal_mse_bddAbove est.1)
        (Classical.arbitrary _))
    exact ciInf_le hb ⟨clipped, hclipped⟩
  have hsup : ENNReal.ofReal (⨆ P : ClassLaw d eps,
      twoSampleMSE (annotationLaw P.1 n m) clipped (ateFunctional P.1)) ≤
      worstCaseDecisionRisk (commonMarginalFixedKernel n m d)
        (commonMarginalTransferLoss eps) rule := by
    by_cases hw : worstCaseDecisionRisk (commonMarginalFixedKernel n m d)
        (commonMarginalTransferLoss eps) rule = ⊤
    · simp [hw]
    rw [ENNReal.ofReal_le_iff_le_toReal hw]
    apply ciSup_le
    intro P
    have hterm : ENNReal.ofReal
        (twoSampleMSE (annotationLaw P.1 n m) clipped (ateFunctional P.1)) ≤
        worstCaseDecisionRisk (commonMarginalFixedKernel n m d)
          (commonMarginalTransferLoss eps) rule := by
      rw [← commonMarginal_clippedLoss_lintegral P.1 P.2 rule hrule]
      unfold worstCaseDecisionRisk
      exact le_iSup (fun Q : DiscreteLaw d =>
        decisionRisk (commonMarginalFixedKernel n m d)
          (commonMarginalTransferLoss eps) rule Q) P.1
    rwa [ENNReal.ofReal_le_iff_le_toReal hw] at hterm
  calc
    ENNReal.ofReal (minimaxRisk n m d eps) ≤
        ENNReal.ofReal (⨆ P : ClassLaw d eps,
          twoSampleMSE (annotationLaw P.1 n m) clipped (ateFunctional P.1)) :=
      ENNReal.ofReal_le_ofReal hmin
    _ ≤ worstCaseDecisionRisk (commonMarginalFixedKernel n m d)
          (commonMarginalTransferLoss eps) rule := hsup

-- @node: helper:common-marginal-class-gated-minimax-reverse
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma commonMarginal_ofReal_minimax_le_classGated (n m d : Nat) (eps : Real)
    [Nonempty (ClassLaw d eps)] :
    ENNReal.ofReal (minimaxRisk n m d eps) ≤
      minimaxDecisionRisk (commonMarginalFixedKernel n m d)
        (commonMarginalTransferLoss eps) := by
  unfold minimaxDecisionRisk
  apply le_iInf
  intro rule
  exact commonMarginal_ofReal_minimax_le_classGated_worstCase
    n m d eps rule.1 rule.2

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.CommonMarginalTransferReconstruction

/-! Mass, target, event, tail, and fuzzy-hypothesis bounds for common-marginal transfer. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram
open Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.RandomScaleMinimaxTransfer

-- @node: helper:common-marginal-mass-concentration
/-- [the stated conditions](hyp:hb) establishes [the stated conclusion](goal). -/
lemma commonMarginal_mass_concentration {eps : Real}
    {calibration : CommonMarginalCalibration eps}
    {n m d L k : Nat} {B a u v C rho : Real}
    (R : CommonMarginalRecipe calibration n m d L B a k)
    (hb : CommonMarginalBounds R u v calibration.dualGap C rho) :
    (R.generator {w | (1 / 2 : Real) < |R.rawTotalMass w - 1|}).toReal ≤
      4 * C * k * B * a := by
  letI : IsProbabilityMeasure R.generator := R.generatorProbability
  have hvar : variance R.rawTotalMass R.generator ≤ C * k * B * a := by
    rw [variance_eq_integral hb.mass_memLp_two.1.aemeasurable]
    exact hb.massVariance
  have h := Causalean.Stat.Concentration.probability_abs_sub_mean_gt_le
    R.generator R.rawTotalMass 1 (C * k * B * a) (1 / 2)
    hb.mass_memLp_two (by norm_num) hb.massMean hvar
  convert h using 1 <;> ring

-- @node: helper:common-marginal-target-concentration
/-- [the stated conditions](hyp:hb,ht) establishes [the stated conclusion](goal). -/
lemma commonMarginal_target_concentration {eps : Real}
    {calibration : CommonMarginalCalibration eps}
    {n m d L k : Nat} {B a u v C rho t : Real}
    (R : CommonMarginalRecipe calibration n m d L B a k)
    (hb : CommonMarginalBounds R u v calibration.dualGap C rho)
    (branch : Bool) (ht : 0 < t) :
    (R.generator {w | t < |R.rawTarget branch w - rawPriorCenter R branch|}).toReal ≤
      C * k * B * a / t ^ 2 := by
  letI : IsProbabilityMeasure R.generator := R.generatorProbability
  have hvar : variance (R.rawTarget branch) R.generator ≤ C * k * B * a := by
    rw [variance_eq_integral (hb.target_memLp_two branch).1.aemeasurable]
    have hbranch : generatorVariance R (R.rawTarget branch) ≤
        max (generatorVariance R (R.rawTarget false))
          (generatorVariance R (R.rawTarget true)) := by
      cases branch
      · exact le_max_left _ _
      · exact le_max_right _ _
    exact hbranch.trans hb.targetVariance
  apply Causalean.Stat.Concentration.probability_abs_sub_mean_gt_le
    R.generator (R.rawTarget branch) (rawPriorCenter R branch)
      (C * k * B * a) t (hb.target_memLp_two branch) ht
  · rfl
  · exact hvar

-- @node: helper:common-marginal-mass-concentration-at
/-- [the stated conditions](hyp:hb,ht) establishes [the stated conclusion](goal). -/
lemma commonMarginal_mass_concentration_at {eps : Real}
    {calibration : CommonMarginalCalibration eps}
    {n m d L k : Nat} {B a u v C rho t : Real}
    (R : CommonMarginalRecipe calibration n m d L B a k)
    (hb : CommonMarginalBounds R u v calibration.dualGap C rho)
    (ht : 0 < t) :
    (R.generator {w | t < |R.rawTotalMass w - 1|}).toReal ≤
      C * k * B * a / t ^ 2 := by
  letI : IsProbabilityMeasure R.generator := R.generatorProbability
  have hvar : variance R.rawTotalMass R.generator ≤ C * k * B * a := by
    rw [variance_eq_integral hb.mass_memLp_two.1.aemeasurable]
    exact hb.massVariance
  apply Causalean.Stat.Concentration.probability_abs_sub_mean_gt_le
    R.generator R.rawTotalMass 1 (C * k * B * a) t
      hb.mass_memLp_two ht hb.massMean hvar

-- @node: helper:common-marginal-prior-scale-tail
/-- [the stated conditions](hyp:hb) establishes [the stated conclusion](goal). -/
lemma commonMarginal_prior_scale_tail {eps : Real}
    {calibration : CommonMarginalCalibration eps}
    {n m d L k : Nat} {B a u v C rho : Real}
    (R : CommonMarginalRecipe calibration n m d L B a k)
    (hb : CommonMarginalBounds R u v calibration.dualGap C rho)
    (branch : Bool) :
    ((commonMarginalRecipePriorOf R branch)
      {P | Real.toNNReal (R.rawScale P) < (1 / 2 : NNReal)}).toReal ≤
      4 * C * k * B * a := by
  let bad : Set (Fin k → Real) :=
    {w | (1 / 2 : Real) < |R.rawTotalMass w - 1|}
  have htail := commonMarginal_mass_concentration R hb
  have hmap (b : Bool) :
      ((R.generator.map (R.lawOf b))
        {P | Real.toNNReal (R.rawScale P) < (1 / 2 : NNReal)}) ≤
        R.generator bad := by
    rw [Measure.map_apply (R.lawOf_measurable b) MeasurableSpace.measurableSet_top]
    apply measure_mono_ae
    filter_upwards [R.rawScale_lawOf b, R.rawMass_pos] with w hscale hpos
    intro hw
    change Real.toNNReal (R.rawScale (R.lawOf b w)) < (1 / 2 : NNReal) at hw
    rw [hscale, Real.toNNReal_lt_iff_lt_coe hpos.le] at hw
    norm_num at hw
    change w ∈ bad
    dsimp [bad]
    rw [abs_of_neg (by linarith : R.rawTotalMass w - 1 < 0)]
    linarith
  have hmeasure : (commonMarginalRecipePriorOf R branch)
      {P | Real.toNNReal (R.rawScale P) < (1 / 2 : NNReal)} ≤
      R.generator bad := by
    cases branch
    · simpa [commonMarginalRecipePriorOf, R.prior0_eq] using hmap false
    · simpa [commonMarginalRecipePriorOf, R.prior1_eq] using hmap true
  letI : IsProbabilityMeasure R.generator := R.generatorProbability
  calc
    ((commonMarginalRecipePriorOf R branch)
        {P | Real.toNNReal (R.rawScale P) < (1 / 2 : NNReal)}).toReal ≤
        (R.generator bad).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) hmeasure
    _ ≤ 4 * C * k * B * a := htail

-- @node: helper:common-marginal-raw-center-bound
/-- [the stated conditions](hyp:hb) establishes [the stated conclusion](goal). -/
lemma commonMarginal_rawPriorCenter_abs_le_one {eps : Real}
    {calibration : CommonMarginalCalibration eps}
    {n m d L k : Nat} {B a u v C rho : Real}
    (R : CommonMarginalRecipe calibration n m d L B a k)
    (hb : CommonMarginalBounds R u v calibration.dualGap C rho)
    (branch : Bool) : |rawPriorCenter R branch| ≤ 1 := by
  letI : IsProbabilityMeasure R.generator := R.generatorProbability
  have htInt : Integrable (R.rawTarget branch) R.generator :=
    (hb.target_memLp_two branch).integrable (by norm_num)
  have hsInt : Integrable R.rawTotalMass R.generator :=
    hb.mass_memLp_two.integrable (by norm_num)
  have hmodel : ∀ᵐ w ∂R.generator, ModelClass d eps (R.lawOf branch w) := by
    cases branch
    · exact R.model0
    · exact R.model1
  have hdom : ∀ᵐ w ∂R.generator,
      |R.rawTarget branch w| ≤ R.rawTotalMass w := by
    filter_upwards [R.rawTarget_formula branch, R.rawMass_pos, hmodel] with w hformula hs hclass
    rw [hformula, abs_mul, abs_of_pos hs]
    have hate := ateFunctional_mem_Icc_neg_one_one _ hclass.overlap
    have habs : |ateFunctional (R.lawOf branch w)| ≤ 1 := abs_le.2 hate
    nlinarith
  unfold rawPriorCenter
  calc
    |∫ w, R.rawTarget branch w ∂R.generator| ≤
        ∫ w, |R.rawTarget branch w| ∂R.generator := abs_integral_le_integral_abs
    _ ≤ ∫ w, R.rawTotalMass w ∂R.generator :=
      integral_mono_ae htInt.abs hsInt hdom
    _ = 1 := hb.massMean

-- @node: helper:common-marginal-normalized-target-event
/-- [the stated conditions](hyp:hb,hDelta,hDelta_le) establishes [the stated conclusion](goal). -/
lemma commonMarginal_normalizedTarget_event {eps : Real}
    {calibration : CommonMarginalCalibration eps}
    {n m d L k : Nat} {B a u v C rho Delta : Real}
    (R : CommonMarginalRecipe calibration n m d L B a k)
    (hb : CommonMarginalBounds R u v calibration.dualGap C rho)
    (branch : Bool) (hDelta : 0 < Delta) (hDelta_le : Delta ≤ 2) :
    ∀ᵐ w ∂R.generator,
      Delta / 4 < |ateFunctional (R.lawOf branch w) - rawPriorCenter R branch| →
        Delta / 16 < |R.rawTarget branch w - rawPriorCenter R branch| ∨
        Delta / 16 < |R.rawTotalMass w - 1| := by
  have hc := commonMarginal_rawPriorCenter_abs_le_one R hb branch
  filter_upwards [R.rawTarget_formula branch, R.rawMass_pos] with w hformula hs
  intro hbad
  by_contra hgood
  push_neg at hgood
  have hSlo : 0 < R.rawTotalMass w := hs
  have hSclose := hgood.2
  have hTclose := hgood.1
  rw [hformula] at hTclose
  have hSbound : |R.rawTotalMass w - 1| ≤ Delta / 16 := hSclose
  have hTbound :
      |R.rawTotalMass w * ateFunctional (R.lawOf branch w) -
        rawPriorCenter R branch| ≤ Delta / 16 := hTclose
  have hscaleA :
      |R.rawTotalMass w * ateFunctional (R.lawOf branch w) -
          R.rawTotalMass w * rawPriorCenter R branch| =
        R.rawTotalMass w *
          |ateFunctional (R.lawOf branch w) - rawPriorCenter R branch| := by
    rw [← mul_sub, abs_mul, abs_of_pos hSlo]
  have hcenterScale :
      |R.rawTotalMass w * rawPriorCenter R branch - rawPriorCenter R branch| ≤
        Delta / 16 := by
    rw [show R.rawTotalMass w * rawPriorCenter R branch -
        rawPriorCenter R branch =
          (R.rawTotalMass w - 1) * rawPriorCenter R branch by ring, abs_mul]
    calc
      |R.rawTotalMass w - 1| * |rawPriorCenter R branch| ≤
          (Delta / 16) * 1 :=
        mul_le_mul hSbound hc (abs_nonneg _) (by positivity)
      _ = Delta / 16 := by ring
  have hprod :
      R.rawTotalMass w *
          |ateFunctional (R.lawOf branch w) - rawPriorCenter R branch| ≤
        Delta / 8 := by
    rw [← hscaleA]
    have htri := abs_sub_le
      (R.rawTotalMass w * ateFunctional (R.lawOf branch w))
      (rawPriorCenter R branch)
      (R.rawTotalMass w * rawPriorCenter R branch)
    rw [abs_sub_comm (rawPriorCenter R branch)
      (R.rawTotalMass w * rawPriorCenter R branch)] at htri
    linarith
  have hSge : 1 - Delta / 16 ≤ R.rawTotalMass w := by
    have := (abs_le.mp hSbound).1
    linarith
  have hSge' : (7 : Real) / 8 ≤ R.rawTotalMass w := by
    linarith
  have hmulLower :
      (7 : Real) / 8 *
          |ateFunctional (R.lawOf branch w) - rawPriorCenter R branch| ≤
        R.rawTotalMass w *
          |ateFunctional (R.lawOf branch w) - rawPriorCenter R branch| :=
    mul_le_mul_of_nonneg_right hSge' (abs_nonneg _)
  have hmulStrict :
      (7 : Real) / 8 * (Delta / 4) <
        (7 : Real) / 8 *
          |ateFunctional (R.lawOf branch w) - rawPriorCenter R branch| :=
    mul_lt_mul_of_pos_left hbad (by norm_num)
  nlinarith [hprod, hmulLower, hmulStrict]

-- @node: helper:common-marginal-prior-target-concentration
/-- [the stated conditions](hyp:hb,hDelta,hDelta_le) establishes [the stated conclusion](goal). -/
lemma commonMarginal_prior_target_concentration {eps : Real}
    {calibration : CommonMarginalCalibration eps}
    {n m d L k : Nat} {B a u v C rho Delta : Real}
    (R : CommonMarginalRecipe calibration n m d L B a k)
    (hb : CommonMarginalBounds R u v calibration.dualGap C rho)
    (branch : Bool) (hDelta : 0 < Delta) (hDelta_le : Delta ≤ 2) :
    (commonMarginalRecipePriorOf R branch).real
        {P | Delta / 4 < |ateFunctional P - rawPriorCenter R branch|} ≤
      512 * C * k * B * a / Delta ^ 2 := by
  letI : IsProbabilityMeasure R.generator := R.generatorProbability
  let targetBad : Set (Fin k → Real) :=
    {w | Delta / 16 < |R.rawTarget branch w - rawPriorCenter R branch|}
  let massBad : Set (Fin k → Real) :=
    {w | Delta / 16 < |R.rawTotalMass w - 1|}
  have hsubset :
      ((R.generator.map (R.lawOf branch)).real
        {P | Delta / 4 < |ateFunctional P - rawPriorCenter R branch|}) ≤
        (R.generator (targetBad ∪ massBad)).toReal := by
    rw [Measure.real, Measure.map_apply (R.lawOf_measurable branch)
      MeasurableSpace.measurableSet_top]
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [commonMarginal_normalizedTarget_event R hb branch hDelta hDelta_le]
      with w hw
    intro hbad
    exact hw hbad
  have htarget := commonMarginal_target_concentration R hb branch
    (show 0 < Delta / 16 by positivity)
  have hmass := commonMarginal_mass_concentration_at R hb
    (show 0 < Delta / 16 by positivity)
  have hunion : (R.generator (targetBad ∪ massBad)).toReal ≤
      (R.generator targetBad).toReal + (R.generator massBad).toReal := by
    have h := measure_union_le targetBad massBad (μ := R.generator)
    calc
      (R.generator (targetBad ∪ massBad)).toReal ≤
          (R.generator targetBad + R.generator massBad).toReal :=
        ENNReal.toReal_mono
          (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) h
      _ = (R.generator targetBad).toReal + (R.generator massBad).toReal :=
        ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)
  have hmap : (commonMarginalRecipePriorOf R branch).real
        {P | Delta / 4 < |ateFunctional P - rawPriorCenter R branch|} ≤
      (R.generator (targetBad ∪ massBad)).toReal := by
    cases branch
    · simpa [commonMarginalRecipePriorOf, R.prior0_eq] using hsubset
    · simpa [commonMarginalRecipePriorOf, R.prior1_eq] using hsubset
  refine hmap.trans (hunion.trans ?_)
  dsimp [targetBad, massBad] at htarget hmass ⊢
  calc
    (R.generator
          {w | Delta / 16 < |R.rawTarget branch w - rawPriorCenter R branch|}).toReal +
        (R.generator {w | Delta / 16 < |R.rawTotalMass w - 1|}).toReal ≤
        C * k * B * a / (Delta / 16) ^ 2 +
          C * k * B * a / (Delta / 16) ^ 2 := add_le_add htarget hmass
    _ = 512 * C * k * B * a / Delta ^ 2 := by
          field_simp [ne_of_gt hDelta]
          ring

-- @node: helper:common-marginal-raw-bayes-risk-identification
/-- [the stated conditions](hyp:hb) establishes [the stated conclusion](goal). -/
lemma commonMarginal_raw_bayesSquared_eq_bayesDecision {eps : Real}
    {X : Type*} [MeasurableSpace X]
    {calibration : CommonMarginalCalibration eps}
    {n m d L k : Nat} {B a u v C rho : Real}
    (R : CommonMarginalRecipe calibration n m d L B a k)
    (hb : CommonMarginalBounds R u v calibration.dualGap C rho)
    (branch : Bool) (K : Kernel (DiscreteLaw d) X)
    (rule : X → Real) :
    Causalean.Stat.Minimax.FuzzyHypotheses.bayesSquaredRisk
        (commonMarginalRecipePriorOf R branch) K ateFunctional
          (fun x => commonMarginalTransferClip (rule x)) =
      bayesDecisionRisk (commonMarginalRecipePriorOf R branch) K
        (commonMarginalTransferLoss eps) rule := by
  unfold Causalean.Stat.Minimax.FuzzyHypotheses.bayesSquaredRisk bayesDecisionRisk
  apply lintegral_congr_ae
  have hclass : ∀ᵐ P ∂commonMarginalRecipePriorOf R branch, ModelClass d eps P := by
    cases branch
    · simpa [commonMarginalRecipePriorOf] using hb.class0
    · simpa [commonMarginalRecipePriorOf] using hb.class1
  filter_upwards [hclass] with P hP
  simp [Causalean.Stat.Minimax.FuzzyHypotheses.squaredRisk, decisionRisk,
    commonMarginalTransferLoss, hP]

-- @node: helper:common-marginal-raw-fuzzy-lower
/-- [the stated conditions](hyp:hb,hK,hDelta,hsep,hmass0,hmass1,htv) establishes [the stated conclusion](goal). -/
lemma commonMarginal_raw_fuzzy_lower {eps : Real}
    {X : Type*} [MeasurableSpace X]
    {calibration : CommonMarginalCalibration eps}
    {n m d L k : Nat} {B a u v C rho Delta : Real}
    (R : CommonMarginalRecipe calibration n m d L B a k)
    (hb : CommonMarginalBounds R u v calibration.dualGap C rho)
    (K : Kernel (DiscreteLaw d) X) (hK : ∀ P, IsProbabilityMeasure (K P))
    (hDelta : 0 < Delta)
    (hsep : Delta ≤ |rawPriorCenter R true - rawPriorCenter R false|)
    (hmass0 : (commonMarginalRecipePriorOf R false).real
      {P | Delta / 4 < |ateFunctional P - rawPriorCenter R false|} ≤ 1 / 16)
    (hmass1 : (commonMarginalRecipePriorOf R true).real
      {P | Delta / 4 < |ateFunctional P - rawPriorCenter R true|} ≤ 1 / 16)
    (htv : Causalean.Stat.tvDist
      (Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive
        (commonMarginalRecipePriorOf R false) K)
      (Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive
        (commonMarginalRecipePriorOf R true) K) ≤ 1 / 8) :
    ∀ rule : X → Real, Measurable rule →
      ENNReal.ofReal (3 * Delta ^ 2 / 128) ≤
        max (bayesDecisionRisk (commonMarginalRecipePriorOf R false) K
          (commonMarginalTransferLoss eps) rule)
          (bayesDecisionRisk (commonMarginalRecipePriorOf R true) K
            (commonMarginalTransferLoss eps) rule) := by
  letI : IsProbabilityMeasure R.prior0 := R.probability0
  letI : IsProbabilityMeasure R.prior1 := R.probability1
  letI : IsProbabilityMeasure (commonMarginalRecipePriorOf R false) := by
    simpa [commonMarginalRecipePriorOf] using R.probability0
  letI : IsProbabilityMeasure (commonMarginalRecipePriorOf R true) := by
    simpa [commonMarginalRecipePriorOf] using R.probability1
  intro rule hrule
  have hclip : Measurable (fun x => commonMarginalTransferClip (rule x)) :=
    measurable_const.max (measurable_const.min hrule)
  have htarget : Measurable (ateFunctional : DiscreteLaw d → Real) :=
    measurable_from_top
  have hconst :
      (((Delta / 2 - Delta / 4) ^ 2 *
        (1 - (1 / 8 : Real) - 1 / 16 - 1 / 16)) / 2) =
        3 * Delta ^ 2 / 128 := by ring
  by_cases horder : rawPriorCenter R false ≤ rawPriorCenter R true
  · have hsep' : Delta ≤ rawPriorCenter R true - rawPriorCenter R false := by
      rw [abs_of_nonneg (sub_nonneg.mpr horder)] at hsep
      exact hsep
    have h := Causalean.Stat.Minimax.FuzzyHypotheses.twoFuzzyHypotheses_bayesRisk_lower
      (commonMarginalRecipePriorOf R false) (commonMarginalRecipePriorOf R true)
      K ateFunctional hK (fun x => commonMarginalTransferClip (rule x)) hclip htarget
      (rawPriorCenter R false) (rawPriorCenter R true) Delta (Delta / 4)
      (1 / 16) (1 / 16) (1 / 8) (le_of_lt hDelta) (by positivity)
      (by linarith) hsep' (by norm_num) (by norm_num) (by norm_num)
      hmass0 hmass1 htv
    rw [hconst, commonMarginal_raw_bayesSquared_eq_bayesDecision R hb false K rule,
      commonMarginal_raw_bayesSquared_eq_bayesDecision R hb true K rule] at h
    exact h
  · have horder' : rawPriorCenter R true ≤ rawPriorCenter R false := le_of_not_ge horder
    have hsep' : Delta ≤ rawPriorCenter R false - rawPriorCenter R true := by
      rw [abs_of_nonpos (sub_nonpos.mpr horder')] at hsep
      linarith
    have h := Causalean.Stat.Minimax.FuzzyHypotheses.twoFuzzyHypotheses_bayesRisk_lower
      (commonMarginalRecipePriorOf R true) (commonMarginalRecipePriorOf R false)
      K ateFunctional hK (fun x => commonMarginalTransferClip (rule x)) hclip htarget
      (rawPriorCenter R true) (rawPriorCenter R false) Delta (Delta / 4)
      (1 / 16) (1 / 16) (1 / 8) (le_of_lt hDelta) (by positivity)
      (by linarith) hsep' (by norm_num) (by norm_num) (by norm_num)
      hmass1 hmass0 (by
        have hcomm : Causalean.Stat.tvDist
            (Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive
              (commonMarginalRecipePriorOf R true) K)
            (Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive
              (commonMarginalRecipePriorOf R false) K) =
            Causalean.Stat.tvDist
              (Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive
                (commonMarginalRecipePriorOf R false) K)
              (Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive
                (commonMarginalRecipePriorOf R true) K) := by
          unfold Causalean.Stat.tvDist
          congr 1
          funext A
          rw [abs_sub_comm]
        rw [hcomm]
        exact htv)
    rw [hconst, commonMarginal_raw_bayesSquared_eq_bayesDecision R hb true K rule,
      commonMarginal_raw_bayesSquared_eq_bayesDecision R hb false K rule] at h
    simpa [max_comm] using h

-- @node: helper:common-marginal-poisson-lower-tail
/-- [the stated conditions](hyp:hN,hlambda) establishes [the stated conclusion](goal). -/
lemma commonMarginal_poisson_lower_tail (N : Nat) (hN : 1 ≤ N)
    (lambda : NNReal) (hlambda : (32768 : Real) * N ≤ lambda) :
    poissonMeasure lambda (Set.Iio N) ≤
      ENNReal.ofReal (1 / (4096 * (N : Real))) := by
  have hNR : (0 : Real) < N := by exact_mod_cast hN
  have hlambdaR : (0 : Real) < lambda := lt_of_lt_of_le (by positivity) hlambda
  let z : Real := (lambda : Real) / 8
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hsqrt : Real.sqrt (2 * (lambda : Real) * z) = (lambda : Real) / 2 := by
    dsimp [z]
    rw [show 2 * (lambda : Real) * ((lambda : Real) / 8) =
        ((lambda : Real) / 2) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hsubset : Set.Iio N ⊆
      {w : Nat | (lambda : Real) - (w : Real) >
        Real.sqrt (2 * (lambda : Real) * z)} := by
    intro w hw
    simp only [Set.mem_Iio] at hw
    have hwR : (w : Real) < N := by exact_mod_cast hw
    change Real.sqrt (2 * (lambda : Real) * z) <
      (lambda : Real) - (w : Real)
    rw [hsqrt]
    nlinarith
  have hbern := Causalean.Stat.Concentration.PoissonSelfNormalized.poisson_lower_bernstein
    lambda hz
  have htail : poissonMeasure lambda (Set.Iio N) ≤
      ENNReal.ofReal (Real.exp (-z)) :=
    (measure_mono hsubset).trans hbern
  refine htail.trans (ENNReal.ofReal_le_ofReal ?_)
  have hzpos : 0 < z := by dsimp [z]; positivity
  have hexp : z ≤ Real.exp z := by linarith [Real.add_one_le_exp z]
  calc
    Real.exp (-z) = 1 / Real.exp z := by rw [Real.exp_neg, one_div]
    _ ≤ 1 / z := one_div_le_one_div_of_le hzpos hexp
    _ ≤ 1 / (4096 * (N : Real)) := by
      apply one_div_le_one_div_of_le (by positivity)
      dsimp [z]
      nlinarith

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

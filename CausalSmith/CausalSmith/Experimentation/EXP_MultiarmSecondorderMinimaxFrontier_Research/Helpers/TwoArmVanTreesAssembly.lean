import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.TwoArmVanTreesModel

/-!
Assembly of the finite van Trees regularity record for the smooth two-arm model.
-/

open scoped BigOperators
open Finset Set MeasureTheory

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

open Causalean.Stat.Limit.ObservationDependentVanTrees

-- @node: finiteCountProduct_aestronglyMeasurable_of_sections
/-- [every finite-coordinate section satisfies the stated regularity condition](hyp:hf), [Sectionwise measurability on a finite discrete carrier gives product almost-everywhere strong measurability.](goal) -/
lemma finiteCountProduct_aestronglyMeasurable_of_sections
    {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ : Measure ℝ} {f : ℝ × X → ℝ}
    (hf : ∀ x, AEStronglyMeasurable (fun θ => f (θ, x)) μ) :
    AEStronglyMeasurable f (μ.prod Measure.count) := by
  classical
  have hterm (x : X) : AEStronglyMeasurable
      (fun z : ℝ × X => (if z.2 = x then 1 else 0) * f (z.1, x))
      (μ.prod Measure.count) := by
    apply AEStronglyMeasurable.mul
    · exact (show Measurable
        (fun z : ℝ × X => if z.2 = x then (1 : ℝ) else 0) by
        apply Measurable.ite
        · exact (measurableSet_singleton x).preimage measurable_snd
        · exact measurable_const
        · exact measurable_const).aestronglyMeasurable
    · exact (hf x).comp_fst
  have hsum := Finset.aestronglyMeasurable_sum (Finset.univ : Finset X)
    (fun x _hx => hterm x)
  apply hsum.congr
  filter_upwards with z
  simp

-- @node: twoArmScoreSqField_integrable
/-- [the parameter lies in the stated interval](hyp:ha), [The joint guarded-score square is integrable in the smooth two-arm model.](goal) -/
lemma twoArmScoreSqField_integrable {n : ℕ} (a : ℝ) (ha : 0 < a) :
    Integrable
      (scoreSqField (smoothPrior 0 (a / 2)) (smoothPriorDeriv 0 (a / 2))
        twoArmRegularBernoulliLikelihood twoArmBernoulliLikelihoodDeriv)
      ((parameterMeasure (-1 / 2) (1 / 2)).prod
        (Measure.count : Measure (Unit n → Bool))) := by
  let μ := (parameterMeasure (-1 / 2) (1 / 2)).prod
    (Measure.count : Measure (Unit n → Bool))
  have hp := twoArmPriorScoreField_integrable (n := n) a ha
  have hf := twoArmFisherScoreField_integrable (n := n) a ha
  have hc := twoArmScoreCrossField_integrable (n := n) a ha
  apply (hp.add (hf.add (hc.const_mul 2))).congr
  filter_upwards with z
  have hw0 : 0 ≤ smoothPrior 0 (a / 2) z.1 :=
    smoothPrior_nonneg (by positivity) z.1
  have hp0 : 0 ≤ twoArmRegularBernoulliLikelihood z.1 z.2 :=
    twoArmRegularBernoulliLikelihood_nonneg z.1 z.2
  by_cases hw : 0 < smoothPrior 0 (a / 2) z.1
  · by_cases hlik : 0 < twoArmRegularBernoulliLikelihood z.1 z.2
    · simp only [Pi.add_apply, Pi.mul_apply]
      rw [scoreSqField, jointScore_eq_add hw hlik]
      unfold jointDensity
      ring
    · have hpz : twoArmRegularBernoulliLikelihood z.1 z.2 = 0 :=
        le_antisymm (le_of_not_gt hlik) hp0
      simp [scoreSqField, jointScore, jointDensity, priorScore,
        likelihoodScore, hw, hlik, hpz]
  · have hwz : smoothPrior 0 (a / 2) z.1 = 0 :=
      le_antisymm (le_of_not_gt hw) hw0
    simp [scoreSqField, jointScore, jointDensity, priorScore,
      likelihoodScore, hw, hwz]

-- @node: twoArmErrorScoreField_integrable
/-- [the parameter lies in the stated interval](hyp:ha), [Estimator error times the joint guarded score is integrable by weighted Young's inequality and the two square-integrability results.](goal) -/
lemma twoArmErrorScoreField_integrable {n : ℕ} (a : ℝ) (ha : 0 < a)
    (T : (Unit n → Bool) → ℝ) :
    Integrable
      (errorScoreField (smoothPrior 0 (a / 2)) (smoothPriorDeriv 0 (a / 2))
        twoArmRegularBernoulliLikelihood twoArmBernoulliLikelihoodDeriv
        (twoArmPosteriorTarget a) T)
      ((parameterMeasure (-1 / 2) (1 / 2)).prod Measure.count) := by
  let μ := (parameterMeasure (-1 / 2) (1 / 2)).prod
    (Measure.count : Measure (Unit n → Bool))
  have he := twoArmErrorSqField_integrable (n := n) a ha T
  have hs := twoArmScoreSqField_integrable (n := n) a ha
  have hmem : ∀ᵐ z ∂μ, z.1 ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
    have hθ : ∀ᵐ θ ∂parameterMeasure (-1 / 2) (1 / 2),
        θ ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
      unfold parameterMeasure
      exact ae_restrict_mem measurableSet_Icc
    exact (Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually hθ)
  have hEq : errorScoreField (smoothPrior 0 (a / 2))
      (smoothPriorDeriv 0 (a / 2)) twoArmRegularBernoulliLikelihood
      twoArmBernoulliLikelihoodDeriv (twoArmPosteriorTarget a) T =ᵐ[μ]
      fun z => (T z.2 - twoArmPosteriorTarget a z.1 z.2) *
        (smoothPriorDeriv 0 (a / 2) z.1 *
            twoArmRegularBernoulliLikelihood z.1 z.2 +
          smoothPrior 0 (a / 2) z.1 *
            twoArmBernoulliLikelihoodDeriv z.1 z.2) := by
    filter_upwards [hmem] with z hz
    apply errorScoreField_eq_numerator
    · exact smoothPrior_nonneg (by positivity) z.1
    · exact twoArmRegularBernoulliLikelihood_nonneg z.1 z.2
    · exact derivative_eq_zero_of_nonnegative_of_eq_zero
        (smoothPrior_nonneg (by positivity))
        (hasDerivAt_smoothPrior (by positivity) z.1)
    · exact derivative_eq_zero_of_nonnegative_of_eq_zero
        (fun θ => twoArmRegularBernoulliLikelihood_nonneg θ z.2)
        (twoArmRegularBernoulliLikelihood_hasDerivAt (by
          rw [abs_lt]
          constructor <;> nlinarith [hz.1, hz.2]) z.2)
  have hnumSm : AEStronglyMeasurable
      (fun z : ℝ × (Unit n → Bool) =>
        (T z.2 - twoArmPosteriorTarget a z.1 z.2) *
          (smoothPriorDeriv 0 (a / 2) z.1 *
              twoArmRegularBernoulliLikelihood z.1 z.2 +
            smoothPrior 0 (a / 2) z.1 *
              twoArmBernoulliLikelihoodDeriv z.1 z.2)) μ := by
    apply finiteCountProduct_aestronglyMeasurable_of_sections
    intro s
    have hgCont := (twoArmPosteriorTarget_absolutelyContinuous a s).continuousOn
    rw [uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)] at hgCont
    have hg : AEStronglyMeasurable (fun θ => twoArmPosteriorTarget a θ s)
        (parameterMeasure (-1 / 2) (1 / 2)) :=
      hgCont.aestronglyMeasurable measurableSet_Icc
    have hp : AEStronglyMeasurable
        (fun θ => twoArmRegularBernoulliLikelihood θ s)
        (parameterMeasure (-1 / 2) (1 / 2)) :=
      (twoArmRegularBernoulliLikelihood_continuousOn s).aestronglyMeasurable
        measurableSet_Icc
    have hdwCont : Continuous (smoothPriorDeriv 0 (a / 2)) := by
      have heq : smoothPriorDeriv 0 (a / 2) = deriv (smoothPrior 0 (a / 2)) := by
        funext θ
        exact (hasDerivAt_smoothPrior (by positivity) θ).deriv.symm
      rw [heq]
      exact (smoothPrior_contDiff (by positivity : 0 < a / 2)).continuous_deriv_one
    have hdpCont : Continuous (fun θ => twoArmBernoulliLikelihoodDeriv θ s) := by
      unfold twoArmBernoulliLikelihoodDeriv
      apply continuous_finsetSum Finset.univ
      intro i _hi
      apply Continuous.mul
      · apply continuous_finsetProd (Finset.univ.erase i)
        intro j _hj
        split <;> fun_prop
      · split <;> fun_prop
    have hT : AEStronglyMeasurable (fun _ : ℝ => T s)
        (parameterMeasure (-1 / 2) (1 / 2)) := aestronglyMeasurable_const
    have hw : AEStronglyMeasurable (smoothPrior 0 (a / 2))
        (parameterMeasure (-1 / 2) (1 / 2)) :=
      (smoothPrior_contDiff (by positivity : 0 < a / 2)).continuous.aestronglyMeasurable
    have hsm := (hT.sub hg).mul
      ((hdwCont.aestronglyMeasurable.mul hp).add
        (hw.mul hdpCont.aestronglyMeasurable))
    apply hsm.congr
    filter_upwards with θ
    rfl
  apply Integrable.congr ((he.add hs).mono' hnumSm ?_) hEq.symm
  filter_upwards [hEq] with z hz
  rw [← hz]
  unfold errorScoreField errorSqField scoreSqField
  change ‖(T z.2 - twoArmPosteriorTarget a z.1 z.2) *
      jointScore (smoothPrior 0 (a / 2)) (smoothPriorDeriv 0 (a / 2))
        twoArmRegularBernoulliLikelihood twoArmBernoulliLikelihoodDeriv z *
      jointDensity (smoothPrior 0 (a / 2)) twoArmRegularBernoulliLikelihood z‖ ≤ _
  ·
    have hw : 0 ≤ smoothPrior 0 (a / 2) z.1 :=
      smoothPrior_nonneg (by positivity) z.1
    have hp : 0 ≤ twoArmRegularBernoulliLikelihood z.1 z.2 :=
      twoArmRegularBernoulliLikelihood_nonneg z.1 z.2
    have hq : 0 ≤ jointDensity (smoothPrior 0 (a / 2))
        twoArmRegularBernoulliLikelihood z := mul_nonneg hw hp
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hq]
    simp only [Pi.add_apply]
    have hyoung :
        |T z.2 - twoArmPosteriorTarget a z.1 z.2| *
            |jointScore (smoothPrior 0 (a / 2)) (smoothPriorDeriv 0 (a / 2))
              twoArmRegularBernoulliLikelihood twoArmBernoulliLikelihoodDeriv z| ≤
          (T z.2 - twoArmPosteriorTarget a z.1 z.2) ^ 2 +
            jointScore (smoothPrior 0 (a / 2)) (smoothPriorDeriv 0 (a / 2))
              twoArmRegularBernoulliLikelihood twoArmBernoulliLikelihoodDeriv z ^ 2 := by
      nlinarith [sq_nonneg
        (|T z.2 - twoArmPosteriorTarget a z.1 z.2| -
          |jointScore (smoothPrior 0 (a / 2)) (smoothPriorDeriv 0 (a / 2))
            twoArmRegularBernoulliLikelihood twoArmBernoulliLikelihoodDeriv z|),
        sq_abs (T z.2 - twoArmPosteriorTarget a z.1 z.2),
        sq_abs (jointScore (smoothPrior 0 (a / 2)) (smoothPriorDeriv 0 (a / 2))
          twoArmRegularBernoulliLikelihood twoArmBernoulliLikelihoodDeriv z)]
    calc
      _ ≤ ((T z.2 - twoArmPosteriorTarget a z.1 z.2) ^ 2 +
          jointScore (smoothPrior 0 (a / 2)) (smoothPriorDeriv 0 (a / 2))
            twoArmRegularBernoulliLikelihood twoArmBernoulliLikelihoodDeriv z ^ 2) *
          jointDensity (smoothPrior 0 (a / 2)) twoArmRegularBernoulliLikelihood z :=
        mul_le_mul_of_nonneg_right hyoung hq
      _ = _ := by
        change _ = errorSqField (smoothPrior 0 (a / 2))
            twoArmRegularBernoulliLikelihood (twoArmPosteriorTarget a) T z +
          scoreSqField (smoothPrior 0 (a / 2)) (smoothPriorDeriv 0 (a / 2))
            twoArmRegularBernoulliLikelihood twoArmBernoulliLikelihoodDeriv z
        unfold errorSqField scoreSqField
        ring

-- @node: twoArmDerivativeBalanceField_integrable
/-- [the parameter lies in the stated interval](hyp:ha), [The derivative-balance field is integrable because it is the error-score field minus the already integrable sensitivity field.](goal) -/
lemma twoArmDerivativeBalanceField_integrable {n : ℕ} (a : ℝ) (ha : 0 < a)
    (T : (Unit n → Bool) → ℝ) :
    Integrable
      (derivativeBalanceField (smoothPrior 0 (a / 2))
        (smoothPriorDeriv 0 (a / 2)) twoArmRegularBernoulliLikelihood
        twoArmBernoulliLikelihoodDeriv (twoArmPosteriorTarget a)
        (twoArmPosteriorTargetDeriv a) T)
      ((parameterMeasure (-1 / 2) (1 / 2)).prod Measure.count) := by
  have he := twoArmErrorScoreField_integrable (n := n) a ha T
  have hs := twoArmSensitivityField_integrable (n := n) a ha
  have hmem : ∀ᵐ z ∂((parameterMeasure (-1 / 2) (1 / 2)).prod
      (Measure.count : Measure (Unit n → Bool))),
      z.1 ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
    have hθ : ∀ᵐ θ ∂parameterMeasure (-1 / 2) (1 / 2),
        θ ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
      unfold parameterMeasure
      exact ae_restrict_mem measurableSet_Icc
    exact Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually hθ
  apply (he.sub hs).congr
  filter_upwards [hmem] with z hz
  have hw0 : 0 ≤ smoothPrior 0 (a / 2) z.1 :=
    smoothPrior_nonneg (by positivity) z.1
  have hp0 : 0 ≤ twoArmRegularBernoulliLikelihood z.1 z.2 :=
    twoArmRegularBernoulliLikelihood_nonneg z.1 z.2
  have hwzero : smoothPrior 0 (a / 2) z.1 = 0 →
      smoothPriorDeriv 0 (a / 2) z.1 = 0 := by
    exact derivative_eq_zero_of_nonnegative_of_eq_zero
      (smoothPrior_nonneg (by positivity)) (hasDerivAt_smoothPrior (by positivity) z.1)
  have hpzero : twoArmRegularBernoulliLikelihood z.1 z.2 = 0 →
      twoArmBernoulliLikelihoodDeriv z.1 z.2 = 0 := by
    exact derivative_eq_zero_of_nonnegative_of_eq_zero
      (fun θ => twoArmRegularBernoulliLikelihood_nonneg θ z.2)
      (twoArmRegularBernoulliLikelihood_hasDerivAt (by
        rw [abs_lt]
        constructor <;> nlinarith [hz.1, hz.2]) z.2)
  change errorScoreField (smoothPrior 0 (a / 2)) (smoothPriorDeriv 0 (a / 2))
      twoArmRegularBernoulliLikelihood twoArmBernoulliLikelihoodDeriv
        (twoArmPosteriorTarget a) T z -
      sensitivityField (smoothPrior 0 (a / 2)) twoArmRegularBernoulliLikelihood
        (twoArmPosteriorTargetDeriv a) z = _
  rw [errorScoreField_eq_numerator hw0 hp0 hwzero hpzero]
  simp only [derivativeBalanceField, sensitivityField, jointDensity]
  ring

-- @node: twoArmFiniteVanTreesRegularity
/-- [the parameter lies in the stated interval](hyp:ha), [All finite-experiment regularity conditions for the smooth two-arm Bernoulli likelihood and its observation-dependent posterior target.](goal) -/
lemma twoArmFiniteVanTreesRegularity {n : ℕ} (a : ℝ) (ha : 0 < a)
    (T : (Unit n → Bool) → ℝ) :
    FiniteVanTreesModelRegularity (Unit n → Bool) (-1 / 2) (1 / 2)
      (smoothPrior 0 (a / 2)) (smoothPriorDeriv 0 (a / 2))
      twoArmRegularBernoulliLikelihood twoArmBernoulliLikelihoodDeriv
      (twoArmPosteriorTarget a) (twoArmPosteriorTargetDeriv a) T := by
  let hb := twoArmDerivativeBalanceField_integrable (n := n) a ha T
  let he := twoArmErrorScoreField_integrable (n := n) a ha T
  let hsen := twoArmSensitivityField_integrable (n := n) a ha
  let herr := twoArmErrorSqField_integrable (n := n) a ha T
  let hscore := twoArmScoreSqField_integrable (n := n) a ha
  let hp := twoArmPriorScoreField_integrable (n := n) a ha
  let hf := twoArmFisherScoreField_integrable (n := n) a ha
  let hc := twoArmScoreCrossField_integrable (n := n) a ha
  refine {
    hpnonneg := twoArmRegularBernoulliLikelihood_nonneg
    hpnorm := ?_
    hpint := ?_
    hdpint := ?_
    hdiffUnder := ?_
    hpAC := ?_
    hgAC := ?_
    hdp := twoArmRegularBernoulliLikelihood_hasDerivAt_ae
    hdg := twoArmPosteriorTarget_hasDerivAt_ae a
    hbalanceSm := hb.aestronglyMeasurable
    hbalanceInt := hb
    herrorScoreSm := he.aestronglyMeasurable
    herrorScoreInt := he
    hsensitivitySm := hsen.aestronglyMeasurable
    hsensitivityInt := hsen
    herrorSqSm := herr.aestronglyMeasurable
    herrorSqInt := herr
    hscoreSqSm := hscore.aestronglyMeasurable
    hscoreSqInt := hscore
    hpriorJointSqSm := hp.aestronglyMeasurable
    hpriorJointSqInt := hp
    hfisherSqSm := hf.aestronglyMeasurable
    hfisherSqInt := hf
    hcrossSm := hc.aestronglyMeasurable
    hcrossInt := hc }
  · intro θ hθ
    apply twoArmRegularBernoulliLikelihood_integral_eq_one
    rw [abs_le]
    constructor <;> nlinarith [hθ.1, hθ.2]
  · intro θ _
    exact twoArmRegularBernoulliLikelihood_integrable_count θ
  · intro θ _
    exact twoArmBernoulliLikelihoodDeriv_integrable_count θ
  · intro θ hθ
    apply twoArmRegularBernoulliIntegral_hasDerivAt
    rw [abs_lt]
    constructor <;> nlinarith [hθ.1, hθ.2]
  · filter_upwards with s
    exact twoArmRegularBernoulliLikelihood_absolutelyContinuous s
  · filter_upwards with s
    exact twoArmPosteriorTarget_absolutelyContinuous a s

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

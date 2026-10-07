module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialBayesOrdering

/-! # Finite-sample sequential van Trees assembly

This file assembles the paper's already verified likelihood, prior, target, and
product-integral adapters into a finite-sample Bayes inequality.  Transcript
Fisher integrability and its numerical upper bound remain explicit premises;
they are the score-projection and Doob-information obligations.
-/

public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open Causalean.Stat.Minimax.ObservationDependentVanTrees

/-- Prior-score, likelihood-score, and cross-term integrability imply
integrability of the guarded joint-score square. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:w,dw,q,dq,mu,hw,hq,hprior,hfisher,hcross), these specify the stated inputs. -/
lemma integrable_scoreSqField_of_prior_fisher_cross
    {X : Type*} [MeasurableSpace X]
    (w dw : ℝ → ℝ) (q dq : ℝ → X → ℝ) (mu : Measure (ℝ × X))
    (hw : ∀ a, 0 ≤ w a) (hq : ∀ a x, 0 ≤ q a x)
    (hprior : Integrable (fun z : ℝ × X =>
      w z.1 * q z.1 z.2 * (priorScore w dw z.1) ^ 2) mu)
    (hfisher : Integrable (fun z : ℝ × X =>
      w z.1 * q z.1 z.2 * (likelihoodScore q dq z.1 z.2) ^ 2) mu)
    (hcross : Integrable (fun z : ℝ × X =>
      w z.1 * q z.1 z.2 *
        (priorScore w dw z.1 * likelihoodScore q dq z.1 z.2)) mu) :
    Integrable (scoreSqField w dw q dq) mu := by
  have hscore_expand (a : ℝ) (x : X) :
      scoreSqField w dw q dq (a, x) =
        w a * q a x * (priorScore w dw a) ^ 2 +
          (w a * q a x * (likelihoodScore q dq a x) ^ 2 +
            2 * (w a * q a x *
              (priorScore w dw a * likelihoodScore q dq a x))) := by
    by_cases hwpos : 0 < w a
    · by_cases hqpos : 0 < q a x
      · simp only [scoreSqField, jointScore, jointDensity, priorScore,
          likelihoodScore, hwpos, hqpos, mul_pos, if_true]
        field_simp
        ring
      · have hqzero : q a x = 0 :=
          le_antisymm (le_of_not_gt hqpos) (hq a x)
        simp [scoreSqField, jointScore, jointDensity, hqzero]
    · have hwzero : w a = 0 :=
        le_antisymm (le_of_not_gt hwpos) (hw a)
      simp [scoreSqField, jointScore, jointDensity, hwzero]
  have hsum := hprior.add (hfisher.add (hcross.const_mul 2))
  exact hsum.congr (Filter.Eventually.of_forall fun z =>
    (hscore_expand z.1 z.2).symm)

/-- For a compact scalar path, finite weighted transcript Fisher information
and an explicit bound on its prior average give the finite-sample Bayes risk
lower bound.  The Fisher premises are precisely the part supplied later by
score projection and the sequential Doob bound. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,v,p,R,I,n,hR,hp,hinterior,T,hT,herrorSqInt,hfisherSqInt,hfisher_le,hinfoPos), these specify the stated inputs. -/
lemma sequential_vanTrees_bayes_lower_bound_of_fisher_control
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p R I : ℝ) (n : ℕ)
    (hR : 0 < R) (hp : InteriorAssignment p)
    (hinterior : ∀ a ∈ Icc (-R) R,
      InteriorMeans (parameterPath θ v a))
    (T : Transcript (Z n) → ℝ) (hT : Measurable T)
    (herrorSqInt : Integrable
      (errorSqField (sequentialVTPrior R)
        (vtDensity P θ v p n (-R) R) (vtTarget θ v) T)
      ((parameterMeasure (-R) R).prod (transcriptReferenceMeasure P n)))
    (hfisherSqInt : Integrable (fun z : ℝ × Transcript (Z n) =>
      sequentialVTPrior R z.1 * vtDensity P θ v p n (-R) R z.1 z.2 *
        (likelihoodScore (vtDensity P θ v p n (-R) R)
          (vtDensityDeriv P θ v p n (-R) R) z.1 z.2) ^ 2)
      ((parameterMeasure (-R) R).prod (transcriptReferenceMeasure P n)))
    (hfisher_le :
      (∫ a, sequentialVTPrior R a *
        fisherInformation (transcriptReferenceMeasure P n)
          (vtDensity P θ v p n (-R) R)
          (vtDensityDeriv P θ v p n (-R) R) a
        ∂parameterMeasure (-R) R) ≤ I)
    (hinfoPos : 0 < priorInformation (-R) R
        (sequentialVTPrior R) (sequentialVTPriorDeriv R) +
      ∫ a, sequentialVTPrior R a *
        fisherInformation (transcriptReferenceMeasure P n)
          (vtDensity P θ v p n (-R) R)
          (vtDensityDeriv P θ v p n (-R) R) a
        ∂parameterMeasure (-R) R) :
    contrast v ^ 2 / (I + 40 / R ^ 2) ≤
      ∫ z, errorSqField (sequentialVTPrior R)
        (vtDensity P θ v p n (-R) R) (vtTarget θ v) T z
        ∂((parameterMeasure (-R) R).prod
          (transcriptReferenceMeasure P n)) := by
  let mu := transcriptReferenceMeasure P n
  let q := vtDensity P θ v p n (-R) R
  let dq := vtDensityDeriv P θ v p n (-R) R
  let w := sequentialVTPrior R
  let dw := sequentialVTPriorDeriv R
  let g := vtTarget (X := Transcript (Z n)) θ v
  let dg := vtTargetDeriv (X := Transcript (Z n)) v
  have hprior := sequentialVTPrior_facts hR
  have hmeas := sequentialVanTreesProductMeasurable P θ v p R n hR T hT
  have hmem : ∀ᵐ a ∂parameterMeasure (-R) R, a ∈ Icc (-R) R := by
    unfold parameterMeasure
    exact ae_restrict_mem measurableSet_Icc
  have hnormAE : ∀ᵐ a ∂parameterMeasure (-R) R,
      ∫ z, q a z ∂mu = 1 := by
    filter_upwards [hmem] with a ha
    exact vtDensity_integral_eq_one P θ v p n (-R) R hp hinterior ha
  have hqintAE : ∀ᵐ a ∂parameterMeasure (-R) R,
      Integrable (q a) mu := by
    filter_upwards [hmem] with a ha
    exact vtDensity_integrable P θ v p n (-R) R ha
  have hjointInt : Integrable (jointDensity w q)
      ((parameterMeasure (-R) R).prod mu) := by
    apply integrable_jointDensity_of_normalization w q
    · exact hprior.nonneg
    · exact vtDensity_nonneg P θ v p n (-R) R hp hinterior
    · exact hqintAE
    · exact hnormAE
    · unfold w sequentialVTPrior
      exact smoothPrior_integrable_parameterMeasure (by linarith)
    · exact ((hprior.contDiff.continuous.measurable.comp measurable_fst).mul
        (measurable_vtDensity_joint P θ v p n (-R) R)).aestronglyMeasurable
  have hsensitivityInt : Integrable (sensitivityField w q dg)
      ((parameterMeasure (-R) R).prod mu) :=
    integrable_sequentialSensitivity_of_jointDensity w q v _ hjointInt
  have hpriorJointInt : Integrable (fun z : ℝ × Transcript (Z n) =>
      w z.1 * q z.1 z.2 * (priorScore w dw z.1) ^ 2)
      ((parameterMeasure (-R) R).prod mu) := by
    apply integrable_priorJointSq_of_normalization w dw q
    · exact hprior.nonneg
    · exact vtDensity_nonneg P θ v p n (-R) R hp hinterior
    · exact hqintAE
    · exact hnormAE
    · exact hprior.scoreSqIntegrable
    · exact hmeas.priorJointSq.aestronglyMeasurable
  have hwmeas : Measurable w := hprior.contDiff.continuous.measurable
  have hdwmeas : Measurable dw := by
    unfold dw sequentialVTPriorDeriv smoothPriorDeriv
    apply Measurable.ite
    · exact measurableSet_lt
        (continuous_abs.comp (continuous_id.sub continuous_const)).measurable
        measurable_const
    · fun_prop
    · exact measurable_const
  have hqmeas : Measurable (fun z : ℝ × Transcript (Z n) => q z.1 z.2) :=
    measurable_vtDensity_joint P θ v p n (-R) R
  have hdqmeas : Measurable (fun z : ℝ × Transcript (Z n) => dq z.1 z.2) :=
    measurable_vtDensityDeriv_joint P θ v p n (-R) R
  have hcrossInt : Integrable (fun z : ℝ × Transcript (Z n) =>
      w z.1 * q z.1 z.2 *
        (priorScore w dw z.1 * likelihoodScore q dq z.1 z.2))
      ((parameterMeasure (-R) R).prod mu) := by
    exact integrable_priorLikelihoodCross_of_squares w dw q dq _
      hwmeas hdwmeas hqmeas hdqmeas hprior.nonneg
      (vtDensity_nonneg P θ v p n (-R) R hp hinterior)
      hpriorJointInt hfisherSqInt
  have hscoreSqInt : Integrable (scoreSqField w dw q dq)
      ((parameterMeasure (-R) R).prod mu) :=
    integrable_scoreSqField_of_prior_fisher_cross w dw q dq _
      hprior.nonneg (vtDensity_nonneg P θ v p n (-R) R hp hinterior)
      hpriorJointInt hfisherSqInt hcrossInt
  have hscoreMeas : Measurable (jointScore w dw q dq) := by
    unfold jointScore jointDensity
    exact Measurable.ite
      (measurableSet_lt measurable_const
        ((hwmeas.comp measurable_fst).mul hqmeas))
      (((hdwmeas.comp measurable_fst).mul hqmeas |>.add
        ((hwmeas.comp measurable_fst).mul hdqmeas)).div
          ((hwmeas.comp measurable_fst).mul hqmeas)) measurable_const
  have herrorScoreInt : Integrable (errorScoreField w dw q dq g T)
      ((parameterMeasure (-R) R).prod mu) :=
    integrable_errorScoreField_of_squares w dw q dq g T _ hwmeas hqmeas
      (by unfold g vtTarget; fun_prop) hT hscoreMeas hprior.nonneg
      (vtDensity_nonneg P θ v p n (-R) R hp hinterior)
      herrorSqInt hscoreSqInt
  have hwzero : ∀ a, w a = 0 → dw a = 0 := by
    intro a ha
    exact derivative_eq_zero_of_nonnegative_of_eq_zero hprior.nonneg
      (hprior.hasDeriv a) ha
  have hqzero : ∀ᵐ z ∂((parameterMeasure (-R) R).prod mu),
      q z.1 z.2 = 0 → dq z.1 z.2 = 0 := by
    filter_upwards [ae_hasDerivAt_vtDensity P θ v p n (-R) R] with z hz
    exact derivative_eq_zero_of_nonnegative_of_eq_zero
      (fun a => vtDensity_nonneg P θ v p n (-R) R hp hinterior a z.2)
      hz
  have hbalanceInt : Integrable (derivativeBalanceField w dw q dq g dg T)
      ((parameterMeasure (-R) R).prod mu) := by
    apply (herrorScoreInt.sub hsensitivityInt).congr
    filter_upwards [hqzero] with z hz
    have heq : derivativeBalanceField w dw q dq g dg T z =
        errorScoreField w dw q dq g T z - sensitivityField w q dg z := by
      rw [errorScoreField_eq_numerator (hprior.nonneg z.1)
        (vtDensity_nonneg P θ v p n (-R) R hp hinterior z.1 z.2)
        (hwzero z.1) hz]
      unfold derivativeBalanceField sensitivityField jointDensity
      ring
    exact heq.symm
  have hboundary : ∀ᵐ z ∂mu,
      w R * q R z * (T z - g R z) = 0 ∧
        w (-R) * q (-R) z * (T z - g (-R) z) = 0 := by
    have hend := sequentialVTPrior_endpoints hR
    filter_upwards with z
    simp [w, hend.1, hend.2]
  have hvan := observation_dependent_van_trees mu (by linarith : -R < R)
    w dw q dq g dg T hprior.contDiff hprior.hasDeriv
    hprior.nonneg
    (vtDensity_nonneg P θ v p n (-R) R hp hinterior)
    (fun a ha => vtDensity_integral_eq_one P θ v p n (-R) R hp hinterior ha)
    (fun a ha => by
      have hzero : ∫ z, dq a z ∂mu = 0 := by
        have haIcc : a ∈ Icc (-R) R := ⟨ha.1.le, ha.2.le⟩
        simpa [dq, mu, vtDensityDeriv, haIcc] using
          integral_transcriptMixtureRealDerivative_eq_zero P
            (parameterPath θ v a) v p n
      rw [hzero]
      exact vtDensity_integral_hasDerivAt P θ v p n (-R) R hp hinterior ha)
    (Filter.Eventually.of_forall
      (vtDensity_absolutelyContinuous P θ v p n (-R) R (by linarith)))
    (Filter.Eventually.of_forall (fun z => vtTarget_absolutelyContinuous θ v z (-R) R))
    (ae_hasDerivAt_vtDensity P θ v p n (-R) R)
    (Filter.Eventually.of_forall (fun z => hasDerivAt_vtTarget θ v z.1 z.2))
    hboundary hbalanceInt
    hmeas.errorScore.aestronglyMeasurable herrorScoreInt
    hsensitivityInt
    hmeas.errorSq.aestronglyMeasurable herrorSqInt
    hmeas.scoreSq.aestronglyMeasurable hscoreSqInt
    hpriorJointInt
    hfisherSqInt
    hcrossInt hinfoPos
  have hsensitivity :
      (∫ z, sensitivityField w q dg z
        ∂((parameterMeasure (-R) R).prod mu)) = contrast v :=
    integral_sequentialSensitivity_eq w q v hprior.normalized hnormAE hsensitivityInt
  have hdenom : priorInformation (-R) R w dw +
      ∫ a, w a * fisherInformation mu q dq a ∂parameterMeasure (-R) R ≤
        I + 40 / R ^ 2 := by
    rw [hprior.information]
    linarith
  have hcompare : contrast v ^ 2 / (I + 40 / R ^ 2) ≤
      contrast v ^ 2 / (priorInformation (-R) R w dw +
        ∫ a, w a * fisherInformation mu q dq a ∂parameterMeasure (-R) R) :=
    div_le_div₀ (sq_nonneg _) le_rfl hinfoPos hdenom
  apply hcompare.trans
  simpa [mu, q, dq, w, dw, g, dg, hsensitivity] using hvan

end CausalSmith.Stat.LdpAteEfficiencySurface

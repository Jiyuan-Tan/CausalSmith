module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialBayesMeasurability
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialVanTreesAssembly

/-! # Sequential van Trees risk and scaling bridge

This file converts the native-real product-space Bayes error in the finite
van Trees inequality into the weighted `ENNReal` local risk used by the
sequential minimax statement.
-/

public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Causalean.Stat.Minimax.ObservationDependentVanTrees

/-- Scaling a parameter direction by inverse root sample size makes its scalar
path exactly the corresponding local alternative. For [the displayed inputs and conditions](hyp:v,a,n), [the stated result](goal) follows. -/
lemma parameterPath_sampleScaledDirection_eq_localAlternative
    (θ v : TrialParameter) (a : ℝ) (n : ℕ) :
    parameterPath θ (scaledDirection ((Real.sqrt n)⁻¹) v) a =
      localAlternative θ (scaledDirection a v) n := by
  funext k
  simp [parameterPath, scaledDirection, localAlternative]
  ring

/-- Along the sample-scaled van Trees path, the squared scaled error is sample
size times the unscaled target error. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,v,a,n,z), these specify the stated inputs. -/
lemma scaledError_sq_eq_nat_mul_vtTarget_error_sq
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (a : ℝ)
    (n : ℕ) (z : Transcript (Z n)) :
    (scaledError P θ (scaledDirection a v) n z) ^ 2 =
      (n : ℝ) * (P.estimate n z -
        vtTarget θ (scaledDirection ((Real.sqrt n)⁻¹) v) a z) ^ 2 := by
  rw [vtTarget_eq_parameterPath,
    parameterPath_sampleScaledDirection_eq_localAlternative]
  unfold scaledError
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

/-- Contrast is linear along scalar multiples of a trial direction. For [the displayed inputs and conditions](hyp:a,v), [the stated result](goal) follows. -/
lemma contrast_scaledDirection (a : ℝ) (v : TrialParameter) :
    contrast (scaledDirection a v) = a * contrast v := by
  simp [contrast, scaledDirection]
  ring

/-- For positive sample size, sample scaling cancels after multiplying the
squared contrast sensitivity by the sample size. For [the displayed inputs and conditions](hyp:v,hn), [the stated result](goal) follows. -/
lemma nat_mul_contrast_sampleScaledDirection_sq
    (v : TrialParameter) {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * contrast (scaledDirection ((Real.sqrt n)⁻¹) v) ^ 2 =
      contrast v ^ 2 := by
  rw [contrast_scaledDirection]
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := by positivity
  have hsqrtSq : (Real.sqrt (n : ℝ)) ^ 2 = n :=
    Real.sq_sqrt (Nat.cast_nonneg n)
  field_simp
  nlinarith

/-- On the compact scalar interval, the local risk is the reference-measure
integral weighted by the interval-extended transcript density. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,v,p,R,a,n,hp,hinterior,ha), these specify the stated inputs. -/
lemma localRisk_scaledDirection_eq_lintegral_vtDensity
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p R a : ℝ) (n : ℕ)
    (hp : InteriorAssignment p)
    (hinterior : ∀ b ∈ Icc (-R) R,
      InteriorMeans (parameterPath θ
        (scaledDirection ((Real.sqrt n)⁻¹) v) b))
    (ha : a ∈ Icc (-R) R) :
    localRisk P θ (scaledDirection a v) p n =
      ∫⁻ z, ENNReal.ofReal
          (vtDensity P θ (scaledDirection ((Real.sqrt n)⁻¹) v)
            p n (-R) R a z) *
        ENNReal.ofReal ((scaledError P θ (scaledDirection a v) n z) ^ 2)
        ∂transcriptReferenceMeasure P n := by
  have hpath := parameterPath_sampleScaledDirection_eq_localAlternative θ v a n
  have hlaw := transcriptLaw_eq_withDensity_mixture P
    (parameterPath θ (scaledDirection ((Real.sqrt n)⁻¹) v) a) p n hp
    (hinterior a ha)
  have hq : (fun z => ENNReal.ofReal
      (vtDensity P θ (scaledDirection ((Real.sqrt n)⁻¹) v)
        p n (-R) R a z)) =
      fun z => ENNReal.ofReal
        (transcriptMixtureRealDensity P
          (parameterPath θ (scaledDirection ((Real.sqrt n)⁻¹) v) a) p n z) := by
    funext z
    simp [vtDensity, ha]
  have hlawq : (transcriptReferenceMeasure P n).withDensity
      (fun z => ENNReal.ofReal
        (vtDensity P θ (scaledDirection ((Real.sqrt n)⁻¹) v)
          p n (-R) R a z)) =
      transcriptLaw P
        (parameterPath θ (scaledDirection ((Real.sqrt n)⁻¹) v) a) p n := by
    rw [hq]
    exact hlaw
  unfold localRisk
  rw [← hpath, ← hlawq]
  rw [lintegral_withDensity_eq_lintegral_mul]
  · rfl
  · apply ENNReal.measurable_ofReal.comp
    have hpair : Measurable (fun z : Transcript (Z n) => (a, z)) :=
      Measurable.prod (f := fun z : Transcript (Z n) => (a, z))
        measurable_const measurable_id
    exact (measurable_vtDensity_joint P θ
      (scaledDirection ((Real.sqrt n)⁻¹) v) p n (-R) R).comp hpair
  · apply ENNReal.measurable_ofReal.comp
    exact (measurable_const.mul
      ((P.estimate_measurable n).sub measurable_const)).pow_const 2

/-- The scaled nonnegative product-space error integral equals the weighted
compact-prior local risk, without any finiteness assumption. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,v,p,R,n,hR,hp,hinterior), these specify the stated inputs. -/
lemma lintegral_scaledSequentialBayesError_eq_weighted_localRisk
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p R : ℝ) (n : ℕ)
    (hR : 0 < R) (hp : InteriorAssignment p)
    (hinterior : ∀ a ∈ Icc (-R) R,
      InteriorMeans (parameterPath θ
        (scaledDirection ((Real.sqrt n)⁻¹) v) a)) :
    (∫⁻ z : ℝ × Transcript (Z n), ENNReal.ofReal ((n : ℝ) *
      errorSqField (sequentialVTPrior R)
        (vtDensity P θ (scaledDirection ((Real.sqrt n)⁻¹) v)
          p n (-R) R)
        (vtTarget θ (scaledDirection ((Real.sqrt n)⁻¹) v))
        (P.estimate n) z)
      ∂((parameterMeasure (-R) R).prod (transcriptReferenceMeasure P n))) =
      ∫⁻ a, ENNReal.ofReal (sequentialVTPrior R a) *
        localRisk P θ (scaledDirection a v) p n
        ∂parameterMeasure (-R) R := by
  rw [lintegral_prod]
  · apply lintegral_congr_ae
    have hmem : ∀ᵐ a ∂parameterMeasure (-R) R, a ∈ Icc (-R) R := by
      unfold parameterMeasure
      exact ae_restrict_mem measurableSet_Icc
    filter_upwards [hmem] with a ha
    rw [localRisk_scaledDirection_eq_lintegral_vtDensity
      P θ v p R a n hp hinterior ha]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro z
    rw [scaledError_sq_eq_nat_mul_vtTarget_error_sq P θ v a n z]
    unfold errorSqField jointDensity
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg n),
      ENNReal.ofReal_mul (sq_nonneg _),
      ENNReal.ofReal_mul ((sequentialVTPrior_facts hR).nonneg a),
      ENNReal.ofReal_mul (Nat.cast_nonneg n)]
    ac_rfl
  · exact (ENNReal.measurable_ofReal.comp
      (measurable_const.mul
        (sequentialVanTreesProductMeasurable P θ
          (scaledDirection ((Real.sqrt n)⁻¹) v) p R n hR
          (P.estimate n) (P.estimate_measurable n)).errorSq)).aemeasurable

/-- Compact-prior averaging is bounded by local worst risk whenever the scalar
directions fit in the chosen radius and remain interior. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,v,p,R,H,n,hR,hinterior,hcover), these specify the stated inputs. -/
lemma weightedLocalRisk_le_localWorstRisk
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter)
    (p R H : ℝ) (n : ℕ) (hR : 0 < R)
    (hinterior : ∀ a ∈ Icc (-R) R,
      InteriorMeans (parameterPath θ
        (scaledDirection ((Real.sqrt n)⁻¹) v) a))
    (hcover : R * Real.sqrt ((v 0) ^ 2 + (v 1) ^ 2) ≤ H) :
    (∫⁻ a, ENNReal.ofReal (sequentialVTPrior R a) *
      localRisk P θ (scaledDirection a v) p n
      ∂parameterMeasure (-R) R) ≤ localWorstRisk P θ p H n := by
  have hprior := sequentialVTPrior_facts hR
  exact (weighted_lintegral_le_uniform
    (parameterMeasure (-R) R) (sequentialVTPrior R)
    (fun a => localRisk P θ (scaledDirection a v) p n)
    (localWorstRisk P θ p H n)
    hprior.contDiff.continuous.measurable
    (measurable_localRisk_scaledDirection P θ v p n).aemeasurable
    (by
      unfold sequentialVTPrior
      exact smoothPrior_integrable_parameterMeasure (by linarith))
    (Filter.Eventually.of_forall hprior.nonneg) hprior.normalized
    (by
      have hmem : ∀ᵐ a ∂parameterMeasure (-R) R, a ∈ Icc (-R) R := by
        unfold parameterMeasure
        exact ae_restrict_mem measurableSet_Icc
      filter_upwards [hmem] with a ha
      apply localRisk_le_localWorstRisk
      refine ⟨(scaledDirection_mem_cover v ha).trans hcover, ?_⟩
      rw [← parameterPath_sampleScaledDirection_eq_localAlternative]
      exact hinterior a ha)).2

/-- In the finite-error branch, multiplying the native-real Bayes error by the
sample size gives exactly the compact-prior weighted local risk. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,v,p,R,n,hR,hp,hinterior,herrorSqInt), these specify the stated inputs. -/
lemma ofReal_nat_mul_sequentialBayesError_eq_weighted_localRisk
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p R : ℝ) (n : ℕ)
    (hR : 0 < R) (hp : InteriorAssignment p)
    (hinterior : ∀ a ∈ Icc (-R) R,
      InteriorMeans (parameterPath θ
        (scaledDirection ((Real.sqrt n)⁻¹) v) a))
    (herrorSqInt : Integrable
      (errorSqField (sequentialVTPrior R)
        (vtDensity P θ (scaledDirection ((Real.sqrt n)⁻¹) v)
          p n (-R) R)
        (vtTarget θ (scaledDirection ((Real.sqrt n)⁻¹) v))
        (P.estimate n))
      ((parameterMeasure (-R) R).prod (transcriptReferenceMeasure P n))) :
    ENNReal.ofReal ((n : ℝ) *
      ∫ z, errorSqField (sequentialVTPrior R)
        (vtDensity P θ (scaledDirection ((Real.sqrt n)⁻¹) v)
          p n (-R) R)
        (vtTarget θ (scaledDirection ((Real.sqrt n)⁻¹) v))
        (P.estimate n) z
        ∂((parameterMeasure (-R) R).prod (transcriptReferenceMeasure P n))) =
      ∫⁻ a, ENNReal.ofReal (sequentialVTPrior R a) *
        localRisk P θ (scaledDirection a v) p n
        ∂parameterMeasure (-R) R := by
  let d := scaledDirection ((Real.sqrt n)⁻¹) v
  let q := vtDensity P θ d p n (-R) R
  let g := vtTarget (X := Transcript (Z n)) θ d
  let w := sequentialVTPrior R
  let mu := transcriptReferenceMeasure P n
  have hscaledInt : Integrable (fun z : ℝ × Transcript (Z n) =>
      (n : ℝ) * errorSqField w q g (P.estimate n) z)
      ((parameterMeasure (-R) R).prod mu) := herrorSqInt.const_mul n
  have hscaledNonneg : ∀ z : ℝ × Transcript (Z n),
      0 ≤ (n : ℝ) * errorSqField w q g (P.estimate n) z := by
    intro z
    unfold errorSqField jointDensity
    exact mul_nonneg (Nat.cast_nonneg n)
      (mul_nonneg (sq_nonneg _)
        (mul_nonneg ((sequentialVTPrior_facts hR).nonneg z.1)
          (vtDensity_nonneg P θ d p n (-R) R hp hinterior z.1 z.2)))
  calc
    ENNReal.ofReal ((n : ℝ) *
        ∫ z, errorSqField (sequentialVTPrior R)
          (vtDensity P θ (scaledDirection ((Real.sqrt n)⁻¹) v)
            p n (-R) R)
          (vtTarget θ (scaledDirection ((Real.sqrt n)⁻¹) v))
          (P.estimate n) z
          ∂((parameterMeasure (-R) R).prod (transcriptReferenceMeasure P n))) =
      ENNReal.ofReal (∫ z, (n : ℝ) *
        errorSqField w q g (P.estimate n) z
        ∂((parameterMeasure (-R) R).prod mu)) := by
          congr 1
          rw [integral_const_mul]
    _ = ∫⁻ z, ENNReal.ofReal ((n : ℝ) *
        errorSqField w q g (P.estimate n) z)
        ∂((parameterMeasure (-R) R).prod mu) :=
      ofReal_integral_eq_lintegral_ofReal hscaledInt
        (Filter.Eventually.of_forall hscaledNonneg)
    _ = ∫⁻ a, ENNReal.ofReal (sequentialVTPrior R a) *
        localRisk P θ (scaledDirection a v) p n
        ∂parameterMeasure (-R) R := by
      rw [lintegral_prod]
      · apply lintegral_congr_ae
        have hmem : ∀ᵐ a ∂parameterMeasure (-R) R, a ∈ Icc (-R) R := by
          unfold parameterMeasure
          exact ae_restrict_mem measurableSet_Icc
        filter_upwards [hmem] with a ha
        rw [localRisk_scaledDirection_eq_lintegral_vtDensity
          P θ v p R a n hp hinterior ha]
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        apply lintegral_congr
        intro z
        rw [scaledError_sq_eq_nat_mul_vtTarget_error_sq P θ v a n z]
        unfold errorSqField jointDensity
        dsimp [w, q, g, d, mu]
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg n),
          ENNReal.ofReal_mul (sq_nonneg _),
          ENNReal.ofReal_mul ((sequentialVTPrior_facts hR).nonneg a),
          ENNReal.ofReal_mul (Nat.cast_nonneg n)]
        ac_rfl
      · fun_prop

/-- The finite van Trees bound, after sample scaling and compact-prior ordering, yields a finite-sample lower bound on local worst risk. Transcript Fisher control remains explicit. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hn,hR,hp,hinterior,hcover,herrorSqInt,hfisherSqInt,hfisher_le,hinfoPos), [the of Real van Trees Envelope le local Worst Risk of fisher control](goal).

Under the stated assumptions, the of Real van Trees Envelope le local Worst Risk of fisher control. -/
lemma ofReal_vanTreesEnvelope_le_localWorstRisk_of_fisher_control
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter)
    (p R H I : ℝ) (n : ℕ) (hn : 0 < n) (hR : 0 < R)
    (hp : InteriorAssignment p)
    (hinterior : ∀ a ∈ Icc (-R) R,
      InteriorMeans (parameterPath θ
        (scaledDirection ((Real.sqrt n)⁻¹) v) a))
    (hcover : R * Real.sqrt ((v 0) ^ 2 + (v 1) ^ 2) ≤ H)
    (herrorSqInt : Integrable
      (errorSqField (sequentialVTPrior R)
        (vtDensity P θ (scaledDirection ((Real.sqrt n)⁻¹) v)
          p n (-R) R)
        (vtTarget θ (scaledDirection ((Real.sqrt n)⁻¹) v))
        (P.estimate n))
      ((parameterMeasure (-R) R).prod (transcriptReferenceMeasure P n)))
    (hfisherSqInt : Integrable (fun z : ℝ × Transcript (Z n) =>
      sequentialVTPrior R z.1 *
        vtDensity P θ (scaledDirection ((Real.sqrt n)⁻¹) v)
          p n (-R) R z.1 z.2 *
        (likelihoodScore
          (vtDensity P θ (scaledDirection ((Real.sqrt n)⁻¹) v)
            p n (-R) R)
          (vtDensityDeriv P θ (scaledDirection ((Real.sqrt n)⁻¹) v)
            p n (-R) R) z.1 z.2) ^ 2)
      ((parameterMeasure (-R) R).prod (transcriptReferenceMeasure P n)))
    (hfisher_le :
      (∫ a, sequentialVTPrior R a *
        fisherInformation (transcriptReferenceMeasure P n)
          (vtDensity P θ (scaledDirection ((Real.sqrt n)⁻¹) v)
            p n (-R) R)
          (vtDensityDeriv P θ (scaledDirection ((Real.sqrt n)⁻¹) v)
            p n (-R) R) a
        ∂parameterMeasure (-R) R) ≤ I)
    (hinfoPos : 0 < priorInformation (-R) R
        (sequentialVTPrior R) (sequentialVTPriorDeriv R) +
      ∫ a, sequentialVTPrior R a *
        fisherInformation (transcriptReferenceMeasure P n)
          (vtDensity P θ (scaledDirection ((Real.sqrt n)⁻¹) v)
            p n (-R) R)
          (vtDensityDeriv P θ (scaledDirection ((Real.sqrt n)⁻¹) v)
            p n (-R) R) a
        ∂parameterMeasure (-R) R) :
    ENNReal.ofReal (contrast v ^ 2 / (I + 40 / R ^ 2)) ≤
      localWorstRisk P θ p H n := by
  let d := scaledDirection ((Real.sqrt n)⁻¹) v
  let bayesError := ∫ z, errorSqField (sequentialVTPrior R)
      (vtDensity P θ d p n (-R) R) (vtTarget θ d) (P.estimate n) z
      ∂((parameterMeasure (-R) R).prod (transcriptReferenceMeasure P n))
  have hvt := sequential_vanTrees_bayes_lower_bound_of_fisher_control
    P θ d p R I n hR hp hinterior (P.estimate n) (P.estimate_measurable n)
    herrorSqInt hfisherSqInt hfisher_le hinfoPos
  have hreal : contrast v ^ 2 / (I + 40 / R ^ 2) ≤
      (n : ℝ) * bayesError := by
    calc
      contrast v ^ 2 / (I + 40 / R ^ 2) =
          ((n : ℝ) * contrast d ^ 2) / (I + 40 / R ^ 2) := by
            rw [nat_mul_contrast_sampleScaledDirection_sq v hn]
      _ = (n : ℝ) * (contrast d ^ 2 / (I + 40 / R ^ 2)) := by ring
      _ ≤ (n : ℝ) * bayesError :=
        mul_le_mul_of_nonneg_left hvt (Nat.cast_nonneg n)
  have hweighted : ENNReal.ofReal ((n : ℝ) * bayesError) =
      ∫⁻ a, ENNReal.ofReal (sequentialVTPrior R a) *
        localRisk P θ (scaledDirection a v) p n
        ∂parameterMeasure (-R) R := by
    exact ofReal_nat_mul_sequentialBayesError_eq_weighted_localRisk
      P θ v p R n hR hp hinterior herrorSqInt
  have hprior := sequentialVTPrior_facts hR
  have hbayesLe :
      (∫⁻ a, ENNReal.ofReal (sequentialVTPrior R a) *
        localRisk P θ (scaledDirection a v) p n
        ∂parameterMeasure (-R) R) ≤ localWorstRisk P θ p H n := by
    exact (weighted_lintegral_le_uniform
      (parameterMeasure (-R) R) (sequentialVTPrior R)
      (fun a => localRisk P θ (scaledDirection a v) p n)
      (localWorstRisk P θ p H n)
      hprior.contDiff.continuous.measurable
      (measurable_localRisk_scaledDirection P θ v p n).aemeasurable
      (by
        unfold sequentialVTPrior
        exact smoothPrior_integrable_parameterMeasure (by linarith))
      (Filter.Eventually.of_forall hprior.nonneg) hprior.normalized
      (by
        have hmem : ∀ᵐ a ∂parameterMeasure (-R) R, a ∈ Icc (-R) R := by
          unfold parameterMeasure
          exact ae_restrict_mem measurableSet_Icc
        filter_upwards [hmem] with a ha
        apply localRisk_le_localWorstRisk
        refine ⟨(scaledDirection_mem_cover v ha).trans hcover, ?_⟩
        rw [← parameterPath_sampleScaledDirection_eq_localAlternative]
        exact hinterior a ha)).2
  exact (ENNReal.ofReal_le_ofReal hreal).trans (hweighted.le.trans hbayesLe)

/-- The finite-sample local-worst-risk lower bound holds for every estimator:
the finite-error branch uses van Trees, while a nonintegrable weighted squared
error forces the compact-prior Bayes risk and local worst risk to be infinite. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,v,p,R,H,I,n,hn,hR,hp,hinterior,hcover,hfisherSqInt,hfisher_le,hinfoPos), these specify the stated inputs. -/
lemma ofReal_vanTreesEnvelope_le_localWorstRisk_of_fisher_control_allErrors
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter)
    (p R H I : ℝ) (n : ℕ) (hn : 0 < n) (hR : 0 < R)
    (hp : InteriorAssignment p)
    (hinterior : ∀ a ∈ Icc (-R) R,
      InteriorMeans (parameterPath θ
        (scaledDirection ((Real.sqrt n)⁻¹) v) a))
    (hcover : R * Real.sqrt ((v 0) ^ 2 + (v 1) ^ 2) ≤ H)
    (hfisherSqInt : Integrable (fun z : ℝ × Transcript (Z n) =>
      sequentialVTPrior R z.1 *
        vtDensity P θ (scaledDirection ((Real.sqrt n)⁻¹) v)
          p n (-R) R z.1 z.2 *
        (likelihoodScore
          (vtDensity P θ (scaledDirection ((Real.sqrt n)⁻¹) v)
            p n (-R) R)
          (vtDensityDeriv P θ (scaledDirection ((Real.sqrt n)⁻¹) v)
            p n (-R) R) z.1 z.2) ^ 2)
      ((parameterMeasure (-R) R).prod (transcriptReferenceMeasure P n)))
    (hfisher_le :
      (∫ a, sequentialVTPrior R a *
        fisherInformation (transcriptReferenceMeasure P n)
          (vtDensity P θ (scaledDirection ((Real.sqrt n)⁻¹) v)
            p n (-R) R)
          (vtDensityDeriv P θ (scaledDirection ((Real.sqrt n)⁻¹) v)
            p n (-R) R) a
        ∂parameterMeasure (-R) R) ≤ I)
    (hinfoPos : 0 < priorInformation (-R) R
        (sequentialVTPrior R) (sequentialVTPriorDeriv R) +
      ∫ a, sequentialVTPrior R a *
        fisherInformation (transcriptReferenceMeasure P n)
          (vtDensity P θ (scaledDirection ((Real.sqrt n)⁻¹) v)
            p n (-R) R)
          (vtDensityDeriv P θ (scaledDirection ((Real.sqrt n)⁻¹) v)
            p n (-R) R) a
        ∂parameterMeasure (-R) R) :
    ENNReal.ofReal (contrast v ^ 2 / (I + 40 / R ^ 2)) ≤
      localWorstRisk P θ p H n := by
  let d := scaledDirection ((Real.sqrt n)⁻¹) v
  let q := vtDensity P θ d p n (-R) R
  let g := vtTarget (X := Transcript (Z n)) θ d
  let w := sequentialVTPrior R
  let mu := (parameterMeasure (-R) R).prod (transcriptReferenceMeasure P n)
  let F := errorSqField w q g (P.estimate n)
  have hFmeas : Measurable F :=
    (sequentialVanTreesProductMeasurable P θ d p R n hR
      (P.estimate n) (P.estimate_measurable n)).errorSq
  have hFnonneg : ∀ z, 0 ≤ F z := by
    intro z
    unfold F errorSqField jointDensity w q
    exact mul_nonneg (sq_nonneg _)
      (mul_nonneg ((sequentialVTPrior_facts hR).nonneg z.1)
        (vtDensity_nonneg P θ d p n (-R) R hp hinterior z.1 z.2))
  rcases integrable_or_lintegral_ofReal_eq_top F mu hFmeas hFnonneg with
      hfinite | hinfinite
  · exact ofReal_vanTreesEnvelope_le_localWorstRisk_of_fisher_control
      P θ v p R H I n hn hR hp hinterior hcover hfinite
      hfisherSqInt hfisher_le hinfoPos
  · have hscaledTop :
        (∫⁻ z, ENNReal.ofReal ((n : ℝ) * F z) ∂mu) = ∞ := by
      have hnTop : ENNReal.ofReal (n : ℝ) ≠ ∞ := ENNReal.ofReal_ne_top
      simp_rw [ENNReal.ofReal_mul (Nat.cast_nonneg n)]
      rw [lintegral_const_mul' _ _ hnTop, hinfinite]
      simp [hn.ne']
    have hweightedTop :
        (∫⁻ a, ENNReal.ofReal (sequentialVTPrior R a) *
          localRisk P θ (scaledDirection a v) p n
          ∂parameterMeasure (-R) R) = ∞ := by
      rw [← lintegral_scaledSequentialBayesError_eq_weighted_localRisk
        P θ v p R n hR hp hinterior]
      simpa [F, mu, w, q, g, d] using hscaledTop
    have hbayesLe := weightedLocalRisk_le_localWorstRisk
      P θ v p R H n hR hinterior hcover
    have hworstTop : localWorstRisk P θ p H n = ∞ := by
      apply top_unique
      rw [← hweightedTop]
      exact hbayesLe
    rw [hworstTop]
    exact le_top

end CausalSmith.Stat.LdpAteEfficiencySurface

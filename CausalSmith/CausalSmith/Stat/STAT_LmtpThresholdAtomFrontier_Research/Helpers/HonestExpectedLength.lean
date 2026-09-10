/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.HonestIntervalBasic
import Causalean.Mathlib.Indep
import Causalean.Mathlib.Probability.ConvergingTogether.CharFunBound

/-!
# Expected-length reductions for the bias-aware interval

This module reduces the expected length of the clipped honest interval to its
displayed sample-dependent radius.  It also records the exact mean of the
atom-frequency estimate, the population input needed to bound that radius.
-/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- On a probability space, integrating the square root of a nonnegative
integrable function is bounded by the square root of its integral. The result uses [the `hf` condition](hyp:hf), [the `hf0` condition](hyp:hf0), [the `hfInt` condition](hyp:hfInt). [This is the stated conclusion](goal).
-/
lemma integral_sqrt_le_sqrt_integral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω)
    (hfInt : Integrable f μ) :
    (∫ ω, Real.sqrt (f ω) ∂μ) ≤ Real.sqrt (∫ ω, f ω ∂μ) := by
  have hsMeas : AEStronglyMeasurable (fun ω => Real.sqrt (f ω)) μ :=
    hf.sqrt.aestronglyMeasurable
  have hsSqInt : Integrable (fun ω => (Real.sqrt (f ω)) ^ 2) μ := by
    simpa only [Real.sq_sqrt (hf0 _)] using hfInt
  have hsLp : MemLp (fun ω => Real.sqrt (f ω)) 2 μ :=
    (memLp_two_iff_integrable_sq hsMeas).mpr hsSqInt
  have hcs :=
    Causalean.Mathlib.Probability.ConvergingTogether.integral_abs_le_sqrt_integral_sq
      μ (fun ω => Real.sqrt (f ω)) hsLp
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (hf0 _)] using hcs

/-- Statistics computed from the atom block and local-regression block factor
under the canonical product law. The result uses [the `hprob` condition](hyp:hprob), [the `F` condition](hyp:F), [the `G` condition](hyp:G), [the `hF` condition](hyp:hF), [the `hG` condition](hyp:hG). [This is the stated conclusion](goal).
-/
lemma integral_mul_I1_I2
    {J n : ℕ} (P : ClampLaw J) (B : SplitBlocks n)
    (hprob : IsProbabilityMeasure P.dataMeasure)
    (F : ((i : {i // i ∈ B.I1}) → ClampObs J) → ℝ)
    (G : ((i : {i // i ∈ B.I2}) → ClampObs J) → ℝ)
    (hF : Measurable F) (hG : Measurable G) :
    (∫ z, F (Causalean.finsetCoordProj B.I1 z) *
        G (Causalean.finsetCoordProj B.I2 z) ∂iidProduct P n) =
      (∫ z, F (Causalean.finsetCoordProj B.I1 z) ∂iidProduct P n) *
        ∫ z, G (Causalean.finsetCoordProj B.I2 z) ∂iidProduct P n := by
  letI : IsProbabilityMeasure P.dataMeasure := hprob
  have hi : ProbabilityTheory.iIndepFun
      (fun (i : Fin n) (z : Fin n → ClampObs J) => z i) (iidProduct P n) := by
    unfold iidProduct
    exact ProbabilityTheory.iIndepFun_pi
      (X := fun _ : Fin n => id) (fun _ => measurable_id.aemeasurable)
  have hind := hi.indepFun_finset B.I1 B.I2 B.disjoint12
    (fun i => measurable_pi_apply i)
  change (∫ z, F (fun i => z i.1) * G (fun i => z i.1) ∂iidProduct P n) =
    (∫ z, F (fun i => z i.1) ∂iidProduct P n) *
      ∫ z, G (fun i => z i.1) ∂iidProduct P n
  exact hind.integral_fun_comp_mul_comp
    (Causalean.measurable_finsetCoordProj B.I1).aemeasurable
    (Causalean.measurable_finsetCoordProj B.I2).aemeasurable
    hF.aestronglyMeasurable hG.aestronglyMeasurable

/-- The displayed radius of the bias-aware interval. -/
def honestRadius (B : SplitBlocks n) (z : Fin n → ClampObs J)
    (beta kappa L cminus cplus delta h alpha : ℝ) : ℝ :=
  Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2) /
      Real.sqrt (B.I0.card : ℝ) +
    ∑ x : Fin J,
      stratumRadius B z x (ellOf beta) beta kappa L cminus cplus delta h
        (Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2))
        (Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2) /
          Real.sqrt (B.I1.card : ℝ))

/-- Under the regime restrictions and nonnegative bandwidth, the displayed
honest radius is nonnegative. The result uses [the `hreg` condition](hyp:hreg), [the `hn` condition](hyp:hn), [the `hh` condition](hyp:hh). [This is the stated conclusion](goal).
-/
lemma honestRadius_nonneg
    (J n : ℕ) (B : SplitBlocks n)
    (beta kappa L cminus cplus pmin deltaBar alpha delta h : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha)
    (hn : 4 ≤ n) (hh : 0 ≤ h) (z : Fin n → ClampObs J) :
    0 ≤ honestRadius B z beta kappa L cminus cplus delta h alpha := by
  simpa only [honestRadius] using
    honestInterval_radius_nonneg J n B beta kappa L cminus cplus pmin
      deltaBar alpha delta h hreg hn hh z

/-- Clipping the honest interval to the outcome range cannot make it longer
than twice its displayed radius. The result uses [the `hreg` condition](hyp:hreg), [the `hn` condition](hyp:hn), [the `hh` condition](hyp:hh). [This is the stated conclusion](goal).
-/
lemma honestInterval_length_le_two_radius
    (J n : ℕ) (B : SplitBlocks n)
    (beta kappa L cminus cplus pmin deltaBar alpha delta h : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha)
    (hn : 4 ≤ n) (hh : 0 ≤ h) (z : Fin n → ClampObs J) :
    intervalLength
        (honestInterval B z (ellOf beta) beta kappa L cminus cplus delta h alpha) ≤
      2 * honestRadius B z beta kappa L cminus cplus delta h alpha := by
  let center := totalGramEstimator B z (ellOf beta) kappa cminus cplus delta h
  let radius := honestRadius B z beta kappa L cminus cplus delta h alpha
  have hr : 0 ≤ radius := by
    simpa only [radius] using honestRadius_nonneg J n B beta kappa L cminus
      cplus pmin deltaBar alpha delta h hreg hn hh z
  have hmin : min 1 (center + radius) ≤ center + radius := min_le_right _ _
  have hmax : center - radius ≤ max 0 (center - radius) := le_max_right _ _
  simp only [honestInterval, honest_intervalLength_Icc_eq]
  change max 0
      (min 1 (center + radius) - max 0 (center - radius)) ≤ 2 * radius
  apply max_le
  · positivity
  · linarith

/-- A uniform modelwise expected-length bound passes through the real
supremum convention used for the concrete honest interval. The result uses [the `hreg` condition](hyp:hreg), [the `hupper` condition](hyp:hupper). [This is the stated conclusion](goal).
-/
lemma honestInterval_modelSup_le
    (J n : ℕ) (B : SplitBlocks n)
    (beta kappa L cminus cplus pmin deltaBar alpha delta h U : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha)
    (hupper : ∀ (P : ClampLaw J),
      ClampModel P beta kappa L cminus cplus pmin →
      (∫ z, intervalLength
          (honestInterval B z (ellOf beta) beta kappa L cminus cplus delta h alpha)
            ∂iidProduct P n) ≤ U) :
    sSup {v : ℝ | ∃ P : ClampLaw J,
      ClampModel P beta kappa L cminus cplus pmin ∧ IidSampling P n ∧
      v = ∫ z, intervalLength
        (honestInterval B z (ellOf beta) beta kappa L cminus cplus delta h alpha)
          ∂iidProduct P n} ≤ U := by
  apply csSup_le
  · let P0 := minimaxClampLaw J kappa (fun _ : Fin J × ℝ => 0)
    have hP0 : ClampModel P0 beta kappa L cminus cplus pmin :=
      minimaxCenter_mem_model J beta kappa L cminus cplus pmin deltaBar alpha hreg
    exact ⟨(∫ z, intervalLength
        (honestInterval B z (ellOf beta) beta kappa L cminus cplus delta h alpha)
          ∂iidProduct P0 n), P0, hP0, clampModel_iidSampling hP0, rfl⟩
  · intro v hv
    rcases hv with ⟨P, hP, _hsampling, rfl⟩
    exact hupper P hP

/-- The mean empirical atom frequency is bounded by its population thinning
envelope plus the root-block fluctuation scale. The result uses [the `hmodel` condition](hyp:hmodel), [the `hreg` condition](hyp:hreg), [the `hcard` condition](hyp:hcard), [the `hdelta` condition](hyp:hdelta). [This is the stated conclusion](goal).
-/
lemma integral_atomEstimate_le_envelope
    {J n : ℕ} (P : ClampLaw J) (B : SplitBlocks n) (x : Fin J)
    (beta kappa L cminus cplus pmin deltaBar alpha delta : ℝ)
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha)
    (hcard : 0 < B.I1.card) (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar) :
    (∫ z, atomEstimate B z x delta ∂iidProduct P n) ≤
      (1 / 2 : ℝ) * Real.sqrt (B.I1.card : ℝ)⁻¹ +
        cplus * delta ^ (kappa + 1) / (kappa + 1) := by
  letI : IsProbabilityMeasure P.dataMeasure := hmodel.probability
  letI : IsProbabilityMeasure (iidProduct P n) := by
    unfold iidProduct
    infer_instance
  let m := P.px x * atomMass P x delta
  let f := fun z : Fin n → ClampObs J => atomEstimate B z x delta
  have hfMeas : Measurable f := atomEstimate_measurable B x delta
  have hfInt : Integrable f (iidProduct P n) := by
    refine Integrable.of_bound hfMeas.aestronglyMeasurable 1 ?_
    filter_upwards with z
    have hz := atomEstimate_mem_Icc B z x delta
    rw [Real.norm_eq_abs, abs_of_nonneg hz.1]
    exact hz.2
  have hd1 : delta ≤ 1 := hdelta.2.trans (by
    rcases hreg with ⟨_, _, _, _, _, _, _, _, _, _, hdBar, _, _⟩
    exact hdBar.le)
  have hdiffInt : Integrable (fun z => |f z - m|) (iidProduct P n) := by
    exact (hfInt.sub (integrable_const m)).abs
  have hpoint : ∀ z, f z ≤ |f z - m| + m := by
    intro z
    linarith [le_abs_self (f z - m)]
  have hint : (∫ z, f z ∂iidProduct P n) ≤
      (∫ z, |f z - m| ∂iidProduct P n) + m := by
    calc
      _ ≤ ∫ z, (|f z - m| + m) ∂iidProduct P n :=
        integral_mono hfInt (hdiffInt.add (integrable_const m)) hpoint
      _ = _ := by rw [integral_add hdiffInt (integrable_const m)]; simp
  have hfluct : (∫ z, |f z - m| ∂iidProduct P n) ≤
      (1 / 2 : ℝ) * Real.sqrt (B.I1.card : ℝ)⁻¹ := by
    simpa [f, m] using atomEstimate_l1_le P hmodel B hcard x hdelta.1 hd1
  have hmean : m ≤ cplus * delta ^ (kappa + 1) / (kappa + 1) := by
    have habs := abs_atomCoefficient_le_envelope J P hmodel hreg x hdelta
    have hm0 := atomCoefficient_mem_Icc P hmodel x hd1 |>.1
    simpa [m, abs_of_nonneg hm0] using habs
  exact hint.trans (add_le_add hfluct hmean)

/-- The expected square root of the stabilized local-weight energy is bounded
by the square root of the existing integrated energy envelope. The result uses [the `hsampling` condition](hyp:hsampling), [the `hh` condition](hyp:hh), [the `hlambda` condition](hyp:hlambda), [the `hp` condition](hyp:hp), [the `hcard` condition](hyp:hcard), [the `hmean` condition](hyp:hmean). [This is the stated conclusion](goal).
-/
lemma integral_sqrt_interceptWeight_energy_le
    {J n ell : ℕ} (P : ClampLaw J) (B : SplitBlocks n) (x : Fin J)
    (kappa cminus cplus delta h p : ℝ)
    (hsampling : IidSampling P n) (hh : 0 < h)
    (hlambda : 0 < lambdaStar ell kappa cminus cplus)
    (hp : 0 < p) (hcard : 0 < B.I2.card)
    (hmean : ∫ o, localWindowWeight x delta h o ∂P.dataMeasure = p) :
    (∫ z, Real.sqrt (∑ i ∈ B.I2,
        (interceptWeight B z x ell kappa cminus cplus delta h i) ^ 2)
        ∂iidProduct P n) ≤
      Real.sqrt
        (2 * (4 * (ell + 1 : ℝ) /
              lambdaStar ell kappa cminus cplus ^ 2) /
            ((B.I2.card : ℝ) * p) +
          2 * (4 * (ell + 1 : ℝ) /
              lambdaStar ell kappa cminus cplus ^ 2) *
            Real.exp (-((B.I2.card : ℝ) * p) / 20)) := by
  letI : IsProbabilityMeasure P.dataMeasure := hsampling.1
  letI : IsProbabilityMeasure (iidProduct P n) := by
    unfold iidProduct
    infer_instance
  let energy : (Fin n → ClampObs J) → ℝ := fun z => ∑ i ∈ B.I2,
    (interceptWeight B z x ell kappa cminus cplus delta h i) ^ 2
  have heMeas : Measurable energy := by
    exact Finset.measurable_fun_sum B.I2 fun i _ =>
      (interceptWeight_measurable (ell := ell) B x kappa cminus cplus delta h i).pow_const 2
  have he0 : ∀ z, 0 ≤ energy z := fun z => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have heInt : Integrable energy (iidProduct P n) := by
    have hbase := localRegression_weight_energy_integrable B P x kappa cminus
      cplus delta h hh hlambda
    apply hbase.congr
    filter_upwards with z
    dsimp only [energy]
    simp_rw [localRegressionDesignWeight_apply (ell := ell), ite_pow,
      zero_pow (by norm_num : 2 ≠ 0)]
    rw [← Finset.sum_filter]
    simp
  have hsqrt := integral_sqrt_le_sqrt_integral (iidProduct P n) energy heMeas he0 heInt
  refine hsqrt.trans (Real.sqrt_le_sqrt ?_)
  calc
    (∫ z, energy z ∂iidProduct P n) =
        ∫ z, ∑ i,
          (localRegressionDesignWeight (ell := ell) B x kappa cminus cplus delta h
            (Causalean.Mathlib.Probability.designVector
              (fun o : ClampObs J => (o.X, o.A)) z) i) ^ 2 ∂iidProduct P n := by
      apply integral_congr_ae
      filter_upwards with z
      dsimp only [energy]
      simp_rw [localRegressionDesignWeight_apply (ell := ell), ite_pow,
        zero_pow (by norm_num : 2 ≠ 0)]
      rw [← Finset.sum_filter]
      simp
    _ ≤ _ := localRegression_weight_energy_integral_le P hsampling B x
      kappa cminus cplus delta h p hh hlambda hp hcard hmean

/-- Each per-stratum radius is bounded by a good-Gram bias/noise expression
plus the indicator of Gram failure. The result uses [the `hbeta` condition](hyp:hbeta), [the `hL` condition](hyp:hL), [the `hh` condition](hyp:hh), [the `ht` condition](hyp:ht), [the `hb1` condition](hyp:hb1), [the `hlambda` condition](hyp:hlambda). [This is the stated conclusion](goal).
-/
lemma stratumRadius_le_good_expression_add_bad
    {J n : ℕ} (B : SplitBlocks n) (z : Fin n → ClampObs J) (x : Fin J)
    (beta kappa L cminus cplus delta h t b1 : ℝ)
    (hbeta : 0 ≤ beta) (hL : 0 ≤ L) (hh : 0 < h)
    (ht : 0 ≤ t) (hb1 : 0 ≤ b1)
    (hlambda : 0 < lambdaStar (ellOf beta) kappa cminus cplus) :
    stratumRadius B z x (ellOf beta) beta kappa L cminus cplus delta h t b1 ≤
      (atomEstimate B z x delta + b1) *
        (L * h ^ beta *
            (2 * Real.sqrt (ellOf beta + 1 : ℝ) /
              lambdaStar (ellOf beta) kappa cminus cplus) +
          t * Real.sqrt (∑ i ∈ B.I2,
            (interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i) ^ 2)) +
        b1 +
          {w : Fin n → ClampObs J |
            ¬ GoodGramEvent B w x (ellOf beta) kappa cminus cplus delta h}.indicator
              (fun _ => (1 : ℝ)) z := by
  have hatom := atomEstimate_mem_Icc B z x delta
  have hfac : 0 ≤ atomEstimate B z x delta + b1 := by linarith [hatom.1]
  have hbias : 0 ≤ L * h ^ beta *
      (2 * Real.sqrt (ellOf beta + 1 : ℝ) /
        lambdaStar (ellOf beta) kappa cminus cplus) := by positivity
  have hnoise : 0 ≤ t * Real.sqrt (∑ i ∈ B.I2,
      (interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i) ^ 2) :=
    mul_nonneg ht (Real.sqrt_nonneg _)
  by_cases hg : GoodGramEvent B z x (ellOf beta) kappa cminus cplus delta h
  · rw [stratumRadius, if_pos hg, Set.indicator_of_notMem]
    · simp only [add_zero]
      have hinner :
          L * h ^ beta * ∑ i ∈ B.I2,
                |interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i| +
              t * Real.sqrt (∑ i ∈ B.I2,
                (interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i) ^ 2) ≤
            L * h ^ beta *
                (2 * Real.sqrt (ellOf beta + 1 : ℝ) /
                  lambdaStar (ellOf beta) kappa cminus cplus) +
              t * Real.sqrt (∑ i ∈ B.I2,
                (interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i) ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left
          (goodGram_weight_controls B z x kappa cminus cplus delta h hh hlambda hg).2.1
          (mul_nonneg hL (Real.rpow_nonneg hh.le _))) le_rfl
      exact add_le_add (mul_le_mul_of_nonneg_left hinner hfac) le_rfl
    · simpa using hg
  · rw [stratumRadius, if_neg hg, Set.indicator_of_mem]
    · nlinarith [mul_nonneg hfac (add_nonneg hbias hnoise), hatom.2]
    · simpa using hg

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier

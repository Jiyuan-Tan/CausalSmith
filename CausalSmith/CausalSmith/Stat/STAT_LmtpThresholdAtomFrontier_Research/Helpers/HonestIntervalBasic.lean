/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.TMinimaxRisk
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.HonestLengthLower

/-! # Measurability and elementary length bounds for the honest interval -/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The convex-hull length of a nonempty closed interval is its nonnegative
endpoint difference. [This is the stated conclusion](goal).
-/
lemma honest_intervalLength_Icc_eq (a b : ℝ) :
    intervalLength (Set.Icc a b) = max 0 (b - a) := by
  unfold intervalLength
  by_cases h : a ≤ b
  · simp [h]
  · have h' : b < a := lt_of_not_ge h
    simp [Set.Icc_eq_empty h, h'.le]

/-- The sample-dependent per-stratum honest radius is measurable. [This is the stated conclusion](goal).
-/
lemma honest_stratumRadius_measurable {J n ell : ℕ} (B : SplitBlocks n)
    (x : Fin J) (beta kappa L cminus cplus delta h tAlpha b1 : ℝ) :
    Measurable fun z : Fin n → ClampObs J =>
      stratumRadius B z x ell beta kappa L cminus cplus delta h tAlpha b1 := by
  classical
  unfold stratumRadius
  refine Measurable.ite
    (goodGramEvent_measurable B x kappa cminus cplus delta h) ?_ ?_
  · have habs := Finset.measurable_fun_sum B.I2 fun i _ =>
      (interceptWeight_measurable (ell := ell) B x kappa cminus cplus delta h i).abs
    have hsq := Finset.measurable_fun_sum B.I2 fun i _ =>
      (interceptWeight_measurable (ell := ell) B x kappa cminus cplus delta h i).pow_const 2
    exact (((atomEstimate_measurable B x delta).add measurable_const).mul
      (((measurable_const.mul measurable_const).mul habs).add
        (measurable_const.mul hsq.sqrt))).add measurable_const
  · exact (atomEstimate_measurable B x delta).add measurable_const

/-- Once the split blocks are nonempty, the displayed honest radius is
nonnegative under the regime restrictions. The result uses [the `hreg` condition](hyp:hreg), [the `hn` condition](hyp:hn), [the `hh` condition](hyp:hh). [This is the stated conclusion](goal).
-/
lemma honestInterval_radius_nonneg
    (J n : ℕ) (B : SplitBlocks n)
    (beta kappa L cminus cplus pmin deltaBar alpha delta h : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha)
    (hn : 4 ≤ n) (hh : 0 ≤ h) :
    ∀ z : Fin n → ClampObs J,
      let tAlpha := Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2)
      let b0 := tAlpha / Real.sqrt (B.I0.card : ℝ)
      let b1 := tAlpha / Real.sqrt (B.I1.card : ℝ)
      0 ≤ b0 + ∑ x : Fin J,
        stratumRadius B z x (ellOf beta) beta kappa L cminus cplus delta h
          tAlpha b1 := by
  intro z
  dsimp only
  rcases hreg with ⟨hJ, hbeta, hkappa, hL, hcminus, hcminus_le, hcplus,
    hpmin, hpmin_le, hdeltaBar, hdeltaBar1, ha, ha_half⟩
  have ht : 0 ≤ Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2) :=
    Real.sqrt_nonneg _
  have hI0 : 0 < (B.I0.card : ℝ) := by
    have hc := B.card_I0
    exact_mod_cast (show 0 < B.I0.card by omega)
  have hI1 : 0 < (B.I1.card : ℝ) := by
    have hc := B.card_I1
    exact_mod_cast (show 0 < B.I1.card by omega)
  have hb0 : 0 ≤ Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2) /
      Real.sqrt (B.I0.card : ℝ) := div_nonneg ht (Real.sqrt_nonneg _)
  have hb1 : 0 ≤ Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2) /
      Real.sqrt (B.I1.card : ℝ) := div_nonneg ht (Real.sqrt_nonneg _)
  apply add_nonneg hb0
  apply Finset.sum_nonneg
  intro x hx
  unfold stratumRadius atomEstimate blockAverage
  split_ifs <;> positivity

/-- The honest interval has measurable ordered endpoints for all sufficiently
large sample sizes. The result uses [the `hreg` condition](hyp:hreg), [the `hn` condition](hyp:hn), [the `hh` condition](hyp:hh). [This is the stated conclusion](goal).
-/
lemma honestInterval_observedMeasurable
    (J n : ℕ) (B : SplitBlocks n)
    (beta kappa L cminus cplus pmin deltaBar alpha delta : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha)
    (hn : 4 ≤ n)
    (hh : 0 ≤ infoBandwidth n delta beta kappa deltaBar) :
    ObservedMeasurableInterval (fun z : Fin n → ClampObs J =>
      honestInterval B z (ellOf beta) beta kappa L cminus cplus delta
        (infoBandwidth n delta beta kappa deltaBar) alpha) := by
  classical
  let tAlpha := Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2)
  let b0 := tAlpha / Real.sqrt (B.I0.card : ℝ)
  let b1 := tAlpha / Real.sqrt (B.I1.card : ℝ)
  let center := fun z : Fin n → ClampObs J =>
    totalGramEstimator B z (ellOf beta) kappa cminus cplus delta
      (infoBandwidth n delta beta kappa deltaBar)
  let radius := fun z : Fin n → ClampObs J => b0 + ∑ x : Fin J,
    stratumRadius B z x (ellOf beta) beta kappa L cminus cplus delta
      (infoBandwidth n delta beta kappa deltaBar) tAlpha b1
  let lo := fun z => max 0 (center z - radius z)
  let hi := fun z => min 1 (center z + radius z)
  have hc : Measurable center :=
    totalGramEstimator_measurable B kappa cminus cplus delta _
  have hr : Measurable radius := measurable_const.add
    (Finset.measurable_fun_sum _ fun x _ =>
      honest_stratumRadius_measurable B x beta kappa L cminus cplus delta _
        tAlpha b1)
  have hlo : Measurable lo := measurable_const.max (hc.sub hr)
  have hhi : Measurable hi := measurable_const.min (hc.add hr)
  refine ⟨lo, hi, hlo, hhi, ?_, ?_⟩
  · intro z
    have hcenter := clampUnit_mem_Icc
      (retainedEstimate B z delta + ∑ x : Fin J,
        atomEstimate B z x delta * localRegressionEstimate B z x (ellOf beta)
          kappa cminus cplus delta (infoBandwidth n delta beta kappa deltaBar))
    have hradius : 0 ≤ radius z := by
      simpa only [radius, tAlpha, b0, b1] using
        honestInterval_radius_nonneg J n B beta kappa L cminus cplus pmin
          deltaBar alpha delta (infoBandwidth n delta beta kappa deltaBar)
          hreg hn hh z
    dsimp only [lo, hi]
    apply le_min
    · apply max_le
      · norm_num
      · dsimp only [center]
        rw [show totalGramEstimator B z (ellOf beta) kappa cminus cplus delta
          (infoBandwidth n delta beta kappa deltaBar) =
            clampUnit (retainedEstimate B z delta + ∑ x : Fin J,
              atomEstimate B z x delta * localRegressionEstimate B z x
                (ellOf beta) kappa cminus cplus delta
                  (infoBandwidth n delta beta kappa deltaBar)) by rfl]
        linarith [hcenter.2]
    · apply max_le
      · dsimp only [center]
        rw [show totalGramEstimator B z (ellOf beta) kappa cminus cplus delta
          (infoBandwidth n delta beta kappa deltaBar) =
            clampUnit (retainedEstimate B z delta + ∑ x : Fin J,
              atomEstimate B z x delta * localRegressionEstimate B z x
                (ellOf beta) kappa cminus cplus delta
                  (infoBandwidth n delta beta kappa deltaBar)) by rfl]
        linarith [hcenter.1]
      · linarith
  · intro z
    rfl

/-- Intersecting the honest interval with the outcome range bounds its length
by one on every sample. [This is the stated conclusion](goal).
-/
lemma honestInterval_length_le_one {J n : ℕ} (B : SplitBlocks n)
    (beta kappa L cminus cplus delta h alpha : ℝ)
    (z : Fin n → ClampObs J) :
    intervalLength (honestInterval B z (ellOf beta) beta kappa L cminus cplus
      delta h alpha) ≤ 1 := by
  simp only [honestInterval, honest_intervalLength_Icc_eq]
  apply max_le
  · norm_num
  · have hmin := min_le_left (1 : ℝ)
        (totalGramEstimator B z (ellOf beta) kappa cminus cplus delta h +
          (Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2) /
              Real.sqrt (B.I0.card : ℝ) + ∑ x : Fin J,
            stratumRadius B z x (ellOf beta) beta kappa L cminus cplus delta h
              (Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2))
              (Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2) /
                Real.sqrt (B.I1.card : ℝ))))
    have hmax := le_max_left (0 : ℝ)
        (totalGramEstimator B z (ellOf beta) kappa cminus cplus delta h -
          (Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2) /
              Real.sqrt (B.I0.card : ℝ) + ∑ x : Fin J,
            stratumRadius B z x (ellOf beta) beta kappa L cminus cplus delta h
              (Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2))
              (Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2) /
                Real.sqrt (B.I1.card : ℝ))))
    linarith

/-- The displayed interval length is measurable as a function of the observed
sample. [This is the stated conclusion](goal).
-/
lemma honestInterval_length_measurable {J n : ℕ} (B : SplitBlocks n)
    (beta kappa L cminus cplus delta h alpha : ℝ) :
    Measurable fun z : Fin n → ClampObs J =>
      intervalLength (honestInterval B z (ellOf beta) beta kappa L cminus
        cplus delta h alpha) := by
  classical
  let tAlpha := Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2)
  let b0 := tAlpha / Real.sqrt (B.I0.card : ℝ)
  let b1 := tAlpha / Real.sqrt (B.I1.card : ℝ)
  let center := fun z : Fin n → ClampObs J =>
    totalGramEstimator B z (ellOf beta) kappa cminus cplus delta h
  let radius := fun z : Fin n → ClampObs J => b0 + ∑ x : Fin J,
    stratumRadius B z x (ellOf beta) beta kappa L cminus cplus delta h tAlpha b1
  have hc : Measurable center :=
    totalGramEstimator_measurable B kappa cminus cplus delta h
  have hr : Measurable radius := measurable_const.add
    (Finset.measurable_fun_sum _ fun x _ =>
      honest_stratumRadius_measurable B x beta kappa L cminus cplus delta h
        tAlpha b1)
  have hm : Measurable fun z =>
      max 0 (min 1 (center z + radius z) - max 0 (center z - radius z)) :=
    measurable_const.max
      ((measurable_const.min (hc.add hr)).sub (measurable_const.max (hc.sub hr)))
  simpa only [honestInterval, honest_intervalLength_Icc_eq, center, radius,
    tAlpha, b0, b1] using hm

/-- A real uniform expected-length upper bound upgrades to the extended-real
worst-length convention. The result uses [the `hupper` condition](hyp:hupper). [This is the stated conclusion](goal).
-/
lemma clampProcedureWorstLength_honestInterval_le_ofReal
    (J n : ℕ) (B : SplitBlocks n)
    (beta kappa L cminus cplus pmin delta h alpha U : ℝ)
    (hupper : sSup {v : ℝ | ∃ P : ClampLaw J,
      ClampModel P beta kappa L cminus cplus pmin ∧ IidSampling P n ∧
      v = ∫ z, intervalLength
        (honestInterval B z (ellOf beta) beta kappa L cminus cplus delta h alpha)
          ∂iidProduct P n} ≤ U) :
    clampProcedureWorstLength J n beta kappa L cminus cplus pmin
      (fun z => honestInterval B z (ellOf beta) beta kappa L cminus cplus
        delta h alpha) ≤ ENNReal.ofReal U := by
  unfold clampProcedureWorstLength
  apply sSup_le
  intro v hv
  rcases hv with ⟨P, hP, rfl⟩
  letI : IsProbabilityMeasure P.dataMeasure := hP.probability
  letI : IsProbabilityMeasure (iidProduct P n) := by unfold iidProduct; infer_instance
  let f := fun z : Fin n → ClampObs J => intervalLength
    (honestInterval B z (ellOf beta) beta kappa L cminus cplus delta h alpha)
  have hfmeas : Measurable f := honestInterval_length_measurable B beta kappa L
    cminus cplus delta h alpha
  have hfnn : ∀ᵐ z ∂iidProduct P n, 0 ≤ f z :=
    ae_of_all _ fun _ => le_max_left _ _
  have hfint : Integrable f (iidProduct P n) := by
    refine Integrable.of_bound hfmeas.aestronglyMeasurable 1 ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    exact honestInterval_length_le_one B beta kappa L cminus cplus delta h alpha z
  simp_rw [intervalLengthENNReal]
  rw [← ofReal_integral_eq_lintegral_ofReal hfint hfnn]
  apply ENNReal.ofReal_le_ofReal
  have hbdd : BddAbove {v : ℝ | ∃ Q : ClampLaw J,
      ClampModel Q beta kappa L cminus cplus pmin ∧ IidSampling Q n ∧
      v = ∫ z, intervalLength
        (honestInterval B z (ellOf beta) beta kappa L cminus cplus delta h alpha)
          ∂iidProduct Q n} := by
    refine ⟨1, ?_⟩
    rintro w ⟨Q, hQ, _hiid, rfl⟩
    letI : IsProbabilityMeasure Q.dataMeasure := hQ.probability
    letI : IsProbabilityMeasure (iidProduct Q n) := by unfold iidProduct; infer_instance
    have hqmeas := honestInterval_length_measurable (J := J) B beta kappa L
      cminus cplus delta h alpha
    have hqint : Integrable (fun z : Fin n → ClampObs J => intervalLength
        (honestInterval B z (ellOf beta) beta kappa L cminus cplus delta h alpha))
        (iidProduct Q n) := by
      refine Integrable.of_bound hqmeas.aestronglyMeasurable 1 ?_
      filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
      exact honestInterval_length_le_one B beta kappa L cminus cplus delta h alpha z
    exact (integral_mono_ae hqint (integrable_const 1)
      (ae_of_all _ fun z => honestInterval_length_le_one B beta kappa L
        cminus cplus delta h alpha z)).trans_eq (by simp)
  have hmem : (∫ z, f z ∂iidProduct P n) ∈ {v : ℝ | ∃ Q : ClampLaw J,
      ClampModel Q beta kappa L cminus cplus pmin ∧ IidSampling Q n ∧
      v = ∫ z, intervalLength
        (honestInterval B z (ellOf beta) beta kappa L cminus cplus delta h alpha)
          ∂iidProduct Q n} := ⟨P, hP, clampModel_iidSampling hP, rfl⟩
  exact (le_csSup hbdd hmem).trans hupper

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier

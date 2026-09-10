/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.ContinuityProcedureBounds

/-! # Expected length of the continuity-only interval

This file bounds the expected length of the two-block Hoeffding interval by
its deterministic root-block radii and the polynomial threshold-mass envelope.
-/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

noncomputable section

/-- The continuity-only interval has length at most twice its displayed
radius, before intersection with the outcome range. [This is the stated conclusion](goal).
-/
lemma contHoeffdingInterval_length_le_radius {J n : ℕ} (B : SplitBlocks n)
    (delta alpha : ℝ) (z : Fin n → ClampObs J) :
    intervalLength (contHoeffdingInterval B z delta alpha) ≤
      2 * (Real.sqrt (Real.log (4 / alpha) / (2 * (B.I0.card : ℝ))) +
        Real.sqrt (Real.log (4 / alpha) / (2 * (B.I1.card : ℝ))) +
        (∑ x : Fin J, atomEstimate B z x delta) / 2) := by
  let radius :=
    Real.sqrt (Real.log (4 / alpha) / (2 * (B.I0.card : ℝ))) +
      Real.sqrt (Real.log (4 / alpha) / (2 * (B.I1.card : ℝ))) +
      (∑ x : Fin J, atomEstimate B z x delta) / 2
  have hrad : 0 ≤ radius := by
    dsimp [radius]
    have hatom : 0 ≤ ∑ x : Fin J, atomEstimate B z x delta :=
      Finset.sum_nonneg fun x _ => (atomEstimate_mem_Icc B z x delta).1
    positivity
  have hcI := clampUnit_mem_Icc
    (retainedEstimate B z delta +
      (1 / 2 : ℝ) * ∑ x : Fin J, atomEstimate B z x delta)
  have hord : max 0 (contFallbackEstimator B z delta - radius) ≤
      min 1 (contFallbackEstimator B z delta + radius) := by
    apply le_min
    · exact max_le (by norm_num) (by
        unfold contFallbackEstimator
        linarith [hcI.2])
    · exact max_le (by
        unfold contFallbackEstimator
        linarith [hcI.1]) (by linarith)
  simp only [contHoeffdingInterval, intervalLength]
  rw [csSup_Icc hord, csInf_Icc hord]
  apply max_le
  · positivity
  · have hhi := min_le_right (1 : ℝ)
        (contFallbackEstimator B z delta + radius)
    have hlo := le_max_right (0 : ℝ)
        (contFallbackEstimator B z delta - radius)
    dsimp [radius] at *
    linarith

/-- Under a continuity-only model, the real expected interval length is
bounded by the two deterministic Hoeffding radii, the atom-estimation noise,
and the polynomial threshold-mass envelope. The result uses [the `hP` condition](hyp:hP), [the `hreg` condition](hyp:hreg), [the `hdelta` condition](hyp:hdelta), [the `hcard1` condition](hyp:hcard1). [This is the stated conclusion](goal).
-/
lemma contHoeffdingInterval_integral_length_le
    {J n : ℕ} (P : ClampLaw J) (B : SplitBlocks n)
    (kappa cminus cplus pmin deltaBar delta alpha : ℝ)
    (hP : ContClampModel P kappa cminus cplus pmin deltaBar)
    (hreg : ContDesignConstants J kappa cminus cplus pmin deltaBar)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar)
    (hcard1 : 0 < B.I1.card) :
    (∫ z, intervalLength (contHoeffdingInterval B z delta alpha)
        ∂iidProduct P n) ≤
      2 * Real.sqrt (Real.log (4 / alpha) / (2 * (B.I0.card : ℝ))) +
      2 * Real.sqrt (Real.log (4 / alpha) / (2 * (B.I1.card : ℝ))) +
      (J : ℝ) * ((1 / 2 : ℝ) * Real.sqrt (B.I1.card : ℝ)⁻¹ +
        cplus * delta ^ (kappa + 1) / (kappa + 1)) := by
  letI : IsProbabilityMeasure P.dataMeasure := hP.probability
  letI : IsProbabilityMeasure (iidProduct P n) := by
    unfold iidProduct
    infer_instance
  let f := fun z : Fin n → ClampObs J =>
    intervalLength (contHoeffdingInterval B z delta alpha)
  let atomTotal := fun z : Fin n → ClampObs J =>
    ∑ x : Fin J, atomEstimate B z x delta
  let t0 := Real.sqrt (Real.log (4 / alpha) / (2 * (B.I0.card : ℝ)))
  let t1 := Real.sqrt (Real.log (4 / alpha) / (2 * (B.I1.card : ℝ)))
  let env := cplus * delta ^ (kappa + 1) / (kappa + 1)
  have hatomMeas : Measurable atomTotal :=
    Finset.measurable_fun_sum _ fun x _ => atomEstimate_measurable B x delta
  have hatomInt : Integrable atomTotal (iidProduct P n) := by
    refine Integrable.of_bound hatomMeas.aestronglyMeasurable J ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact (Finset.sum_le_sum fun x _ => (atomEstimate_mem_Icc B z x delta).2).trans_eq
        (by simp)
    · exact Finset.sum_nonneg fun x _ => (atomEstimate_mem_Icc B z x delta).1
  have hlenMeas : Measurable f := by
    let center := fun z : Fin n → ClampObs J => contFallbackEstimator B z delta
    let radius := fun z : Fin n → ClampObs J =>
      t0 + t1 + atomTotal z / 2
    let lo := fun z => max 0 (center z - radius z)
    let hi := fun z => min 1 (center z + radius z)
    have hc : Measurable center := by
      dsimp [center]
      exact clampUnit_measurable'.comp
        ((retainedEstimate_measurable B delta).add
          (measurable_const.mul hatomMeas))
    have hr : Measurable radius :=
      (measurable_const.add measurable_const).add (hatomMeas.div_const 2)
    have hlo : Measurable lo := measurable_const.max (hc.sub hr)
    have hhi : Measurable hi := measurable_const.min (hc.add hr)
    have hord : ∀ z, lo z ≤ hi z := by
      intro z
      have hrad : 0 ≤ radius z := by
        dsimp [radius, atomTotal]
        have ha : 0 ≤ ∑ x : Fin J, atomEstimate B z x delta :=
          Finset.sum_nonneg fun x _ => (atomEstimate_mem_Icc B z x delta).1
        positivity
      have hcI := clampUnit_mem_Icc
        (retainedEstimate B z delta +
          (1 / 2 : ℝ) * ∑ x : Fin J, atomEstimate B z x delta)
      apply le_min
      · exact max_le (by norm_num) (by
          dsimp [lo, hi, center]
          unfold contFallbackEstimator
          linarith [hcI.2])
      · exact max_le (by
          dsimp [lo, hi, center]
          unfold contFallbackEstimator
          linarith [hcI.1]) (by
          dsimp [lo, hi, center]
          linarith)
    have heq : f = fun z => max 0 (hi z - lo z) := by
      funext z
      dsimp [f, lo, hi, center, radius, t0, t1, atomTotal]
      simp only [contHoeffdingInterval, intervalLength]
      rw [csSup_Icc (hord z), csInf_Icc (hord z)]
    rw [heq]
    exact measurable_const.max (hhi.sub hlo)
  have hlenInt : Integrable f (iidProduct P n) := by
    refine Integrable.of_bound hlenMeas.aestronglyMeasurable 1 ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    let radius := t0 + t1 + atomTotal z / 2
    have hrad : 0 ≤ radius := by
      dsimp [radius, atomTotal, t0, t1]
      have ha : 0 ≤ ∑ x : Fin J, atomEstimate B z x delta :=
        Finset.sum_nonneg fun x _ => (atomEstimate_mem_Icc B z x delta).1
      positivity
    have hcI := clampUnit_mem_Icc
      (retainedEstimate B z delta +
        (1 / 2 : ℝ) * ∑ x : Fin J, atomEstimate B z x delta)
    have hord : max 0 (contFallbackEstimator B z delta - radius) ≤
        min 1 (contFallbackEstimator B z delta + radius) := by
      apply le_min
      · exact max_le (by norm_num) (by
          unfold contFallbackEstimator
          linarith [hcI.2])
      · exact max_le (by
          unfold contFallbackEstimator
          linarith [hcI.1]) (by linarith)
    dsimp [f, radius, t0, t1, atomTotal]
    simp only [contHoeffdingInterval, intervalLength]
    rw [csSup_Icc hord, csInf_Icc hord]
    apply max_le
    · norm_num
    · have hhi' := min_le_left (1 : ℝ)
        (contFallbackEstimator B z delta +
          (Real.sqrt (Real.log (4 / alpha) / (2 * (B.I0.card : ℝ))) +
            Real.sqrt (Real.log (4 / alpha) / (2 * (B.I1.card : ℝ))) +
            (∑ x : Fin J, atomEstimate B z x delta) / 2))
      have hlo' := le_max_left (0 : ℝ)
        (contFallbackEstimator B z delta -
          (Real.sqrt (Real.log (4 / alpha) / (2 * (B.I0.card : ℝ))) +
            Real.sqrt (Real.log (4 / alpha) / (2 * (B.I1.card : ℝ))) +
            (∑ x : Fin J, atomEstimate B z x delta) / 2))
      linarith
  have hatomIntLe : (∫ z, atomTotal z ∂iidProduct P n) ≤
      (J : ℝ) * ((1 / 2 : ℝ) * Real.sqrt (B.I1.card : ℝ)⁻¹ + env) := by
    rw [integral_finsetSum]
    · calc
        (∑ x : Fin J, ∫ z, atomEstimate B z x delta ∂iidProduct P n) ≤
            ∑ _x : Fin J,
              ((1 / 2 : ℝ) * Real.sqrt (B.I1.card : ℝ)⁻¹ + env) := by
          apply Finset.sum_le_sum
          intro x hx
          let coeff := P.px x * atomMass P x delta
          have hax : Integrable (fun z : Fin n → ClampObs J => atomEstimate B z x delta)
              (iidProduct P n) := by
            refine Integrable.of_bound
              (atomEstimate_measurable B x delta).aestronglyMeasurable 1 ?_
            filter_upwards with z
            rw [Real.norm_eq_abs, abs_of_nonneg (atomEstimate_mem_Icc B z x delta).1]
            exact (atomEstimate_mem_Icc B z x delta).2
          have habs : |∫ z, atomEstimate B z x delta - coeff ∂iidProduct P n| ≤
              (1 / 2 : ℝ) * Real.sqrt (B.I1.card : ℝ)⁻¹ := by
            calc
              _ ≤ ∫ z, |atomEstimate B z x delta - coeff| ∂iidProduct P n :=
                abs_integral_le_integral_abs
              _ ≤ _ := cont_atomEstimate_l1_le P hP B hcard1 x hdelta.1
                (hdelta.2.trans hreg.2.2.2.2.2.2.2.2.le)
          have hcoeff :=
            (cont_atomCoefficient_nonneg_le_envelope P hP hreg x hdelta).2
          have hintconst :
              (∫ _z : Fin n → ClampObs J, coeff ∂iidProduct P n) = coeff := by simp
          have hrewrite :
              (∫ z, atomEstimate B z x delta - coeff ∂iidProduct P n) =
                (∫ z, atomEstimate B z x delta ∂iidProduct P n) - coeff := by
            rw [integral_sub hax (integrable_const coeff), hintconst]
          rw [hrewrite] at habs
          dsimp [env, coeff]
          linarith [le_abs_self
            ((∫ z, atomEstimate B z x delta ∂iidProduct P n) - coeff)]
        _ = (J : ℝ) *
            ((1 / 2 : ℝ) * Real.sqrt (B.I1.card : ℝ)⁻¹ + env) := by
          simp
          ring
    · intro x hx
      refine Integrable.of_bound (atomEstimate_measurable B x delta).aestronglyMeasurable 1 ?_
      filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_nonneg (atomEstimate_mem_Icc B z x delta).1]
      exact (atomEstimate_mem_Icc B z x delta).2
  have hpoint : ∀ z, f z ≤ 2 * t0 + 2 * t1 + atomTotal z := by
    intro z
    dsimp [f, t0, t1, atomTotal]
    convert contHoeffdingInterval_length_le_radius B delta alpha z using 1 <;> ring
  have hrhsInt : Integrable (fun z => 2 * t0 + 2 * t1 + atomTotal z)
      (iidProduct P n) := (integrable_const _).add hatomInt
  calc
    (∫ z, f z ∂iidProduct P n) ≤
        ∫ z, (2 * t0 + 2 * t1 + atomTotal z) ∂iidProduct P n :=
      integral_mono_ae hlenInt hrhsInt (ae_of_all _ hpoint)
    _ = 2 * t0 + 2 * t1 + ∫ z, atomTotal z ∂iidProduct P n := by
      rw [integral_add (integrable_const _) hatomInt, integral_const]
      simp
    _ ≤ 2 * t0 + 2 * t1 +
        (J : ℝ) * ((1 / 2 : ℝ) * Real.sqrt (B.I1.card : ℝ)⁻¹ + env) :=
      by linarith [hatomIntLe]
    _ = _ := rfl

/-- The real expected-length bound upgrades to the extended-real convention
used by the continuity-only minimax criterion. The result uses [the `hP` condition](hyp:hP), [the `hreg` condition](hyp:hreg), [the `hdelta` condition](hyp:hdelta), [the `hcard1` condition](hyp:hcard1). [This is the stated conclusion](goal).
-/
lemma contHoeffdingInterval_lintegral_length_le
    {J n : ℕ} (P : ClampLaw J) (B : SplitBlocks n)
    (kappa cminus cplus pmin deltaBar delta alpha : ℝ)
    (hP : ContClampModel P kappa cminus cplus pmin deltaBar)
    (hreg : ContDesignConstants J kappa cminus cplus pmin deltaBar)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar)
    (hcard1 : 0 < B.I1.card) :
    (∫⁻ z, intervalLengthENNReal (contHoeffdingInterval B z delta alpha)
        ∂iidProduct P n) ≤
      ENNReal.ofReal
        (2 * Real.sqrt (Real.log (4 / alpha) / (2 * (B.I0.card : ℝ))) +
        2 * Real.sqrt (Real.log (4 / alpha) / (2 * (B.I1.card : ℝ))) +
        (J : ℝ) * ((1 / 2 : ℝ) * Real.sqrt (B.I1.card : ℝ)⁻¹ +
          cplus * delta ^ (kappa + 1) / (kappa + 1))) := by
  letI : IsProbabilityMeasure P.dataMeasure := hP.probability
  letI : IsProbabilityMeasure (iidProduct P n) := by
    unfold iidProduct
    infer_instance
  let f := fun z : Fin n → ClampObs J =>
    intervalLength (contHoeffdingInterval B z delta alpha)
  have hfmeas : Measurable f := by
    let center := fun z : Fin n → ClampObs J => contFallbackEstimator B z delta
    let radius := fun z : Fin n → ClampObs J =>
      Real.sqrt (Real.log (4 / alpha) / (2 * (B.I0.card : ℝ))) +
      Real.sqrt (Real.log (4 / alpha) / (2 * (B.I1.card : ℝ))) +
      (∑ x : Fin J, atomEstimate B z x delta) / 2
    let lo := fun z => max 0 (center z - radius z)
    let hi := fun z => min 1 (center z + radius z)
    have hc : Measurable center := by
      dsimp [center]
      exact clampUnit_measurable'.comp
        ((retainedEstimate_measurable B delta).add
          (measurable_const.mul
            (Finset.measurable_fun_sum _ fun x _ => atomEstimate_measurable B x delta)))
    have hr : Measurable radius :=
      (measurable_const.add measurable_const).add
        ((Finset.measurable_fun_sum _ fun x _ =>
          atomEstimate_measurable B x delta).div_const 2)
    have hlo : Measurable lo := measurable_const.max (hc.sub hr)
    have hhi : Measurable hi := measurable_const.min (hc.add hr)
    have hord : ∀ z, lo z ≤ hi z := by
      intro z
      have hrad : 0 ≤ radius z := by
        dsimp [radius]
        have ha : 0 ≤ ∑ x : Fin J, atomEstimate B z x delta :=
          Finset.sum_nonneg fun x _ => (atomEstimate_mem_Icc B z x delta).1
        positivity
      have hcI := clampUnit_mem_Icc
        (retainedEstimate B z delta +
          (1 / 2 : ℝ) * ∑ x : Fin J, atomEstimate B z x delta)
      apply le_min
      · exact max_le (by norm_num) (by
          dsimp [lo, hi, center]
          unfold contFallbackEstimator
          linarith [hcI.2])
      · exact max_le (by
          dsimp [lo, hi, center]
          unfold contFallbackEstimator
          linarith [hcI.1]) (by
          dsimp [lo, hi, center]
          linarith)
    have heq : f = fun z => max 0 (hi z - lo z) := by
      funext z
      dsimp [f, lo, hi, center, radius]
      simp only [contHoeffdingInterval, intervalLength]
      rw [csSup_Icc (hord z), csInf_Icc (hord z)]
    rw [heq]
    exact measurable_const.max (hhi.sub hlo)
  have hfint : Integrable f (iidProduct P n) := by
    refine Integrable.of_bound hfmeas.aestronglyMeasurable 1 ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    let radius :=
      Real.sqrt (Real.log (4 / alpha) / (2 * (B.I0.card : ℝ))) +
      Real.sqrt (Real.log (4 / alpha) / (2 * (B.I1.card : ℝ))) +
      (∑ x : Fin J, atomEstimate B z x delta) / 2
    have hrad : 0 ≤ radius := by
      dsimp [radius]
      have ha : 0 ≤ ∑ x : Fin J, atomEstimate B z x delta :=
        Finset.sum_nonneg fun x _ => (atomEstimate_mem_Icc B z x delta).1
      positivity
    have hcI := clampUnit_mem_Icc
      (retainedEstimate B z delta +
        (1 / 2 : ℝ) * ∑ x : Fin J, atomEstimate B z x delta)
    have hord : max 0 (contFallbackEstimator B z delta - radius) ≤
        min 1 (contFallbackEstimator B z delta + radius) := by
      apply le_min
      · exact max_le (by norm_num) (by
          unfold contFallbackEstimator
          linarith [hcI.2])
      · exact max_le (by
          unfold contFallbackEstimator
          linarith [hcI.1]) (by linarith)
    dsimp [f, radius]
    simp only [contHoeffdingInterval, intervalLength]
    rw [csSup_Icc hord, csInf_Icc hord]
    apply max_le
    · norm_num
    · have hhi := min_le_left (1 : ℝ)
        (contFallbackEstimator B z delta +
          (Real.sqrt (Real.log (4 / alpha) / (2 * (B.I0.card : ℝ))) +
            Real.sqrt (Real.log (4 / alpha) / (2 * (B.I1.card : ℝ))) +
            (∑ x : Fin J, atomEstimate B z x delta) / 2))
      have hlo := le_max_left (0 : ℝ)
        (contFallbackEstimator B z delta -
          (Real.sqrt (Real.log (4 / alpha) / (2 * (B.I0.card : ℝ))) +
            Real.sqrt (Real.log (4 / alpha) / (2 * (B.I1.card : ℝ))) +
            (∑ x : Fin J, atomEstimate B z x delta) / 2))
      linarith
  have hfnn : 0 ≤ᵐ[iidProduct P n] f :=
    ae_of_all _ fun z => le_max_left (0 : ℝ)
      (sSup (contHoeffdingInterval B z delta alpha) -
        sInf (contHoeffdingInterval B z delta alpha))
  simp_rw [intervalLengthENNReal]
  rw [← ofReal_integral_eq_lintegral_ofReal hfint hfnn]
  exact ENNReal.ofReal_le_ofReal
    (contHoeffdingInterval_integral_length_le P B kappa cminus cplus pmin
      deltaBar delta alpha hP hreg hdelta hcard1)

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier

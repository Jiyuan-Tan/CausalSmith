/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.ContinuityWitness
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.ContinuityUpper
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.TMinimaxRisk

/-! # Functionals of the canonical continuity witnesses -/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory ProbabilityTheory Set

noncomputable section

private lemma measurable_minimax_design {J : ℕ} :
    Measurable (fun o : ClampObs J => (o.X, o.A)) := by
  let h : Measurable (fun o : ClampObs J => (o.X, o.A, o.Y)) :=
    Measurable.of_comap_le le_rfl
  exact (measurable_fst.comp h).prodMk
    (measurable_fst.comp (measurable_snd.comp h))

/-- The selected continuous regression of a canonical Bernoulli witness is
the displayed Bernoulli mean throughout the threshold range. The result uses [the `hreg` condition](hyp:hreg), [the `hqmeas` condition](hyp:hqmeas), [the `hqbound` condition](hyp:hqbound), [the `hcont` condition](hyp:hcont), [the `ha` condition](hyp:ha). [This is the stated conclusion](goal).
-/
lemma contRegression_minimaxClampLaw_eq
    (J : ℕ) (kappa cminus cplus pmin deltaBar : ℝ)
    (hreg : ContDesignConstants J kappa cminus cplus pmin deltaBar)
    (q : ℝ → ℝ) (hqmeas : Measurable q)
    (hqbound : ∀ a, |q a| ≤ 1 / 2)
    (hcont : ContinuousOn (fun a => 1 / 2 + q a) (Set.Icc (0 : ℝ) deltaBar))
    (x : Fin J) (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) deltaBar) :
    let P := minimaxClampLaw J kappa (fun p => q p.2)
    let hP := minimaxClampModel_continuous J kappa cminus cplus pmin deltaBar
      hreg.1 hreg.2.1 hreg.2.2.2.1 hreg.2.2.2.2.1 hreg.2.2.2.2.2.2.1
      q hqmeas hqbound hcont
    contRegression P kappa cminus cplus pmin deltaBar hP x a = 1 / 2 + q a := by
  dsimp only
  let g : Fin J × ℝ → ℝ := fun p => q p.2
  let P := minimaxClampLaw J kappa g
  have hP := minimaxClampModel_continuous J kappa cminus cplus pmin deltaBar
    hreg.1 hreg.2.1 hreg.2.2.2.1 hreg.2.2.2.2.1 hreg.2.2.2.2.2.2.1
    q hqmeas hqbound hcont
  have hchosen := Classical.choose_spec hP.continuousVersion
  let μ := minimaxDataMeasure J kappa g
  let design : ClampObs J → Fin J × ℝ := fun o => (o.X, o.A)
  let m : ClampObs J → ℝ := fun o => 1 / 2 + q o.A
  have hgmeas : Measurable g := hqmeas.comp measurable_snd
  have hgbound : ∀ p, |g p| ≤ 1 / 2 := fun p => hqbound p.2
  letI : IsProbabilityMeasure μ :=
    minimaxDataMeasure_isProbabilityMeasure J kappa hreg.1 hreg.2.1
      g hgmeas hgbound
  have hdesign : Measurable design := measurable_minimax_design
  have hY : Integrable (fun o : ClampObs J => o.Y) μ := by
    refine Integrable.of_bound clampOutcome_measurable.aestronglyMeasurable 1 ?_
    filter_upwards [minimaxDataMeasure_ae_bernoulli J kappa g hgmeas] with o ho
    rcases ho with ho | ho <;> rw [ho] <;> norm_num
  have hm_meas : Measurable m := by
    exact measurable_const.add (hqmeas.comp
      (measurable_fst.comp (measurable_snd.comp
        (Measurable.of_comap_le le_rfl))))
  have hm : Integrable m μ := by
    refine Integrable.of_bound hm_meas.aestronglyMeasurable 1 ?_
    filter_upwards with o
    rw [Real.norm_eq_abs]
    change |1 / 2 + q o.A| ≤ 1
    have hb := hqbound o.A
    rw [abs_le] at hb
    exact abs_le.2 ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have hm_design :
      AEStronglyMeasurable[MeasurableSpace.comap design inferInstance] m μ := by
    have heq : m = (fun p : Fin J × ℝ => 1 / 2 + q p.2) ∘ design := rfl
    rw [heq]
    exact ((measurable_const.add (hqmeas.comp measurable_snd)).comp
      (Measurable.of_comap_le le_rfl)).aestronglyMeasurable
  have hint : ∀ T : Set (Fin J × ℝ), MeasurableSet T →
      (∫ o in design ⁻¹' T, o.Y ∂μ) = ∫ o in design ⁻¹' T, m o ∂μ := by
    intro T hT
    rw [minimaxDataMeasure_integral_Y_design J kappa hreg.1 hreg.2.1
      g hgmeas hgbound T hT]
    rw [← integral_indicator (hT.preimage hdesign), ← integral_indicator hT]
    rw [← minimaxDataMeasure_map_design J kappa g hgmeas hgbound,
      integral_map hdesign.aemeasurable]
    · rfl
    · exact ((measurable_const.add hgmeas).indicator hT).aestronglyMeasurable
  have hver :
      P.dataMeasure[(fun o : ClampObs J => o.Y) |
        MeasurableSpace.comap (fun o : ClampObs J => (o.X, o.A)) inferInstance]
        =ᵐ[P.dataMeasure] fun o => 1 / 2 + q o.A := by
    exact Causalean.Mathlib.MeasureTheory.condExp_eq_of_integral_preimage_eq
      μ design hdesign (fun o => o.Y) m hY hm hm_design hint
  exact (cont_regression_extension_unique P kappa cminus cplus pmin deltaBar
    hP hreg _ (fun _ => 1 / 2 + q) hchosen.1 (fun _ => hcont)
    hchosen.2 hver x) ha

/-- The continuity functional of a canonical witness agrees with its explicit
clamp functional on the threshold range. The result uses [the `hreg` condition](hyp:hreg), [the `hdelta` condition](hyp:hdelta), [the `hqmeas` condition](hyp:hqmeas), [the `hqbound` condition](hyp:hqbound), [the `hcont` condition](hyp:hcont). [This is the stated conclusion](goal).
-/
lemma contClampFunctional_minimaxClampLaw_eq
    (J : ℕ) (kappa cminus cplus pmin deltaBar delta : ℝ)
    (hreg : ContDesignConstants J kappa cminus cplus pmin deltaBar)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar)
    (q : ℝ → ℝ) (hqmeas : Measurable q)
    (hqbound : ∀ a, |q a| ≤ 1 / 2)
    (hcont : ContinuousOn (fun a => 1 / 2 + q a) (Set.Icc (0 : ℝ) deltaBar)) :
    let P := minimaxClampLaw J kappa (fun p => q p.2)
    let hP := minimaxClampModel_continuous J kappa cminus cplus pmin deltaBar
      hreg.1 hreg.2.1 hreg.2.2.2.1 hreg.2.2.2.2.1 hreg.2.2.2.2.2.2.1
      q hqmeas hqbound hcont
    contClampFunctional P kappa cminus cplus pmin deltaBar hP delta =
      clampFunctional P delta := by
  dsimp only
  unfold contClampFunctional clampFunctional
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [contRegression_minimaxClampLaw_eq J kappa cminus cplus pmin deltaBar
    hreg q hqmeas hqbound hcont x delta hdelta]
  rfl

/-- A fixed-height continuity bump changes the threshold functional by at
least its atom contribution. The result uses [the `hJ` condition](hyp:hJ), [the `hkappa` condition](hyp:hkappa), [the `hdelta` condition](hyp:hdelta), [the `hh` condition](hyp:hh), [the `hamp` condition](hyp:hamp), [the `hamp_le` condition](hyp:hamp_le). [This is the stated conclusion](goal).
-/
lemma minimaxContinuityBumpSeparation
    (J : ℕ) (kappa delta h amplitude : ℝ)
    (hJ : 0 < J) (hkappa : 0 ≤ kappa)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) 1) (hh : 0 < h)
    (hamp : 0 ≤ amplitude) (hamp_le : amplitude ≤ 1 / 4) :
    let q := fun a : ℝ => amplitude *
      CausalSmith.Stat.DoseResponseMinimax.doseBump ((a - delta) / h)
    amplitude * delta ^ (kappa + 1) ≤
      clampFunctional (minimaxClampLaw J kappa (fun p => q p.2)) delta -
        clampFunctional (minimaxClampLaw J kappa (fun _ => 0)) delta := by
  dsimp only
  let q := fun a : ℝ => amplitude *
    CausalSmith.Stat.DoseResponseMinimax.doseBump ((a - delta) / h)
  have hqmeas : Measurable q := by dsimp [q]; fun_prop
  have hq0 (a : ℝ) : 0 ≤ q a := by
    exact mul_nonneg hamp
      (CausalSmith.Stat.DoseResponseMinimax.doseBump_nonneg _)
  have hqbound (a : ℝ) : |q a| ≤ 1 / 2 := by
    rw [abs_of_nonneg (hq0 a)]
    have hb := CausalSmith.Stat.DoseResponseMinimax.doseBump_le_one
      ((a - delta) / h)
    dsimp [q]
    nlinarith
  rw [minimaxClampFunctional J kappa delta hJ hkappa hdelta.1 q hqmeas hqbound,
    minimaxClampFunctional J kappa delta hJ hkappa hdelta.1
      (fun _ => 0) measurable_const (fun _ => by norm_num)]
  haveI : IsProbabilityMeasure (minimaxTreatmentMeasure kappa) :=
    minimaxTreatmentMeasure_isProbabilityMeasure kappa hkappa
  have hqint : Integrable q (minimaxTreatmentMeasure kappa) := by
    refine Integrable.of_bound hqmeas.aestronglyMeasurable (1 / 2) ?_
    filter_upwards with a
    simpa [Real.norm_eq_abs] using hqbound a
  have honeint : Integrable (fun _ : ℝ => (1 / 2 : ℝ))
      (minimaxTreatmentMeasure kappa) := integrable_const _
  rw [show (∫ a in Set.Ioi delta, (1 / 2 + q a) ∂minimaxTreatmentMeasure kappa) =
      (∫ a in Set.Ioi delta, (1 / 2 : ℝ) ∂minimaxTreatmentMeasure kappa) +
        ∫ a in Set.Ioi delta, q a ∂minimaxTreatmentMeasure kappa by
        rw [integral_add honeint.integrableOn hqint.integrableOn],
    show (∫ a in Set.Ioi delta, (1 / 2 + 0) ∂minimaxTreatmentMeasure kappa) =
      ∫ a in Set.Ioi delta, (1 / 2 : ℝ) ∂minimaxTreatmentMeasure kappa by simp]
  have hqdelta : q delta = amplitude := by
    simp [q, hh.ne', CausalSmith.Stat.DoseResponseMinimax.doseBump_zero]
  rw [hqdelta]
  have hnonneg : 0 ≤ ∫ a in Set.Ioi delta, q a ∂minimaxTreatmentMeasure kappa :=
    integral_nonneg_of_ae (ae_of_all _ hq0)
  nlinarith

/-- The canonical center and a fixed-height narrow bump form an admissible
continuity-only two-point experiment with an explicit product chi-square
budget and atom-scale functional separation. The result uses [the `hreg` condition](hyp:hreg), [the `hdelta` condition](hyp:hdelta), [the `hh` condition](hyp:hh), [the `hamp` condition](hyp:hamp), [the `hamp_le` condition](hyp:hamp_le). [This is the stated conclusion](goal).
-/
lemma continuityBump_twoPoint
    (J n : ℕ) (kappa cminus cplus pmin deltaBar delta h amplitude : ℝ)
    (hreg : ContDesignConstants J kappa cminus cplus pmin deltaBar)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar)
    (hh : 0 < h) (hamp : 0 ≤ amplitude) (hamp_le : amplitude ≤ 1 / 4) :
    let q := fun a : ℝ => amplitude *
      CausalSmith.Stat.DoseResponseMinimax.doseBump ((a - delta) / h)
    let Q0 := minimaxClampLaw J kappa (fun _ : Fin J × ℝ => 0)
    let Q1 := minimaxClampLaw J kappa (fun p => q p.2)
    ∃ (hQ0 : ContClampModel Q0 kappa cminus cplus pmin deltaBar)
      (hQ1 : ContClampModel Q1 kappa cminus cplus pmin deltaBar),
      amplitude * delta ^ (kappa + 1) ≤
        |contClampFunctional Q1 kappa cminus cplus pmin deltaBar hQ1 delta -
          contClampFunctional Q0 kappa cminus cplus pmin deltaBar hQ0 delta| ∧
      1 + productChiSq Q1 Q0 n ≤
        Real.exp ((n : ℝ) * (8 * (kappa + 1) * amplitude ^ 2 * h *
          (delta + h) ^ kappa)) := by
  dsimp only
  let q := fun a : ℝ => amplitude *
    CausalSmith.Stat.DoseResponseMinimax.doseBump ((a - delta) / h)
  let Q0 := minimaxClampLaw J kappa (fun _ : Fin J × ℝ => 0)
  let Q1 := minimaxClampLaw J kappa (fun p => q p.2)
  have hcont0 : ContinuousOn (fun _ : ℝ => (1 / 2 : ℝ) + 0)
      (Set.Icc (0 : ℝ) deltaBar) := by fun_prop
  have hqmeas : Measurable q := by dsimp [q]; fun_prop
  have hq0 (a : ℝ) : 0 ≤ q a := mul_nonneg hamp
    (CausalSmith.Stat.DoseResponseMinimax.doseBump_nonneg _)
  have hqbound (a : ℝ) : |q a| ≤ 1 / 2 := by
    rw [abs_of_nonneg (hq0 a)]
    have hb := CausalSmith.Stat.DoseResponseMinimax.doseBump_le_one
      ((a - delta) / h)
    dsimp [q]
    nlinarith
  have hqstrict (p : Fin J × ℝ) : |q p.2| < 1 / 2 := by
    rw [abs_of_nonneg (hq0 p.2)]
    have hb := CausalSmith.Stat.DoseResponseMinimax.doseBump_le_one
      ((p.2 - delta) / h)
    dsimp [q]
    nlinarith
  have hcont1 : ContinuousOn (fun a => 1 / 2 + q a)
      (Set.Icc (0 : ℝ) deltaBar) := by
    apply Continuous.continuousOn
    dsimp [q]
    have hb : Continuous CausalSmith.Stat.DoseResponseMinimax.doseBump := by
      unfold CausalSmith.Stat.DoseResponseMinimax.doseBump
      exact (CausalSmith.Stat.DoseResponseMinimax.doseContDiffBump.contDiff
        (n := ⊤)).continuous
    exact continuous_const.add (continuous_const.mul
      (hb.comp ((continuous_id.sub continuous_const).div_const h)))
  let hQ0 := minimaxConstant_mem_cont_model J kappa cminus cplus pmin deltaBar 0
    hreg (by norm_num)
  let hQ1 := minimaxDoseBump_mem_cont_model J kappa cminus cplus pmin deltaBar
    delta h amplitude hreg hh hamp hamp_le
  refine ⟨hQ0, hQ1, ?_, ?_⟩
  · rw [contClampFunctional_minimaxClampLaw_eq J kappa cminus cplus pmin
      deltaBar delta hreg hdelta q hqmeas hqbound hcont1,
      contClampFunctional_minimaxClampLaw_eq J kappa cminus cplus pmin
        deltaBar delta hreg hdelta (fun _ => 0) measurable_const
        (fun _ => by norm_num) hcont0]
    have hsep := minimaxContinuityBumpSeparation J kappa delta h amplitude
      hreg.1 hreg.2.1 ⟨hdelta.1, hdelta.2.trans hreg.2.2.2.2.2.2.2.2.le⟩
      hh hamp hamp_le
    rw [abs_of_nonneg (hsep.trans' (mul_nonneg hamp
      (Real.rpow_nonneg hdelta.1 _)))]
    exact hsep
  · let I := ∫ p, 4 * ((fun p : Fin J × ℝ => q p.2) p) ^ 2
        ∂minimaxDesignMeasure J kappa
    have hI : I ≤ 8 * (kappa + 1) * amplitude ^ 2 * h *
        (delta + h) ^ kappa := by
      have hi := minimaxLocal_designIntegral_le J 0 kappa delta h amplitude
        hreg.1 hreg.2.1 hdelta.1 hh hamp
      simpa [I, q] using hi
    have hI0 : 0 ≤ I := integral_nonneg_of_ae (ae_of_all _ fun _ => by positivity)
    have heq := minimaxProduct_chiSqDiv_center J n kappa hreg.1 hreg.2.1
      (fun p : Fin J × ℝ => q p.2) (hqmeas.comp measurable_snd) hqstrict
    change 1 + productChiSq Q1 Q0 n = (1 + I) ^ n at heq
    rw [heq]
    calc
      (1 + I) ^ n ≤ (Real.exp I) ^ n := pow_le_pow_left₀ (by linarith)
        (by simpa [add_comm] using Real.add_one_le_exp I) n
      _ = Real.exp ((n : ℝ) * I) := by rw [Real.exp_nat_mul]
      _ ≤ Real.exp ((n : ℝ) * (8 * (kappa + 1) * amplitude ^ 2 * h *
          (delta + h) ^ kappa)) := Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left hI (Nat.cast_nonneg n))

/-- Two constant Bernoulli regressions give the regular root-sample-size
two-point experiment inside the continuity-only model. The result uses [the `hreg` condition](hyp:hreg), [the `hdelta` condition](hyp:hdelta), [the `heps` condition](hyp:heps), [the `heps_le` condition](hyp:heps_le). [This is the stated conclusion](goal).
-/
lemma continuityConstant_twoPoint
    (J n : ℕ) (kappa cminus cplus pmin deltaBar delta eps : ℝ)
    (hreg : ContDesignConstants J kappa cminus cplus pmin deltaBar)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar)
    (heps : 0 ≤ eps) (heps_le : eps ≤ 1 / 4) :
    let Q0 := minimaxClampLaw J kappa (fun _ : Fin J × ℝ => 0)
    let Q1 := minimaxClampLaw J kappa (fun _ : Fin J × ℝ => eps)
    ∃ (hQ0 : ContClampModel Q0 kappa cminus cplus pmin deltaBar)
      (hQ1 : ContClampModel Q1 kappa cminus cplus pmin deltaBar),
      eps = |contClampFunctional Q1 kappa cminus cplus pmin deltaBar hQ1 delta -
        contClampFunctional Q0 kappa cminus cplus pmin deltaBar hQ0 delta| ∧
      1 + productChiSq Q1 Q0 n ≤ Real.exp ((n : ℝ) * (4 * eps ^ 2)) := by
  dsimp only
  let Q0 := minimaxClampLaw J kappa (fun _ : Fin J × ℝ => 0)
  let Q1 := minimaxClampLaw J kappa (fun _ : Fin J × ℝ => eps)
  have hepsBound : |eps| ≤ 1 / 2 := by rw [abs_of_nonneg heps]; linarith
  have hepsStrict : |eps| < 1 / 2 := by
    rw [abs_of_nonneg heps]
    linarith
  have hcont0 : ContinuousOn (fun _ : ℝ => (1 / 2 : ℝ) + 0)
      (Set.Icc (0 : ℝ) deltaBar) := by fun_prop
  have hcont1 : ContinuousOn (fun _ : ℝ => (1 / 2 : ℝ) + eps)
      (Set.Icc (0 : ℝ) deltaBar) := by fun_prop
  let hQ0 := minimaxConstant_mem_cont_model J kappa cminus cplus pmin deltaBar 0
    hreg (by norm_num)
  let hQ1 := minimaxConstant_mem_cont_model J kappa cminus cplus pmin deltaBar eps
    hreg hepsBound
  refine ⟨hQ0, hQ1, ?_, ?_⟩
  · rw [contClampFunctional_minimaxClampLaw_eq J kappa cminus cplus pmin
      deltaBar delta hreg hdelta (fun _ => eps) measurable_const
      (fun _ => hepsBound) hcont1,
      contClampFunctional_minimaxClampLaw_eq J kappa cminus cplus pmin
        deltaBar delta hreg hdelta (fun _ => 0) measurable_const
        (fun _ => by norm_num) hcont0,
      minimaxGlobalSeparation J kappa delta eps hreg.1 hreg.2.1
        ⟨hdelta.1, hdelta.2.trans hreg.2.2.2.2.2.2.2.2.le⟩ hepsBound,
      abs_of_nonneg heps]
  · have heq := minimaxProduct_chiSqDiv_center J n kappa hreg.1 hreg.2.1
      (fun _ : Fin J × ℝ => eps) measurable_const (fun _ => hepsStrict)
    have hI : (∫ _p, 4 * eps ^ 2 ∂minimaxDesignMeasure J kappa) = 4 * eps ^ 2 := by
      letI : IsProbabilityMeasure (minimaxDesignMeasure J kappa) :=
        minimaxDesignMeasure_isProbabilityMeasure J kappa hreg.1 hreg.2.1
      simp
    change 1 + productChiSq Q1 Q0 n =
      (1 + ∫ _p, 4 * eps ^ 2 ∂minimaxDesignMeasure J kappa) ^ n at heq
    rw [hI] at heq
    rw [heq]
    calc
      (1 + 4 * eps ^ 2) ^ n ≤ (Real.exp (4 * eps ^ 2)) ^ n :=
        pow_le_pow_left₀ (by positivity)
          (by simpa [add_comm] using Real.add_one_le_exp (4 * eps ^ 2)) n
      _ = Real.exp ((n : ℝ) * (4 * eps ^ 2)) := by rw [Real.exp_nat_mul]

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier

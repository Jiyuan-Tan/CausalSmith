/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.TMinimaxRisk
import Causalean.Stat.Minimax.HonestConfidenceSet

/-! # Two-point lower bounds for honest confidence length

This file isolates the low-level expected-length converse for the fixed-Hölder
clamp model.  It deliberately defines the worst length of one procedure here,
so that the headline module can reuse the results without an import cycle.
-/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open Filter MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Worst expected extended interval length of one procedure over the
fixed-Hölder clamp model. -/
def clampProcedureWorstLength (J n : ℕ)
    (beta kappa L cminus cplus pmin : ℝ) (C : ConfidenceProcedure n J) : ℝ≥0∞ :=
  sSup {v : ℝ≥0∞ | ∃ P : ClampLaw J,
    ClampModel P beta kappa L cminus cplus pmin ∧
    v = ∫⁻ z, intervalLengthENNReal (C z) ∂iidProduct P n}

/-- A close pair in the fixed-Hölder model lower-bounds the worst expected
length of every interval procedure that is honest over that model. The result uses [the `hC` condition](hyp:hC), [the `hP0` condition](hyp:hP0), [the `hP1` condition](hyp:hP1), [the `hgap` condition](hyp:hgap), [the `hsep` condition](hyp:hsep), [the `hac` condition](hyp:hac), [the `hint` condition](hyp:hint). [This is the stated conclusion](goal).
-/
lemma procedureWorstLength_lower_of_two_point
    (P0 P1 : ClampLaw J) (n : ℕ)
    (beta kappa L cminus cplus pmin delta alpha gap : ℝ)
    (C : ConfidenceProcedure n J)
    (hC : UniformCoverage J n beta kappa L cminus cplus pmin delta alpha C)
    (hP0 : ClampModel P0 beta kappa L cminus cplus pmin)
    (hP1 : ClampModel P1 beta kappa L cminus cplus pmin)
    (hgap : 0 ≤ gap)
    (hsep : gap ≤ |clampFunctional P1 delta - clampFunctional P0 delta|)
    (hac : iidProduct P1 n ≪ iidProduct P0 n)
    (hint : Integrable (fun z => (((iidProduct P1 n).rnDeriv
      (iidProduct P0 n) z).toReal - 1) ^ 2) (iidProduct P0 n)) :
    ENNReal.ofReal ((1 - 2 * alpha -
        (1 / 2) * Real.sqrt (productChiSq P1 P0 n)) * gap) ≤
      clampProcedureWorstLength J n beta kappa L cminus cplus pmin C := by
  rcases hC with ⟨⟨lo, hi, hlo, hhi, hord, hCeq⟩, hcover⟩
  let theta0 := clampFunctional P0 delta
  let theta1 := clampFunctional P1 delta
  let A : Set (Fin n → ClampObs J) := {z | theta0 ∈ C z}
  let B : Set (Fin n → ClampObs J) := {z | theta1 ∈ C z}
  have hA : MeasurableSet A := by
    simp only [A, hCeq, mem_Icc]
    exact (measurableSet_le hlo measurable_const).inter
      (measurableSet_le measurable_const hhi)
  have hB : MeasurableSet B := by
    simp only [B, hCeq, mem_Icc]
    exact (measurableSet_le hlo measurable_const).inter
      (measurableSet_le measurable_const hhi)
  letI : IsProbabilityMeasure P0.dataMeasure := hP0.probability
  letI : IsProbabilityMeasure P1.dataMeasure := hP1.probability
  letI : IsProbabilityMeasure (iidProduct P0 n) := by unfold iidProduct; infer_instance
  letI : IsProbabilityMeasure (iidProduct P1 n) := by unfold iidProduct; infer_instance
  have hcov0 : 1 - alpha ≤ (iidProduct P0 n).real A := by
    simpa [A, theta0] using hcover P0 hP0
  have hcov1 : 1 - alpha ≤ (iidProduct P1 n).real B := by
    simpa [B, theta1] using hcover P1 hP1
  have htv : Causalean.Stat.tvDist (iidProduct P1 n) (iidProduct P0 n) ≤
      (1 / 2) * Real.sqrt (productChiSq P1 P0 n) := by
    simpa [productChiSq] using
      Causalean.Stat.tvDist_le_half_sqrt_chiSqDiv
        (iidProduct P1 n) (iidProduct P0 n) hac hint
  have hcov1_at0 : 1 - alpha -
      (1 / 2) * Real.sqrt (productChiSq P1 P0 n) ≤
      (iidProduct P0 n).real B := by
    have hmove := Causalean.Stat.measureReal_sub_le_tvDist
      (μ := iidProduct P0 n) (ν := iidProduct P1 n) hB
    rw [Causalean.Stat.tvDist_symm] at hmove
    linarith
  have hinter : 1 - 2 * alpha -
      (1 / 2) * Real.sqrt (productChiSq P1 P0 n) ≤
      (iidProduct P0 n).real (A ∩ B) := by
    have hunion := measureReal_union_add_inter (μ := iidProduct P0 n)
      (s := A) (t := B) hB (measure_ne_top _ _) (measure_ne_top _ _)
    have hunionle : (iidProduct P0 n).real (A ∪ B) ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
    linarith
  have hpoint (z : Fin n → ClampObs J) :
      (A ∩ B).indicator (fun _ => ENNReal.ofReal gap) z ≤
        intervalLengthENNReal (C z) := by
    by_cases hz : z ∈ A ∩ B
    · rw [Set.indicator_of_mem hz]
      apply ENNReal.ofReal_le_ofReal
      rw [hCeq z]
      simp only [intervalLength, csSup_Icc (hord z), csInf_Icc (hord z)]
      rcases hz with ⟨hz0, hz1⟩
      have hz0' : lo z ≤ theta0 ∧ theta0 ≤ hi z := by
        simpa [A, theta0, hCeq z] using hz0
      have hz1' : lo z ≤ theta1 ∧ theta1 ≤ hi z := by
        simpa [B, theta1, hCeq z] using hz1
      have habs : |clampFunctional P1 delta - clampFunctional P0 delta| ≤
          hi z - lo z := by
        rw [abs_le]
        constructor <;> linarith [hz0'.1, hz0'.2, hz1'.1, hz1'.2]
      exact (hsep.trans habs).trans (le_max_right _ _)
    · simp [hz, intervalLengthENNReal]
  have hlen : ENNReal.ofReal gap * (iidProduct P0 n) (A ∩ B) ≤
      ∫⁻ z, intervalLengthENNReal (C z) ∂iidProduct P0 n := by
    calc
      _ = ∫⁻ z, (A ∩ B).indicator (fun _ => ENNReal.ofReal gap) z
          ∂iidProduct P0 n := by
            rw [lintegral_indicator (hA.inter hB), lintegral_const]
            simp
      _ ≤ _ := lintegral_mono hpoint
  have hreal : ENNReal.ofReal (1 - 2 * alpha -
      (1 / 2) * Real.sqrt (productChiSq P1 P0 n)) ≤
      (iidProduct P0 n) (A ∩ B) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal hinter
  have htarget : ENNReal.ofReal ((1 - 2 * alpha -
      (1 / 2) * Real.sqrt (productChiSq P1 P0 n)) * gap) ≤
      ∫⁻ z, intervalLengthENNReal (C z) ∂iidProduct P0 n := by
    rw [mul_comm, ENNReal.ofReal_mul hgap]
    exact (mul_le_mul le_rfl hreal bot_le bot_le).trans hlen
  exact htarget.trans (le_sSup ⟨P0, hP0, rfl⟩)

/-- The same two-point experiment lower-bounds the minimax honest expected
length. The result uses [the `hP0` condition](hyp:hP0), [the `hP1` condition](hyp:hP1), [the `hgap` condition](hyp:hgap), [the `hsep` condition](hyp:hsep), [the `hac` condition](hyp:hac), [the `hint` condition](hyp:hint). [This is the stated conclusion](goal).
-/
lemma observedMinimaxLength_lower_of_two_point
    (P0 P1 : ClampLaw J) (n : ℕ)
    (beta kappa L cminus cplus pmin delta alpha gap : ℝ)
    (hP0 : ClampModel P0 beta kappa L cminus cplus pmin)
    (hP1 : ClampModel P1 beta kappa L cminus cplus pmin)
    (hgap : 0 ≤ gap)
    (hsep : gap ≤ |clampFunctional P1 delta - clampFunctional P0 delta|)
    (hac : iidProduct P1 n ≪ iidProduct P0 n)
    (hint : Integrable (fun z => (((iidProduct P1 n).rnDeriv
      (iidProduct P0 n) z).toReal - 1) ^ 2) (iidProduct P0 n)) :
    ENNReal.ofReal ((1 - 2 * alpha -
        (1 / 2) * Real.sqrt (productChiSq P1 P0 n)) * gap) ≤
      observedMinimaxLength J n beta kappa L cminus cplus pmin delta alpha := by
  unfold observedMinimaxLength
  apply le_sInf
  intro r hr
  rcases hr with ⟨C, hC, rfl⟩
  exact procedureWorstLength_lower_of_two_point P0 P1 n beta kappa L cminus
    cplus pmin delta alpha gap C hC hP0 hP1 hgap hsep hac hint

/-- A numerical product chi-square budget can replace the exact divergence in
the two-point expected-length bound. The result uses [the `hP0` condition](hyp:hP0), [the `hP1` condition](hyp:hP1), [the `hgap` condition](hyp:hgap), [the `hsep` condition](hyp:hsep), [the `hac` condition](hyp:hac), [the `hint` condition](hyp:hint), [the `hchi0` condition](hyp:hchi0), [the `hchi` condition](hyp:hchi). [This is the stated conclusion](goal).
-/
lemma observedMinimaxLength_lower_of_two_point_chi
    (P0 P1 : ClampLaw J) (n : ℕ)
    (beta kappa L cminus cplus pmin delta alpha gap chi : ℝ)
    (hP0 : ClampModel P0 beta kappa L cminus cplus pmin)
    (hP1 : ClampModel P1 beta kappa L cminus cplus pmin)
    (hgap : 0 ≤ gap)
    (hsep : gap ≤ |clampFunctional P1 delta - clampFunctional P0 delta|)
    (hac : iidProduct P1 n ≪ iidProduct P0 n)
    (hint : Integrable (fun z => (((iidProduct P1 n).rnDeriv
      (iidProduct P0 n) z).toReal - 1) ^ 2) (iidProduct P0 n))
    (hchi0 : 0 ≤ chi) (hchi : productChiSq P1 P0 n ≤ chi) :
    ENNReal.ofReal ((1 - 2 * alpha - (1 / 2) * Real.sqrt chi) * gap) ≤
      observedMinimaxLength J n beta kappa L cminus cplus pmin delta alpha := by
  have hsqrt := Real.sqrt_le_sqrt hchi
  have hreal : (1 - 2 * alpha - (1 / 2) * Real.sqrt chi) * gap ≤
      (1 - 2 * alpha -
        (1 / 2) * Real.sqrt (productChiSq P1 P0 n)) * gap :=
    mul_le_mul_of_nonneg_right (by linarith) hgap
  exact (ENNReal.ofReal_le_ofReal hreal).trans
    (observedMinimaxLength_lower_of_two_point P0 P1 n beta kappa L cminus
      cplus pmin delta alpha gap hP0 hP1 hgap hsep hac hint)

/-- Every honest procedure's worst length dominates the minimax honest
length. The result uses [the `hC` condition](hyp:hC). [This is the stated conclusion](goal).
-/
lemma observedMinimaxLength_le_clampProcedureWorstLength
    (J n : ℕ) (beta kappa L cminus cplus pmin delta alpha : ℝ)
    (C : ConfidenceProcedure n J)
    (hC : UniformCoverage J n beta kappa L cminus cplus pmin delta alpha C) :
    observedMinimaxLength J n beta kappa L cminus cplus pmin delta alpha ≤
      clampProcedureWorstLength J n beta kappa L cminus cplus pmin C := by
  unfold observedMinimaxLength
  apply sInf_le
  exact ⟨C, hC, rfl⟩

/-- The fixed-Hölder minimax honest length has the root-sample-size lower
bound, uniformly over admissible threshold sequences. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
lemma observedMinimaxLength_eventually_ge_root
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha) :
    ∃ c : ℝ, 0 < c ∧ ∀ deltaSeq : ℕ → ℝ,
      ThresholdSequence deltaBar deltaSeq → ∀ᶠ n : ℕ in Filter.atTop,
      ENNReal.ofReal (c * (n : ℝ) ^ (-(1 : ℝ) / 2)) ≤
        observedMinimaxLength J n beta kappa L cminus cplus pmin
          (deltaSeq n) alpha := by
  let eta : ℝ := 1 - 2 * alpha
  let tau : ℝ := eta / 16
  let chi : ℝ := eta ^ 2 / 16
  let floor : ℝ := eta - (1 / 2) * Real.sqrt chi
  let c : ℝ := floor * tau
  have heta : 0 < eta := by dsimp [eta]; linarith [hreg.2.2.2.2.2.2.2.2.2.2.2.2]
  have heta1 : eta < 1 := by dsimp [eta]; linarith [hreg.2.2.2.2.2.2.2.2.2.2.2.1]
  have htau : 0 < tau := div_pos heta (by norm_num)
  have hchi0 : 0 ≤ chi := by dsimp [chi]; positivity
  have hsqrt : Real.sqrt chi = eta / 4 := by
    rw [show chi = (eta / 4) ^ 2 by dsimp [chi]; ring,
      Real.sqrt_sq_eq_abs, abs_of_pos (div_pos heta (by norm_num))]
  have hfloor : 0 < floor := by dsimp [floor]; rw [hsqrt]; linarith
  refine ⟨c, by dsimp [c]; positivity, ?_⟩
  intro deltaSeq hdelta
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnpos : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  let root : ℝ := (n : ℝ) ^ (-(1 : ℝ) / 2)
  let eps : ℝ := tau * root
  have hroot : 0 < root := Real.rpow_pos_of_pos hnR _
  have heps : 0 < eps := mul_pos htau hroot
  have hroot1 : root ≤ 1 := by
    rw [show (1 : ℝ) = 1 ^ (-(1 : ℝ) / 2) by norm_num]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hn) (by norm_num)
  have heps_le : eps ≤ 1 / 4 := by
    dsimp [eps, tau]
    nlinarith
  have hepsb : |eps| ≤ 1 / 2 := by rw [abs_of_pos heps]; linarith
  have hepss : |eps| < 1 / 2 := by rw [abs_of_pos heps]; linarith
  let P0 := minimaxClampLaw J kappa (fun _ : Fin J × ℝ => 0)
  let P1 := minimaxClampLaw J kappa (fun _ : Fin J × ℝ => eps)
  have hP0 : ClampModel P0 beta kappa L cminus cplus pmin :=
    minimaxCenter_mem_model J beta kappa L cminus cplus pmin deltaBar alpha hreg
  have hP1 : ClampModel P1 beta kappa L cminus cplus pmin :=
    minimaxConstant_mem_model J beta kappa L cminus cplus pmin deltaBar alpha
      eps hreg hepsb
  have hdelta1 : deltaSeq n ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(hdelta n).1, (hdelta n).2.trans hreg.2.2.2.2.2.2.2.2.2.2.1.le⟩
  have hsepEq := minimaxGlobalSeparation J kappa (deltaSeq n) eps hreg.1
    hreg.2.2.1 hdelta1 hepsb
  have hsep : eps ≤ |clampFunctional P1 (deltaSeq n) -
      clampFunctional P0 (deltaSeq n)| := by
    rw [show P1 = minimaxClampLaw J kappa (fun _ : Fin J × ℝ => eps) by rfl,
      show P0 = minimaxClampLaw J kappa (fun _ : Fin J × ℝ => 0) by rfl,
      hsepEq, abs_of_pos heps]
  have hrootSq : root ^ 2 = (n : ℝ)⁻¹ := by
    dsimp [root]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
    norm_num
    rw [Real.rpow_neg_one]
  have hepsSq : eps ^ 2 = tau ^ 2 * (n : ℝ)⁻¹ := by
    dsimp [eps]
    rw [mul_pow, hrootSq]
  letI : IsProbabilityMeasure (minimaxDesignMeasure J kappa) :=
    minimaxDesignMeasure_isProbabilityMeasure J kappa hreg.1 hreg.2.2.1
  have hintEq : (∫ p, 4 * ((fun _ : Fin J × ℝ => eps) p) ^ 2
      ∂minimaxDesignMeasure J kappa) = 4 * eps ^ 2 := by simp
  have hchiEq := minimaxProduct_chiSqDiv_center J n kappa hreg.1 hreg.2.2.1
    (fun _ : Fin J × ℝ => eps) measurable_const (fun _ => hepss)
  rw [hintEq] at hchiEq
  have hnE : (n : ℝ) * (4 * eps ^ 2) = eta ^ 2 / 64 := by
    rw [hepsSq]
    dsimp [tau]
    field_simp [hnR.ne']
    ring
  have hxabs : |eta ^ 2 / 64| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg eta]
  have hexp : Real.exp (eta ^ 2 / 64) ≤
      1 + eta ^ 2 / 64 + (eta ^ 2 / 64) ^ 2 :=
    Causalean.Stat.Concentration.exp_le_one_add_add_sq hxabs
  have hpoly : eta ^ 2 / 64 + (eta ^ 2 / 64) ^ 2 ≤ chi := by
    dsimp [chi]
    have heta_sq : eta ^ 2 ≤ 1 := by nlinarith [sq_nonneg eta]
    nlinarith [sq_nonneg (eta ^ 2 / 64)]
  have hpow : (1 + 4 * eps ^ 2) ^ n ≤ Real.exp (eta ^ 2 / 64) := by
    calc
      _ ≤ (Real.exp (4 * eps ^ 2)) ^ n :=
        pow_le_pow_left₀ (by positivity)
          (by simpa [add_comm] using Real.add_one_le_exp (4 * eps ^ 2)) n
      _ = Real.exp ((n : ℝ) * (4 * eps ^ 2)) := by rw [Real.exp_nat_mul]
      _ = _ := by rw [hnE]
  have hchi : productChiSq P1 P0 n ≤ chi := by
    change Causalean.Stat.chiSqDiv
      (Measure.pi (fun _ : Fin n => minimaxDataMeasure J kappa
        (fun _ : Fin J × ℝ => eps)))
      (Measure.pi (fun _ : Fin n => minimaxDataMeasure J kappa
        (fun _ : Fin J × ℝ => 0))) ≤ chi
    linarith [hchiEq, hpow, hexp, hpoly]
  have hac1 := minimaxDataMeasure_ac_center J kappa hreg.1 hreg.2.2.1
    (fun _ : Fin J × ℝ => eps) measurable_const (fun _ => hepss)
  have hint1 := minimaxDataMeasure_sq_integrable_center J kappa hreg.1 hreg.2.2.1
    (fun _ : Fin J × ℝ => eps) measurable_const (fun _ => hepss)
  letI : IsProbabilityMeasure (minimaxDataMeasure J kappa
      (fun _ : Fin J × ℝ => eps)) :=
    minimaxDataMeasure_isProbabilityMeasure J kappa hreg.1 hreg.2.2.1 _
      measurable_const (fun _ => hepsb)
  letI : IsProbabilityMeasure (minimaxDataMeasure J kappa
      (fun _ : Fin J × ℝ => 0)) :=
    minimaxDataMeasure_isProbabilityMeasure J kappa hreg.1 hreg.2.2.1 _
      measurable_const (fun _ => by norm_num)
  have hac := Causalean.Stat.pi_iid_absolutelyContinuous _ _ hac1 n
  have hint := Causalean.Stat.pi_iid_integrable_sq_dev _ _ hac1 hint1 n
  have hlower := observedMinimaxLength_lower_of_two_point_chi P0 P1 n beta
    kappa L cminus cplus pmin (deltaSeq n) alpha eps chi hP0 hP1 heps.le hsep
    (by simpa [P0, P1, iidProduct, minimaxClampLaw] using hac)
    (by simpa [P0, P1, iidProduct, minimaxClampLaw] using hint) hchi0 hchi
  dsimp [c, floor, eps, tau, root, eta] at hlower ⊢
  simpa [mul_assoc] using hlower

set_option maxHeartbeats 800000 in
/-- A fixed contraction of the information bandwidth gives the local
fixed-Hölder lower component for minimax honest expected length. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
lemma observedMinimaxLength_eventually_ge_local
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha) :
    ∃ c : ℝ, 0 < c ∧ ∀ deltaSeq : ℕ → ℝ,
      ThresholdSequence deltaBar deltaSeq → ∀ᶠ n : ℕ in Filter.atTop,
      let h := infoBandwidth n (deltaSeq n) beta kappa deltaBar
      ENNReal.ofReal (c * (deltaSeq n) ^ (kappa + 1) * h ^ beta) ≤
        observedMinimaxLength J n beta kappa L cminus cplus pmin
          (deltaSeq n) alpha := by
  have hr := hreg
  rcases hr with ⟨hJ, hbeta, hkappa, hL, hcminus, hcminus_le, hcplus,
    hpmin, hpmin_le, hdeltaBar, hdeltaBar1, halpha, halpha1⟩
  obtain ⟨amplitude, hamp, hamp_le, hamp_model⟩ :=
    exists_minimaxBump_amplitude beta L hbeta hL
  let eta : ℝ := 1 - 2 * alpha
  let s : ℝ := eta ^ 2 / 64
  let d0 : ℝ := 8 * (kappa + 1) * amplitude ^ 2
  let p : ℝ := 2 * beta + 1
  let t : ℝ := s / (d0 + 1)
  let chi : ℝ := eta ^ 2 / 16
  let floor : ℝ := eta - (1 / 2) * Real.sqrt chi
  let c : ℝ := floor * amplitude * t ^ beta
  have heta : 0 < eta := by dsimp [eta]; linarith
  have heta1 : eta < 1 := by dsimp [eta]; linarith
  have hs : 0 < s := by dsimp [s]; positivity
  have hs1 : s ≤ 1 := by dsimp [s]; nlinarith [sq_nonneg eta]
  have hd0 : 0 ≤ d0 := by dsimp [d0]; positivity
  have hp : 1 < p := by dsimp [p]; linarith
  have ht : 0 < t := div_pos hs (by linarith)
  have ht1 : t ≤ 1 := by
    dsimp [t]
    rw [div_le_one (by linarith : 0 < d0 + 1)]
    linarith
  have htp : t ^ p ≤ t :=
    Real.rpow_le_self_of_le_one ht.le ht1 hp.le
  have hdsmall : d0 * t ^ p ≤ s := by
    calc
      d0 * t ^ p ≤ d0 * t := mul_le_mul_of_nonneg_left htp hd0
      _ ≤ s := by
        dsimp [t]
        rw [← mul_div_assoc, div_le_iff₀ (by linarith : 0 < d0 + 1)]
        nlinarith [hs.le]
  have hchi0 : 0 ≤ chi := by dsimp [chi]; positivity
  have hsqrt : Real.sqrt chi = eta / 4 := by
    rw [show chi = (eta / 4) ^ 2 by dsimp [chi]; ring,
      Real.sqrt_sq_eq_abs, abs_of_pos (div_pos heta (by norm_num))]
  have hfloor : 0 < floor := by dsimp [floor]; rw [hsqrt]; linarith
  have hxabs : |s| ≤ 1 := by rw [abs_of_pos hs]; exact hs1
  have hexp : Real.exp s ≤ 1 + s + s ^ 2 :=
    Causalean.Stat.Concentration.exp_le_one_add_add_sq hxabs
  have hpoly : s + s ^ 2 ≤ chi := by
    dsimp [s, chi]
    have heta_sq : eta ^ 2 ≤ 1 := by nlinarith [sq_nonneg eta]
    nlinarith [sq_nonneg (eta ^ 2 / 64)]
  refine ⟨c, by dsimp [c]; positivity, ?_⟩
  intro deltaSeq hdelta
  have hbal := infoBandwidth_eventually_balance beta kappa deltaBar hbeta hkappa
    ⟨hdeltaBar, hdeltaBar1⟩ deltaSeq hdelta
  filter_upwards [hbal] with n hbn
  dsimp only
  let delta := deltaSeq n
  let h := infoBandwidth n delta beta kappa deltaBar
  let hsml := t * h
  let q := fun a : ℝ => amplitude * hsml ^ beta *
    CausalSmith.Stat.DoseResponseMinimax.doseBump ((a - delta) / hsml)
  let P0 := minimaxClampLaw J kappa (fun _ : Fin J × ℝ => 0)
  let P1 := minimaxClampLaw J kappa (fun z => q z.2)
  have hh : 0 < h := hbn.1
  have hh1 : h ≤ 1 := hbn.2.1.trans (by linarith)
  have hhs : 0 < hsml := mul_pos ht hh
  have hhs1 : hsml ≤ 1 := (mul_le_of_le_one_left hh.le ht1).trans hh1
  have hd : delta ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(hdelta n).1, (hdelta n).2.trans hdeltaBar1.le⟩
  have hshape := hamp_model hd.1 hd.2 hhs hhs1
  have hqmeas : Measurable q := by dsimp [q]; fun_prop
  have hq0 (a : ℝ) : 0 ≤ q a := by
    dsimp [q]
    exact mul_nonneg (mul_nonneg hamp.le (Real.rpow_nonneg hhs.le _))
      (CausalSmith.Stat.DoseResponseMinimax.doseBump_nonneg _)
  have hqbound (a : ℝ) : |q a| ≤ 1 / 2 := by
    rw [abs_of_nonneg (hq0 a)]
    have hb := CausalSmith.Stat.DoseResponseMinimax.doseBump_le_one
      ((a - delta) / hsml)
    have hpw := Real.rpow_le_one hhs.le hhs1 hbeta.le
    dsimp [q]
    calc
      _ ≤ amplitude * hsml ^ beta := by
        nlinarith [mul_nonneg hamp.le (Real.rpow_nonneg hhs.le beta)]
      _ ≤ amplitude := by simpa using mul_le_mul_of_nonneg_left hpw hamp.le
      _ ≤ 1 / 2 := by linarith
  have hqstrict (z : Fin J × ℝ) : |q z.2| < 1 / 2 := by
    rw [abs_of_nonneg (hq0 z.2)]
    have hb := CausalSmith.Stat.DoseResponseMinimax.doseBump_le_one
      ((z.2 - delta) / hsml)
    have hpw := Real.rpow_le_one hhs.le hhs1 hbeta.le
    have hqamp : q z.2 ≤ amplitude := by
      dsimp [q]
      calc
        _ ≤ amplitude * hsml ^ beta := by
          nlinarith [mul_nonneg hamp.le (Real.rpow_nonneg hhs.le beta)]
        _ ≤ amplitude := by simpa using mul_le_mul_of_nonneg_left hpw hamp.le
    linarith [hamp_le]
  have hP0 := minimaxCenter_mem_model J beta kappa L cminus cplus pmin
    deltaBar alpha hreg
  have hP1 : ClampModel P1 beta kappa L cminus cplus pmin := by
    apply minimaxClampModel_of_taylor J beta kappa L cminus cplus pmin
      hJ hbeta hkappa hcminus_le hcplus hpmin_le q hqmeas hqbound
    exact hshape.1
    exact hshape.2.1
    exact hshape.2.2
  have hsep0 := minimaxLocalSeparation J beta kappa delta hsml amplitude
    hJ hbeta hkappa hd hhs hhs1 hamp.le hamp_le
  have hsep : amplitude * delta ^ (kappa + 1) * hsml ^ beta ≤
      |clampFunctional P1 delta - clampFunctional P0 delta| := by
    have hn : 0 ≤ clampFunctional P1 delta - clampFunctional P0 delta :=
      (mul_nonneg (mul_nonneg hamp.le (Real.rpow_nonneg hd.1 _))
        (Real.rpow_nonneg hhs.le _)).trans (by simpa [P0, P1, q] using hsep0)
    rw [abs_of_nonneg hn]
    simpa [P0, P1, q] using hsep0
  let I := ∫ z, 4 * ((fun z : Fin J × ℝ => q z.2) z) ^ 2
    ∂minimaxDesignMeasure J kappa
  have hI := minimaxLocal_designIntegral_le J beta kappa delta hsml amplitude
    hJ hkappa hd.1 hhs hamp.le
  have hnI : (n : ℝ) * I ≤ s := by
    have hw : delta + hsml ≤ delta + h := by
      dsimp [hsml]
      nlinarith [mul_le_of_le_one_left hh.le ht1]
    have hpoww := Real.rpow_le_rpow (add_nonneg hd.1 hhs.le) hw hkappa
    have hb := hbn.2.2
    calc
      _ ≤ (n : ℝ) * (8 * (kappa + 1) * amplitude ^ 2 *
          hsml ^ (2 * beta + 1) * (delta + hsml) ^ kappa) :=
        mul_le_mul_of_nonneg_left (by simpa [I, q] using hI) (Nat.cast_nonneg n)
      _ ≤ d0 * t ^ p *
          ((n : ℝ) * h ^ (2 * beta + 1) * (delta + h) ^ kappa) := by
        dsimp [d0, p, hsml]
        rw [Real.mul_rpow ht.le hh.le]
        ring_nf
        gcongr
      _ = d0 * t ^ p := by rw [hb, mul_one]
      _ ≤ s := hdsmall
  have hchiEq := minimaxProduct_chiSqDiv_center J n kappa hJ hkappa
    (fun z : Fin J × ℝ => q z.2) (hqmeas.comp measurable_snd) hqstrict
  have hpow : (1 + I) ^ n ≤ Real.exp s := by
    calc
      _ ≤ (Real.exp I) ^ n := pow_le_pow_left₀ (by positivity)
        (by simpa [add_comm] using Real.add_one_le_exp I) n
      _ = Real.exp ((n : ℝ) * I) := by rw [Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr hnI
  have hchi : productChiSq P1 P0 n ≤ chi := by
    change Causalean.Stat.chiSqDiv _ _ ≤ chi
    dsimp [P0, P1, iidProduct, minimaxClampLaw]
    change 1 + Causalean.Stat.chiSqDiv _ _ = (1 + I) ^ n at hchiEq
    linarith [hexp, hpoly]
  have hac1 : minimaxDataMeasure J kappa (fun z : Fin J × ℝ => q z.2) ≪
      minimaxDataMeasure J kappa (fun _ : Fin J × ℝ => 0) :=
    minimaxDataMeasure_ac_center J kappa hJ hkappa _
      (hqmeas.comp measurable_snd) hqstrict
  have hint1 : Integrable
      (fun o => (((minimaxDataMeasure J kappa
        (fun z : Fin J × ℝ => q z.2)).rnDeriv
        (minimaxDataMeasure J kappa (fun _ : Fin J × ℝ => 0)) o).toReal - 1) ^ 2)
      (minimaxDataMeasure J kappa (fun _ : Fin J × ℝ => 0)) := by
    exact minimaxDataMeasure_sq_integrable_center J kappa hJ hkappa _
      (hqmeas.comp measurable_snd) hqstrict
  letI : IsProbabilityMeasure
      (minimaxDataMeasure J kappa (fun z : Fin J × ℝ => q z.2)) :=
    minimaxDataMeasure_isProbabilityMeasure J kappa hJ hkappa _
      (hqmeas.comp measurable_snd) (fun z => (hqstrict z).le)
  letI : IsProbabilityMeasure
      (minimaxDataMeasure J kappa (fun _ : Fin J × ℝ => 0)) :=
    minimaxDataMeasure_isProbabilityMeasure J kappa hJ hkappa _ measurable_const
      (fun _ => by norm_num)
  have hlower := observedMinimaxLength_lower_of_two_point_chi P0 P1 n beta
    kappa L cminus cplus pmin delta alpha
    (amplitude * delta ^ (kappa + 1) * hsml ^ beta) chi hP0 hP1
    (mul_nonneg (mul_nonneg hamp.le (Real.rpow_nonneg hd.1 _))
      (Real.rpow_nonneg hhs.le _)) hsep
    (by simpa [P0, P1, iidProduct, minimaxClampLaw] using
      Causalean.Stat.pi_iid_absolutelyContinuous _ _ hac1 n)
    (by simpa [P0, P1, iidProduct, minimaxClampLaw] using
      Causalean.Stat.pi_iid_integrable_sq_dev _ _ hac1 hint1 n)
    hchi0 hchi
  dsimp [c, floor, eta, hsml] at hlower ⊢
  rw [Real.mul_rpow ht.le hh.le] at hlower
  simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using hlower

/-- The root and localized experiments combine into the full fixed-Hölder
frontier lower bound for minimax honest expected length. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
lemma observedMinimaxLength_eventually_ge_frontier
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha) :
    ∃ c : ℝ, 0 < c ∧ ∀ deltaSeq : ℕ → ℝ,
      ThresholdSequence deltaBar deltaSeq → ∀ᶠ n : ℕ in Filter.atTop,
      ENNReal.ofReal (c * clampFrontier n (deltaSeq n) kappa
        (infoBandwidth n (deltaSeq n) beta kappa deltaBar) beta) ≤
        observedMinimaxLength J n beta kappa L cminus cplus pmin
          (deltaSeq n) alpha := by
  obtain ⟨c0, hc0, h0⟩ := observedMinimaxLength_eventually_ge_root J beta
    kappa L cminus cplus pmin deltaBar alpha hreg
  obtain ⟨c1, hc1, h1⟩ := observedMinimaxLength_eventually_ge_local J beta
    kappa L cminus cplus pmin deltaBar alpha hreg
  let c := min c0 c1 / 2
  refine ⟨c, by dsimp [c]; positivity, ?_⟩
  intro deltaSeq hdelta
  have hbal := infoBandwidth_eventually_balance beta kappa deltaBar hreg.2.1
    hreg.2.2.1 ⟨hreg.2.2.2.2.2.2.2.2.2.1,
      hreg.2.2.2.2.2.2.2.2.2.2.1⟩ deltaSeq hdelta
  filter_upwards [h0 deltaSeq hdelta, h1 deltaSeq hdelta, hbal] with n hn0 hn1 hbn
  let h := infoBandwidth n (deltaSeq n) beta kappa deltaBar
  let root : ℝ := (n : ℝ) ^ (-(1 : ℝ) / 2)
  let localTerm : ℝ := (deltaSeq n) ^ (kappa + 1) * h ^ beta
  have hroot : 0 ≤ root := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hlocal : 0 ≤ localTerm := mul_nonneg
    (Real.rpow_nonneg (hdelta n).1 _)
    (Real.rpow_nonneg hbn.1.le _)
  by_cases hle : c0 * root ≤ c1 * localTerm
  · apply (ENNReal.ofReal_le_ofReal ?_).trans
      (by simpa [mul_assoc] using hn1)
    dsimp [c, clampFrontier, root, localTerm, h]
    calc
      min c0 c1 / 2 *
          ((n : ℝ) ^ (-(1 : ℝ) / 2) +
            (deltaSeq n) ^ (kappa + 1) *
              (infoBandwidth n (deltaSeq n) beta kappa deltaBar) ^ beta) =
          (min c0 c1 * (n : ℝ) ^ (-(1 : ℝ) / 2) +
            min c0 c1 * ((deltaSeq n) ^ (kappa + 1) *
              (infoBandwidth n (deltaSeq n) beta kappa deltaBar) ^ beta)) / 2 := by ring
      _ ≤ (c0 * (n : ℝ) ^ (-(1 : ℝ) / 2) +
            c1 * ((deltaSeq n) ^ (kappa + 1) *
              (infoBandwidth n (deltaSeq n) beta kappa deltaBar) ^ beta)) / 2 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact add_le_add
            (mul_le_mul_of_nonneg_right (min_le_left _ _) hroot)
            (mul_le_mul_of_nonneg_right (min_le_right _ _) hlocal)
      _ ≤ c1 * ((deltaSeq n) ^ (kappa + 1) *
            (infoBandwidth n (deltaSeq n) beta kappa deltaBar) ^ beta) := by
          dsimp [root, localTerm, h] at hle
          linarith
  · apply (ENNReal.ofReal_le_ofReal ?_).trans hn0
    have hle' : c1 * localTerm ≤ c0 * root := le_of_not_ge hle
    dsimp [c, clampFrontier, root, localTerm, h]
    calc
      min c0 c1 / 2 *
          ((n : ℝ) ^ (-(1 : ℝ) / 2) +
            (deltaSeq n) ^ (kappa + 1) *
              (infoBandwidth n (deltaSeq n) beta kappa deltaBar) ^ beta) =
          (min c0 c1 * (n : ℝ) ^ (-(1 : ℝ) / 2) +
            min c0 c1 * ((deltaSeq n) ^ (kappa + 1) *
              (infoBandwidth n (deltaSeq n) beta kappa deltaBar) ^ beta)) / 2 := by ring
      _ ≤ (c0 * (n : ℝ) ^ (-(1 : ℝ) / 2) +
            c1 * ((deltaSeq n) ^ (kappa + 1) *
              (infoBandwidth n (deltaSeq n) beta kappa deltaBar) ^ beta)) / 2 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact add_le_add
            (mul_le_mul_of_nonneg_right (min_le_left _ _) hroot)
            (mul_le_mul_of_nonneg_right (min_le_right _ _) hlocal)
      _ ≤ c0 * (n : ℝ) ^ (-(1 : ℝ) / 2) := by
          dsimp [root, localTerm, h] at hle'
          linarith

/-- The same eventual frontier lower bound holds for the worst expected length
of every uniformly honest procedure. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
lemma procedureWorstLength_eventually_ge_frontier
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha) :
    ∃ c : ℝ, 0 < c ∧ ∀ deltaSeq : ℕ → ℝ,
      ThresholdSequence deltaBar deltaSeq → ∀ᶠ n : ℕ in Filter.atTop,
      ∀ C : ConfidenceProcedure n J,
        UniformCoverage J n beta kappa L cminus cplus pmin (deltaSeq n) alpha C →
        ENNReal.ofReal (c * clampFrontier n (deltaSeq n) kappa
          (infoBandwidth n (deltaSeq n) beta kappa deltaBar) beta) ≤
          clampProcedureWorstLength J n beta kappa L cminus cplus pmin C := by
  obtain ⟨c, hc, hmin⟩ := observedMinimaxLength_eventually_ge_frontier J beta
    kappa L cminus cplus pmin deltaBar alpha hreg
  refine ⟨c, hc, ?_⟩
  intro deltaSeq hdelta
  filter_upwards [hmin deltaSeq hdelta] with n hn
  intro C hC
  exact hn.trans (observedMinimaxLength_le_clampProcedureWorstLength J n beta
    kappa L cminus cplus pmin (deltaSeq n) alpha C hC)

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier

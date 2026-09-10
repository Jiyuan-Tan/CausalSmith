/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.ContinuityWitnessFunctional
import Causalean.Stat.Minimax.HonestConfidenceSet
import Causalean.Stat.Concentration.TailBounds.Bernstein

/-! # Two-point lower bounds for continuity-only honest confidence length -/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- A close pair in the continuity-only model lower-bounds minimax honest
expected interval length. The result uses [the `hP0` condition](hyp:hP0), [the `hP1` condition](hyp:hP1), [the `hgap` condition](hyp:hgap), [the `hsep` condition](hyp:hsep), [the `hac` condition](hyp:hac), [the `hint` condition](hyp:hint). [This is the stated conclusion](goal).
-/
lemma contMinimaxLength_lower_of_two_point
    (P0 P1 : ClampLaw J) (n : ℕ)
    (kappa cminus cplus pmin deltaBar delta alpha gap : ℝ)
    (hP0 : ContClampModel P0 kappa cminus cplus pmin deltaBar)
    (hP1 : ContClampModel P1 kappa cminus cplus pmin deltaBar)
    (hgap : 0 ≤ gap)
    (hsep : gap ≤ |contClampFunctional P1 kappa cminus cplus pmin deltaBar hP1 delta -
      contClampFunctional P0 kappa cminus cplus pmin deltaBar hP0 delta|)
    (hac : iidProduct P1 n ≪ iidProduct P0 n)
    (hint : Integrable (fun z => (((iidProduct P1 n).rnDeriv
      (iidProduct P0 n) z).toReal - 1) ^ 2) (iidProduct P0 n)) :
    ENNReal.ofReal ((1 - 2 * alpha -
        (1 / 2) * Real.sqrt (productChiSq P1 P0 n)) * gap) ≤
      (contFrontierCriteria J n kappa cminus cplus pmin deltaBar delta alpha).2.1 := by
  let theta0 := contClampFunctional P0 kappa cminus cplus pmin deltaBar hP0 delta
  let theta1 := contClampFunctional P1 kappa cminus cplus pmin deltaBar hP1 delta
  let outer : Set ℝ≥0∞ := {r : ℝ≥0∞ | ∃ C : ConfidenceProcedure n J,
    ObservedMeasurableInterval C ∧
    (∀ (P : ClampLaw J)
        (hP : ContClampModel P kappa cminus cplus pmin deltaBar),
      1 - alpha ≤ (iidProduct P n).real
        {z | contClampFunctional P kappa cminus cplus pmin deltaBar hP delta ∈ C z}) ∧
    r = sSup {v : ℝ≥0∞ | ∃ (P : ClampLaw J)
        (_hP : ContClampModel P kappa cminus cplus pmin deltaBar),
      v = ∫⁻ z, intervalLengthENNReal (C z) ∂iidProduct P n}}
  change _ ≤ sInf outer
  apply le_sInf
  intro r hr
  rcases hr with ⟨C, ⟨lo, hi, hlo, hhi, hord, hC⟩, hcover, rfl⟩
  let A : Set (Fin n → ClampObs J) := {z | theta0 ∈ C z}
  let B : Set (Fin n → ClampObs J) := {z | theta1 ∈ C z}
  have hA : MeasurableSet A := by
    simp only [A, hC, mem_Icc]
    exact
      ((measurableSet_le hlo measurable_const).inter
        (measurableSet_le measurable_const hhi))
  have hB : MeasurableSet B := by
    simp only [B, hC, mem_Icc]
    exact
      ((measurableSet_le hlo measurable_const).inter
        (measurableSet_le measurable_const hhi))
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
      rw [hC z]
      simp only [intervalLength, csSup_Icc (hord z), csInf_Icc (hord z)]
      rcases hz with ⟨hz0, hz1⟩
      have hz0' : lo z ≤ theta0 ∧ theta0 ≤ hi z := by
        simpa [A, theta0, hC z] using hz0
      have hz1' : lo z ≤ theta1 ∧ theta1 ≤ hi z := by
        simpa [B, theta1, hC z] using hz1
      rcases hz0' with ⟨hlo0, hhi0⟩
      rcases hz1' with ⟨hlo1, hhi1⟩
      have habs : |contClampFunctional P1 kappa cminus cplus pmin deltaBar hP1 delta -
          contClampFunctional P0 kappa cminus cplus pmin deltaBar hP0 delta| ≤
          hi z - lo z := by
        rw [abs_le]
        constructor <;> linarith
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
  apply htarget.trans
  exact le_sSup ⟨P0, hP0, rfl⟩

/-- A numerical upper bound on the product chi-square divergence gives a
corresponding explicit honest-length lower bound. The result uses [the `hP0` condition](hyp:hP0), [the `hP1` condition](hyp:hP1), [the `hgap` condition](hyp:hgap), [the `hsep` condition](hyp:hsep), [the `hac` condition](hyp:hac), [the `hint` condition](hyp:hint), [the `hchi0` condition](hyp:hchi0), [the `hchi` condition](hyp:hchi). [This is the stated conclusion](goal).
-/
lemma contMinimaxLength_lower_of_two_point_chi
    (P0 P1 : ClampLaw J) (n : ℕ)
    (kappa cminus cplus pmin deltaBar delta alpha gap chi : ℝ)
    (hP0 : ContClampModel P0 kappa cminus cplus pmin deltaBar)
    (hP1 : ContClampModel P1 kappa cminus cplus pmin deltaBar)
    (hgap : 0 ≤ gap)
    (hsep : gap ≤ |contClampFunctional P1 kappa cminus cplus pmin deltaBar hP1 delta -
      contClampFunctional P0 kappa cminus cplus pmin deltaBar hP0 delta|)
    (hac : iidProduct P1 n ≪ iidProduct P0 n)
    (hint : Integrable (fun z => (((iidProduct P1 n).rnDeriv
      (iidProduct P0 n) z).toReal - 1) ^ 2) (iidProduct P0 n))
    (hchi0 : 0 ≤ chi) (hchi : productChiSq P1 P0 n ≤ chi) :
    ENNReal.ofReal ((1 - 2 * alpha - (1 / 2) * Real.sqrt chi) * gap) ≤
      (contFrontierCriteria J n kappa cminus cplus pmin deltaBar delta alpha).2.1 := by
  have hsqrt := Real.sqrt_le_sqrt hchi
  have hreal : (1 - 2 * alpha - (1 / 2) * Real.sqrt chi) * gap ≤
      (1 - 2 * alpha -
        (1 / 2) * Real.sqrt (productChiSq P1 P0 n)) * gap :=
    mul_le_mul_of_nonneg_right (by linarith) hgap
  exact (ENNReal.ofReal_le_ofReal hreal).trans
    (contMinimaxLength_lower_of_two_point P0 P1 n kappa cminus cplus pmin
      deltaBar delta alpha gap hP0 hP1 hgap hsep hac hint)

/-- The continuity-only minimax honest length has the regular
root-sample-size lower bound, uniformly over threshold sequences. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
lemma contMinimaxLength_eventually_ge_root
    (J : ℕ) (kappa cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : ContRegimeConstants J kappa cminus cplus pmin deltaBar alpha) :
    ∃ c : ℝ, 0 < c ∧ ∀ deltaSeq : ℕ → ℝ,
      ThresholdSequence deltaBar deltaSeq → ∀ᶠ n : ℕ in Filter.atTop,
      ENNReal.ofReal (c * (n : ℝ) ^ (-(1 : ℝ) / 2)) ≤
        (contFrontierCriteria J n kappa cminus cplus pmin deltaBar
          (deltaSeq n) alpha).2.1 := by
  let eta : ℝ := 1 - 2 * alpha
  let tau : ℝ := eta / 16
  let chi : ℝ := eta ^ 2 / 16
  let floor : ℝ := eta - (1 / 2) * Real.sqrt chi
  let c : ℝ := floor * tau
  have heta : 0 < eta := by dsimp [eta]; linarith [hreg.2.2]
  have heta1 : eta < 1 := by dsimp [eta]; linarith [hreg.2.1]
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
  have heta_le : eta ≤ 1 := heta1.le
  have hroot1 : root ≤ 1 := by
    rw [show (1 : ℝ) = 1 ^ (-(1 : ℝ) / 2) by norm_num]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hn)
      (by norm_num)
  have heps_le : eps ≤ 1 / 4 := by
    dsimp [eps, tau]
    nlinarith
  have hepsb : |eps| ≤ 1 / 2 := by rw [abs_of_pos heps]; linarith
  have hepss : |eps| < 1 / 2 := by rw [abs_of_pos heps]; linarith
  let P0 := minimaxClampLaw J kappa (fun _ : Fin J × ℝ => 0)
  let P1 := minimaxClampLaw J kappa (fun _ : Fin J × ℝ => eps)
  have hw := continuityConstant_twoPoint J n kappa cminus cplus pmin deltaBar
    (deltaSeq n) eps hreg.1 (hdelta n) heps.le heps_le
  rcases hw with ⟨hP0, hP1, hsepEq, hchiExp⟩
  have hrootSq : root ^ 2 = (n : ℝ)⁻¹ := by
    dsimp [root]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
    norm_num
    rw [Real.rpow_neg_one]
  have hepsSq : eps ^ 2 = tau ^ 2 * (n : ℝ)⁻¹ := by
    dsimp [eps]
    rw [mul_pow, hrootSq]
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
  have hchi : productChiSq P1 P0 n ≤ chi := by
    rw [hnE] at hchiExp
    linarith
  have hac1 := minimaxDataMeasure_ac_center J kappa hreg.1.1 hreg.1.2.1
    (fun _ : Fin J × ℝ => eps) measurable_const (fun _ => hepss)
  have hint1 := minimaxDataMeasure_sq_integrable_center J kappa hreg.1.1 hreg.1.2.1
    (fun _ : Fin J × ℝ => eps) measurable_const (fun _ => hepss)
  letI : IsProbabilityMeasure (minimaxDataMeasure J kappa
      (fun _ : Fin J × ℝ => eps)) :=
    minimaxDataMeasure_isProbabilityMeasure J kappa hreg.1.1 hreg.1.2.1 _
      measurable_const (fun _ => hepsb)
  letI : IsProbabilityMeasure (minimaxDataMeasure J kappa
      (fun _ : Fin J × ℝ => 0)) :=
    minimaxDataMeasure_isProbabilityMeasure J kappa hreg.1.1 hreg.1.2.1 _
      measurable_const (fun _ => by norm_num)
  have hac := Causalean.Stat.pi_iid_absolutelyContinuous _ _ hac1 n
  have hint := Causalean.Stat.pi_iid_integrable_sq_dev _ _ hac1 hint1 n
  have hlower := contMinimaxLength_lower_of_two_point_chi P0 P1 n kappa cminus
    cplus pmin deltaBar (deltaSeq n) alpha eps chi hP0 hP1 heps.le
    (by simpa [P0, P1] using hsepEq.le)
    (by simpa [P0, P1, iidProduct, minimaxClampLaw] using hac)
    (by simpa [P0, P1, iidProduct, minimaxClampLaw] using hint)
    hchi0 hchi
  dsimp [c, floor, eps, tau, root, eta] at hlower ⊢
  simpa [mul_assoc] using hlower

/-- Narrow continuous bumps give an atom-scale lower bound for
continuity-only minimax honest length. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
lemma contMinimaxLength_eventually_ge_atom
    (J : ℕ) (kappa cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : ContRegimeConstants J kappa cminus cplus pmin deltaBar alpha) :
    ∃ c : ℝ, 0 < c ∧ ∀ deltaSeq : ℕ → ℝ,
      ThresholdSequence deltaBar deltaSeq → ∀ᶠ n : ℕ in Filter.atTop,
      ENNReal.ofReal (c * (deltaSeq n) ^ (kappa + 1)) ≤
        (contFrontierCriteria J n kappa cminus cplus pmin deltaBar
          (deltaSeq n) alpha).2.1 := by
  let eta : ℝ := 1 - 2 * alpha
  let amplitude : ℝ := 1 / 4
  let chi : ℝ := eta ^ 2 / 16
  let floor : ℝ := eta - (1 / 2) * Real.sqrt chi
  let c : ℝ := floor * amplitude
  have heta : 0 < eta := by dsimp [eta]; linarith [hreg.2.2]
  have heta1 : eta < 1 := by dsimp [eta]; linarith [hreg.2.1]
  have hchi0 : 0 ≤ chi := by dsimp [chi]; positivity
  have hsqrt : Real.sqrt chi = eta / 4 := by
    rw [show chi = (eta / 4) ^ 2 by dsimp [chi]; ring,
      Real.sqrt_sq_eq_abs, abs_of_pos (div_pos heta (by norm_num))]
  have hfloor : 0 < floor := by dsimp [floor]; rw [hsqrt]; linarith
  refine ⟨c, by dsimp [c, amplitude]; positivity, ?_⟩
  intro deltaSeq hdelta
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnpos : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  let A : ℝ := 8 * (kappa + 1) * amplitude ^ 2 * (deltaBar + 1) ^ kappa
  let K : ℝ := eta ^ 2 + 64 * A
  let h : ℝ := eta ^ 2 / (K * (n : ℝ))
  have hk1 : 0 ≤ kappa + 1 := by linarith [hreg.1.2.1]
  have hd1 : 0 ≤ deltaBar + 1 := by
    linarith [hreg.1.2.2.2.2.2.2.2.1]
  have hA : 0 ≤ A := by
    dsimp [A, amplitude]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hk1) (sq_nonneg _))
      (Real.rpow_nonneg hd1 _)
  have hK : 0 < K := by dsimp [K]; positivity
  have hh : 0 < h := by dsimp [h]; positivity
  have hh1 : h ≤ 1 := by
    rw [div_le_one (mul_pos hK hnR)]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    dsimp [K]
    nlinarith [sq_nonneg eta]
  have hdh : deltaSeq n + h ≤ deltaBar + 1 := by
    linarith [(hdelta n).2]
  have hpow : (deltaSeq n + h) ^ kappa ≤ (deltaBar + 1) ^ kappa :=
    Real.rpow_le_rpow (add_nonneg (hdelta n).1 hh.le) hdh hreg.1.2.1
  have hcoef : 0 ≤ 8 * (kappa + 1) * amplitude ^ 2 * h := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hk1) (sq_nonneg _)) hh.le
  have hcore : (n : ℝ) * (8 * (kappa + 1) * amplitude ^ 2 * h *
      (deltaBar + 1) ^ kappa) = A * eta ^ 2 / K := by
    dsimp [h, A]
    field_simp [hK.ne', hnR.ne']
  have hfrac : A * eta ^ 2 / K ≤ eta ^ 2 / 64 := by
    rw [div_le_iff₀ hK]
    dsimp [K]
    nlinarith [sq_nonneg eta]
  have hexponent : (n : ℝ) * (8 * (kappa + 1) * amplitude ^ 2 * h *
      (deltaSeq n + h) ^ kappa) ≤ eta ^ 2 / 64 := by
    calc
      _ ≤ (n : ℝ) * (8 * (kappa + 1) * amplitude ^ 2 * h *
          (deltaBar + 1) ^ kappa) := by gcongr
      _ = A * eta ^ 2 / K := hcore
      _ ≤ _ := hfrac
  have hw := continuityBump_twoPoint J n kappa cminus cplus pmin deltaBar
    (deltaSeq n) h amplitude hreg.1 (hdelta n) hh (by norm_num [amplitude])
    (by norm_num [amplitude])
  let q := fun a : ℝ => amplitude *
    CausalSmith.Stat.DoseResponseMinimax.doseBump ((a - deltaSeq n) / h)
  let P0 := minimaxClampLaw J kappa (fun _ : Fin J × ℝ => 0)
  let P1 := minimaxClampLaw J kappa (fun p => q p.2)
  rcases hw with ⟨hP0, hP1, hsep, hchiExp⟩
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
  have hchi : productChiSq P1 P0 n ≤ chi := by
    have hbound := hchiExp.trans (Real.exp_le_exp.mpr hexponent)
    linarith
  have hqmeas : Measurable q := by dsimp [q]; fun_prop
  have hq0 (a : ℝ) : 0 ≤ q a := by
    exact mul_nonneg (by norm_num [amplitude])
      (CausalSmith.Stat.DoseResponseMinimax.doseBump_nonneg _)
  have hqbound (a : ℝ) : |q a| ≤ 1 / 2 := by
    rw [abs_of_nonneg (hq0 a)]
    have hb := CausalSmith.Stat.DoseResponseMinimax.doseBump_le_one
      ((a - deltaSeq n) / h)
    dsimp [q, amplitude]
    nlinarith
  have hqstrict (p : Fin J × ℝ) : |q p.2| < 1 / 2 := by
    rw [abs_of_nonneg (hq0 p.2)]
    have hb := CausalSmith.Stat.DoseResponseMinimax.doseBump_le_one
      ((p.2 - deltaSeq n) / h)
    dsimp [q, amplitude]
    nlinarith
  have hac1 := minimaxDataMeasure_ac_center J kappa hreg.1.1 hreg.1.2.1
    (fun p : Fin J × ℝ => q p.2) (hqmeas.comp measurable_snd) hqstrict
  have hint1 := minimaxDataMeasure_sq_integrable_center J kappa hreg.1.1 hreg.1.2.1
    (fun p : Fin J × ℝ => q p.2) (hqmeas.comp measurable_snd) hqstrict
  letI : IsProbabilityMeasure (minimaxDataMeasure J kappa
      (fun p : Fin J × ℝ => q p.2)) :=
    minimaxDataMeasure_isProbabilityMeasure J kappa hreg.1.1 hreg.1.2.1 _
      (hqmeas.comp measurable_snd) (fun p => hqbound p.2)
  letI : IsProbabilityMeasure (minimaxDataMeasure J kappa
      (fun _ : Fin J × ℝ => 0)) :=
    minimaxDataMeasure_isProbabilityMeasure J kappa hreg.1.1 hreg.1.2.1 _
      measurable_const (fun _ => by norm_num)
  have hac := Causalean.Stat.pi_iid_absolutelyContinuous _ _ hac1 n
  have hint := Causalean.Stat.pi_iid_integrable_sq_dev _ _ hac1 hint1 n
  have hlower := contMinimaxLength_lower_of_two_point_chi P0 P1 n kappa cminus
    cplus pmin deltaBar (deltaSeq n) alpha
    (amplitude * (deltaSeq n) ^ (kappa + 1)) chi hP0 hP1
    (mul_nonneg (by norm_num [amplitude]) (Real.rpow_nonneg (hdelta n).1 _)) hsep
    (by simpa [P0, P1, q, iidProduct, minimaxClampLaw] using hac)
    (by simpa [P0, P1, q, iidProduct, minimaxClampLaw] using hint)
    hchi0 hchi
  dsimp [c, floor, amplitude, eta] at hlower ⊢
  simpa [mul_assoc] using hlower

/-- The regular and atom experiments combine into the full continuity
frontier lower bound for minimax honest expected length. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
lemma contMinimaxLength_eventually_ge_frontier
    (J : ℕ) (kappa cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : ContRegimeConstants J kappa cminus cplus pmin deltaBar alpha) :
    ∃ c : ℝ, 0 < c ∧ ∀ deltaSeq : ℕ → ℝ,
      ThresholdSequence deltaBar deltaSeq → ∀ᶠ n : ℕ in Filter.atTop,
      ENNReal.ofReal (c * contFrontier n (deltaSeq n) kappa) ≤
        (contFrontierCriteria J n kappa cminus cplus pmin deltaBar
          (deltaSeq n) alpha).2.1 := by
  obtain ⟨c0, hc0, h0⟩ := contMinimaxLength_eventually_ge_root J kappa
    cminus cplus pmin deltaBar alpha hreg
  obtain ⟨c1, hc1, h1⟩ := contMinimaxLength_eventually_ge_atom J kappa
    cminus cplus pmin deltaBar alpha hreg
  let c := min c0 c1 / 2
  refine ⟨c, by dsimp [c]; positivity, ?_⟩
  intro deltaSeq hdelta
  filter_upwards [h0 deltaSeq hdelta, h1 deltaSeq hdelta] with n hn0 hn1
  let root : ℝ := (n : ℝ) ^ (-(1 : ℝ) / 2)
  let atom : ℝ := (deltaSeq n) ^ (kappa + 1)
  have hroot : 0 ≤ root := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hatom : 0 ≤ atom := Real.rpow_nonneg (hdelta n).1 _
  by_cases hle : c0 * root ≤ c1 * atom
  · apply (ENNReal.ofReal_le_ofReal ?_).trans hn1
    dsimp [c, contFrontier, root, atom]
    calc
      min c0 c1 / 2 *
          ((n : ℝ) ^ (-(1 : ℝ) / 2) + (deltaSeq n) ^ (kappa + 1)) =
          (min c0 c1 * (n : ℝ) ^ (-(1 : ℝ) / 2) +
            min c0 c1 * (deltaSeq n) ^ (kappa + 1)) / 2 := by ring
      _ ≤ (c0 * (n : ℝ) ^ (-(1 : ℝ) / 2) +
            c1 * (deltaSeq n) ^ (kappa + 1)) / 2 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact add_le_add
            (mul_le_mul_of_nonneg_right (min_le_left _ _) hroot)
            (mul_le_mul_of_nonneg_right (min_le_right _ _) hatom)
      _ ≤ c1 * (deltaSeq n) ^ (kappa + 1) := by
          dsimp [root, atom] at hle
          linarith
  · apply (ENNReal.ofReal_le_ofReal ?_).trans hn0
    have hle' : c1 * atom ≤ c0 * root := le_of_not_ge hle
    dsimp [c, contFrontier, root, atom]
    calc
      min c0 c1 / 2 *
          ((n : ℝ) ^ (-(1 : ℝ) / 2) + (deltaSeq n) ^ (kappa + 1)) =
          (min c0 c1 * (n : ℝ) ^ (-(1 : ℝ) / 2) +
            min c0 c1 * (deltaSeq n) ^ (kappa + 1)) / 2 := by ring
      _ ≤ (c0 * (n : ℝ) ^ (-(1 : ℝ) / 2) +
            c1 * (deltaSeq n) ^ (kappa + 1)) / 2 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact add_le_add
            (mul_le_mul_of_nonneg_right (min_le_left _ _) hroot)
            (mul_le_mul_of_nonneg_right (min_le_right _ _) hatom)
      _ ≤ c0 * (n : ℝ) ^ (-(1 : ℝ) / 2) := by
          dsimp [root, atom] at hle'
          linarith

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier

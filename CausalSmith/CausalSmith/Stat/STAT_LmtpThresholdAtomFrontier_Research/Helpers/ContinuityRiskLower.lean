/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.ContinuityWitnessFunctional

/-! # Two-point lower bounds for continuity-only risk -/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory Set

noncomputable section

/-- A close pair in the continuity-only model lower-bounds its observed
minimax absolute risk. The result uses [the `hreg` condition](hyp:hreg), [the `hdelta` condition](hyp:hdelta), [the `hP0` condition](hyp:hP0), [the `hP1` condition](hyp:hP1), [the `hgap0` condition](hyp:hgap0), [the `hsep` condition](hyp:hsep), [the `hac` condition](hyp:hac), [the `hint` condition](hyp:hint), [the `hchi0` condition](hyp:hchi0), [the `hchi4` condition](hyp:hchi4), [the `hchi` condition](hyp:hchi). [This is the stated conclusion](goal).
-/
lemma contMinimaxRisk_lower_of_two_point
    (P0 P1 : ClampLaw J) (n : ℕ)
    (kappa cminus cplus pmin deltaBar delta gap chi : ℝ)
    (hreg : ContDesignConstants J kappa cminus cplus pmin deltaBar)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar)
    (hP0 : ContClampModel P0 kappa cminus cplus pmin deltaBar)
    (hP1 : ContClampModel P1 kappa cminus cplus pmin deltaBar)
    (hgap0 : 0 ≤ gap)
    (hsep : gap ≤ |contClampFunctional P1 kappa cminus cplus pmin deltaBar hP1 delta -
      contClampFunctional P0 kappa cminus cplus pmin deltaBar hP0 delta|)
    (hac : iidProduct P1 n ≪ iidProduct P0 n)
    (hint : Integrable (fun z => (((iidProduct P1 n).rnDeriv
      (iidProduct P0 n) z).toReal - 1) ^ 2) (iidProduct P0 n))
    (hchi0 : 0 ≤ chi) (hchi4 : chi < 4)
    (hchi : productChiSq P1 P0 n ≤ chi) :
    ((1 - (1 / 2) * Real.sqrt chi) / 4) * gap ≤
      (contFrontierCriteria J n kappa cminus cplus pmin deltaBar delta 0).1 := by
  let target := fun (P : ClampLaw J)
      (hP : ContClampModel P kappa cminus cplus pmin deltaBar) =>
    contClampFunctional P kappa cminus cplus pmin deltaBar hP delta
  let outer : Set ℝ := {r : ℝ | ∃ est : Estimator n J,
    ObservedMeasurableEstimator est ∧ (∀ z, est z ∈ Set.Icc (0 : ℝ) 1) ∧
    r = sSup {v : ℝ | ∃ (P : ClampLaw J)
      (hP : ContClampModel P kappa cminus cplus pmin deltaBar),
      v = contEstimatorRisk P n kappa cminus cplus pmin deltaBar delta hP est}}
  change _ ≤ sInf outer
  have houter : outer.Nonempty := by
    let est : Estimator n J := fun _ => 0
    refine ⟨sSup {v : ℝ | ∃ (P : ClampLaw J)
      (hP : ContClampModel P kappa cminus cplus pmin deltaBar),
      v = contEstimatorRisk P n kappa cminus cplus pmin deltaBar delta hP est},
      est, measurable_const, fun _ => ⟨le_rfl, by norm_num⟩, rfl⟩
  apply le_csInf houter
  intro r hr
  rcases hr with ⟨est, hest, hestrange, rfl⟩
  let risks : Set ℝ := {v : ℝ | ∃ (P : ClampLaw J)
    (hP : ContClampModel P kappa cminus cplus pmin deltaBar),
    v = contEstimatorRisk P n kappa cminus cplus pmin deltaBar delta hP est}
  have hrisk_le (P : ClampLaw J)
      (hP : ContClampModel P kappa cminus cplus pmin deltaBar) :
      contEstimatorRisk P n kappa cminus cplus pmin deltaBar delta hP est ≤ 1 := by
    letI : IsProbabilityMeasure P.dataMeasure := hP.probability
    letI : IsProbabilityMeasure (iidProduct P n) := by unfold iidProduct; infer_instance
    have ht := contClampFunctional_mem_Icc P kappa cminus cplus pmin deltaBar
      delta hP hreg hdelta
    unfold contEstimatorRisk
    have hfint : Integrable (fun z => |est z - target P hP|) (iidProduct P n) := by
      refine Integrable.of_bound ((hest.sub measurable_const).abs.aestronglyMeasurable) 1 ?_
      filter_upwards with z
      rw [Real.norm_eq_abs, abs_abs, abs_le]
      exact ⟨by dsimp [target]; linarith [(hestrange z).1, ht.2],
        by dsimp [target]; linarith [(hestrange z).2, ht.1]⟩
    calc
      (∫ z, |est z - target P hP| ∂iidProduct P n) ≤
          ∫ _z, (1 : ℝ) ∂iidProduct P n := by
        apply integral_mono_ae hfint (integrable_const 1)
        filter_upwards with z
        rw [abs_le]
        exact ⟨by dsimp [target]; linarith [(hestrange z).1, ht.2],
          by dsimp [target]; linarith [(hestrange z).2, ht.1]⟩
      _ = 1 := by simp
  have hbdd : BddAbove risks := by
    refine ⟨1, ?_⟩
    rintro v ⟨P, hP, rfl⟩
    exact hrisk_le P hP
  have hle0 : contEstimatorRisk P0 n kappa cminus cplus pmin deltaBar delta hP0 est ≤
      sSup risks := le_csSup hbdd ⟨P0, hP0, rfl⟩
  have hle1 : contEstimatorRisk P1 n kappa cminus cplus pmin deltaBar delta hP1 est ≤
      sSup risks := le_csSup hbdd ⟨P1, hP1, rfl⟩
  letI : IsProbabilityMeasure P0.dataMeasure := hP0.probability
  letI : IsProbabilityMeasure P1.dataMeasure := hP1.probability
  letI : IsProbabilityMeasure (iidProduct P0 n) := by unfold iidProduct; infer_instance
  letI : IsProbabilityMeasure (iidProduct P1 n) := by unfold iidProduct; infer_instance
  have htest := Causalean.Stat.two_point_lower_bound_of_chiSqDiv_le
    (P₀ := iidProduct P1 n) (P₁ := iidProduct P0 n) hest
    (θ₀ := target P1 hP1) (θ₁ := target P0 hP0)
    (s := gap / 2) (c := chi) (by dsimp [target]; convert hsep using 1 <;> ring)
    hac hint hchi
  have hfloor : 0 < (1 - (1 / 2) * Real.sqrt chi) / 2 := by
    have hsqrt : Real.sqrt chi < 2 := by
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
      convert hchi4 using 1 <;> norm_num
    linarith
  have hint0 : Integrable (fun z => |est z - target P0 hP0|) (iidProduct P0 n) := by
    refine Integrable.of_bound ((hest.sub measurable_const).abs.aestronglyMeasurable) 1 ?_
    have ht := contClampFunctional_mem_Icc P0 kappa cminus cplus pmin deltaBar
      delta hP0 hreg hdelta
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_abs, abs_le]
    exact ⟨by dsimp [target]; linarith [(hestrange z).1, ht.2],
      by dsimp [target]; linarith [(hestrange z).2, ht.1]⟩
  have hint1 : Integrable (fun z => |est z - target P1 hP1|) (iidProduct P1 n) := by
    refine Integrable.of_bound ((hest.sub measurable_const).abs.aestronglyMeasurable) 1 ?_
    have ht := contClampFunctional_mem_Icc P1 kappa cminus cplus pmin deltaBar
      delta hP1 hreg hdelta
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_abs, abs_le]
    exact ⟨by dsimp [target]; linarith [(hestrange z).1, ht.2],
      by dsimp [target]; linarith [(hestrange z).2, ht.1]⟩
  have hevent0 := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ fun z => abs_nonneg (est z - target P1 hP1)) hint1 (gap / 2)
  have hevent1 := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ fun z => abs_nonneg (est z - target P0 hP0)) hint0 (gap / 2)
  have hmaxEvent : ((1 - (1 / 2) * Real.sqrt chi) / 2) * (gap / 2) ≤
      max (contEstimatorRisk P1 n kappa cminus cplus pmin deltaBar delta hP1 est)
        (contEstimatorRisk P0 n kappa cminus cplus pmin deltaBar delta hP0 est) := by
    unfold contEstimatorRisk
    have hg2 : 0 ≤ gap / 2 := by positivity
    calc
      _ ≤ (gap / 2) * max
          ((iidProduct P1 n).real {z | gap / 2 ≤ |est z - target P1 hP1|})
          ((iidProduct P0 n).real {z | gap / 2 ≤ |est z - target P0 hP0|}) := by
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_left htest hg2
      _ = max ((gap / 2) * (iidProduct P1 n).real
          {z | gap / 2 ≤ |est z - target P1 hP1|})
          ((gap / 2) * (iidProduct P0 n).real
          {z | gap / 2 ≤ |est z - target P0 hP0|}) := by
            rw [mul_max_of_nonneg _ _ hg2]
      _ ≤ _ := max_le_max hevent0 hevent1
  calc
    ((1 - (1 / 2) * Real.sqrt chi) / 4) * gap =
        ((1 - (1 / 2) * Real.sqrt chi) / 2) * (gap / 2) := by ring
    _ ≤ max (contEstimatorRisk P1 n kappa cminus cplus pmin deltaBar delta hP1 est)
      (contEstimatorRisk P0 n kappa cminus cplus pmin deltaBar delta hP0 est) := hmaxEvent
    _ ≤ sSup risks := max_le hle1 hle0

/-- The continuity-only minimax risk has the regular root-sample lower bound,
uniformly over threshold sequences. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
lemma contMinimaxRisk_eventually_ge_root
    (J : ℕ) (kappa cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : ContRegimeConstants J kappa cminus cplus pmin deltaBar alpha) :
    ∃ c : ℝ, 0 < c ∧ ∀ deltaSeq : ℕ → ℝ,
      ThresholdSequence deltaBar deltaSeq → ∀ᶠ n : ℕ in Filter.atTop,
      c * (n : ℝ) ^ (-(1 : ℝ) / 2) ≤
        (contFrontierCriteria J n kappa cminus cplus pmin deltaBar
          (deltaSeq n) alpha).1 := by
  let chi : ℝ := Real.exp (1 / 4 : ℝ) - 1
  let floor : ℝ := (1 - (1 / 2) * Real.sqrt chi) / 4
  let c : ℝ := floor / 4
  have hchi0 : 0 ≤ chi := sub_nonneg.mpr (Real.one_le_exp (by norm_num))
  have hchi4 : chi < 4 := by
    dsimp [chi]
    have he : Real.exp (1 / 4 : ℝ) < Real.exp 1 :=
      Real.exp_lt_exp.mpr (by norm_num)
    linarith [Real.exp_one_lt_three]
  have hfloor : 0 < floor := by
    dsimp [floor]
    have hs : Real.sqrt chi < 2 := by
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
      convert hchi4 using 1 <;> norm_num
    linarith
  refine ⟨c, by dsimp [c]; positivity, ?_⟩
  intro deltaSeq hdelta
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnpos : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  let root : ℝ := (n : ℝ) ^ (-(1 : ℝ) / 2)
  let eps : ℝ := (1 / 4 : ℝ) * root
  have hroot : 0 < root := Real.rpow_pos_of_pos hnR _
  have heps : 0 < eps := mul_pos (by norm_num) hroot
  have heps_le : eps ≤ 1 / 4 := by
    have hroot1 : root ≤ 1 := by
      rw [show (1 : ℝ) = 1 ^ (-(1 : ℝ) / 2) by norm_num]
      exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hn)
        (by norm_num)
    dsimp [eps]
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
  have hepsSq : eps ^ 2 = (1 / 16 : ℝ) * (n : ℝ)⁻¹ := by
    dsimp [eps]
    rw [mul_pow, hrootSq]
    norm_num
  have hnE : (n : ℝ) * (4 * eps ^ 2) = 1 / 4 := by
    rw [hepsSq]
    field_simp [hnR.ne']
    ring
  have hchi : productChiSq P1 P0 n ≤ chi := by
    dsimp [chi]
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
  have hlower := contMinimaxRisk_lower_of_two_point P0 P1 n kappa cminus
    cplus pmin deltaBar (deltaSeq n) eps chi hreg.1 (hdelta n) hP0 hP1
    heps.le (by simpa [P0, P1] using hsepEq.le)
    (by simpa [P0, P1, iidProduct, minimaxClampLaw] using hac)
    (by simpa [P0, P1, iidProduct, minimaxClampLaw] using hint)
    hchi0 hchi4 hchi
  change _ ≤ (contFrontierCriteria J n kappa cminus cplus pmin deltaBar
    (deltaSeq n) 0).1 at hlower
  dsimp [c, floor, eps, root] at hlower ⊢
  change _ ≤ (contFrontierCriteria J n kappa cminus cplus pmin deltaBar
    (deltaSeq n) 0).1
  convert hlower using 1 <;> ring

/-- Arbitrarily narrow continuous bumps give an atom-scale minimax lower
bound uniformly over the whole threshold range. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
lemma contMinimaxRisk_eventually_ge_atom
    (J : ℕ) (kappa cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : ContRegimeConstants J kappa cminus cplus pmin deltaBar alpha) :
    ∃ c : ℝ, 0 < c ∧ ∀ deltaSeq : ℕ → ℝ,
      ThresholdSequence deltaBar deltaSeq → ∀ᶠ n : ℕ in Filter.atTop,
      c * (deltaSeq n) ^ (kappa + 1) ≤
        (contFrontierCriteria J n kappa cminus cplus pmin deltaBar
          (deltaSeq n) alpha).1 := by
  let amplitude : ℝ := 1 / 4
  let chi : ℝ := Real.exp 1 - 1
  let floor : ℝ := (1 - (1 / 2) * Real.sqrt chi) / 4
  let c : ℝ := floor * amplitude
  have hchi0 : 0 ≤ chi := sub_nonneg.mpr (Real.one_le_exp zero_le_one)
  have hchi4 : chi < 4 := by dsimp [chi]; linarith [Real.exp_one_lt_three]
  have hfloor : 0 < floor := by
    dsimp [floor]
    have hs : Real.sqrt chi < 2 := by
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
      convert hchi4 using 1 <;> norm_num
    linarith
  refine ⟨c, by dsimp [c, amplitude]; positivity, ?_⟩
  intro deltaSeq hdelta
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnpos : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  let A : ℝ := 8 * (kappa + 1) * amplitude ^ 2 * (deltaBar + 1) ^ kappa
  let K : ℝ := 1 + A
  let h : ℝ := 1 / (K * (n : ℝ))
  have hk1 : 0 ≤ kappa + 1 := by linarith [hreg.1.2.1]
  have hd1 : 0 ≤ deltaBar + 1 := by
    linarith [hreg.1.2.2.2.2.2.2.2.1]
  have hA : 0 ≤ A := by
    dsimp [A, amplitude]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hk1) (sq_nonneg _))
      (Real.rpow_nonneg hd1 _)
  have hK : 0 < K := by dsimp [K]; linarith
  have hh : 0 < h := by dsimp [h]; positivity
  have hh1 : h ≤ 1 := by
    rw [show h = (K * (n : ℝ))⁻¹ by simp [h]]
    rw [inv_le_one₀ (mul_pos hK hnR)]
    nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn]
  have hdh : deltaSeq n + h ≤ deltaBar + 1 := by
    linarith [(hdelta n).2]
  have hpow : (deltaSeq n + h) ^ kappa ≤ (deltaBar + 1) ^ kappa := by
    exact Real.rpow_le_rpow (add_nonneg (hdelta n).1 hh.le) hdh hreg.1.2.1
  have hcoef : 0 ≤ 8 * (kappa + 1) * amplitude ^ 2 * h := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (by linarith [hreg.1.2.1])) (sq_nonneg _)) hh.le
  have hexp : (n : ℝ) * (8 * (kappa + 1) * amplitude ^ 2 * h *
      (deltaSeq n + h) ^ kappa) ≤ 1 := by
    have hcore : (n : ℝ) * (8 * (kappa + 1) * amplitude ^ 2 * h *
        (deltaBar + 1) ^ kappa) = A / K := by
      dsimp [h, A]
      field_simp [hK.ne', hnR.ne']
      <;> ring
    calc
      _ ≤ (n : ℝ) * (8 * (kappa + 1) * amplitude ^ 2 * h *
          (deltaBar + 1) ^ kappa) := by gcongr
      _ = A / K := hcore
      _ ≤ 1 := by rw [div_le_one hK]; dsimp [K]; linarith
  have hw := continuityBump_twoPoint J n kappa cminus cplus pmin deltaBar
    (deltaSeq n) h amplitude hreg.1 (hdelta n) hh (by norm_num [amplitude])
    (by norm_num [amplitude])
  let q := fun a : ℝ => amplitude *
    CausalSmith.Stat.DoseResponseMinimax.doseBump ((a - deltaSeq n) / h)
  let P0 := minimaxClampLaw J kappa (fun _ : Fin J × ℝ => 0)
  let P1 := minimaxClampLaw J kappa (fun p => q p.2)
  rcases hw with ⟨hP0, hP1, hsep, hchiExp⟩
  have hchi : productChiSq P1 P0 n ≤ chi := by
    dsimp [chi]
    have := hchiExp.trans (Real.exp_le_exp.mpr hexp)
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
  have hlower := contMinimaxRisk_lower_of_two_point P0 P1 n kappa cminus cplus
    pmin deltaBar (deltaSeq n) (amplitude * (deltaSeq n) ^ (kappa + 1)) chi
    hreg.1 (hdelta n) hP0 hP1
    (mul_nonneg (by norm_num [amplitude]) (Real.rpow_nonneg (hdelta n).1 _))
    hsep
    (by simpa [P0, P1, q, iidProduct, minimaxClampLaw] using hac)
    (by simpa [P0, P1, q, iidProduct, minimaxClampLaw] using hint)
    hchi0 hchi4 hchi
  change _ ≤ (contFrontierCriteria J n kappa cminus cplus pmin deltaBar
    (deltaSeq n) 0).1 at hlower
  dsimp [c, floor] at hlower ⊢
  change _ ≤ (contFrontierCriteria J n kappa cminus cplus pmin deltaBar
    (deltaSeq n) 0).1
  convert hlower using 1 <;> ring

/-- The regular and atom experiments combine into the full continuity
frontier lower bound. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
lemma contMinimaxRisk_eventually_ge_frontier
    (J : ℕ) (kappa cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : ContRegimeConstants J kappa cminus cplus pmin deltaBar alpha) :
    ∃ c : ℝ, 0 < c ∧ ∀ deltaSeq : ℕ → ℝ,
      ThresholdSequence deltaBar deltaSeq → ∀ᶠ n : ℕ in Filter.atTop,
      c * contFrontier n (deltaSeq n) kappa ≤
        (contFrontierCriteria J n kappa cminus cplus pmin deltaBar
          (deltaSeq n) alpha).1 := by
  obtain ⟨c0, hc0, h0⟩ := contMinimaxRisk_eventually_ge_root J kappa cminus
    cplus pmin deltaBar alpha hreg
  obtain ⟨c1, hc1, h1⟩ := contMinimaxRisk_eventually_ge_atom J kappa cminus
    cplus pmin deltaBar alpha hreg
  let c := min c0 c1 / 2
  refine ⟨c, by dsimp [c]; positivity, ?_⟩
  intro deltaSeq hdelta
  filter_upwards [h0 deltaSeq hdelta, h1 deltaSeq hdelta] with n hn0 hn1
  have hr0 : 0 ≤ (n : ℝ) ^ (-(1 : ℝ) / 2) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  have ha0 : 0 ≤ (deltaSeq n) ^ (kappa + 1) :=
    Real.rpow_nonneg (hdelta n).1 _
  dsimp [c, contFrontier]
  have hmin0 : min c0 c1 ≤ c0 := min_le_left _ _
  have hmin1 : min c0 c1 ≤ c1 := min_le_right _ _
  nlinarith [mul_le_mul_of_nonneg_right hmin0 hr0,
    mul_le_mul_of_nonneg_right hmin1 ha0]

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier

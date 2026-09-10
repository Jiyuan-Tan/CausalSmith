/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.HonestMixedTerm
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.UpperTotal

/-! # Eventual expected-length upper bound for the honest interval -/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open Filter MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- Exponential decay along the smallest effective-sample polynomial implied
by the balance equation dominates the root-sample scale. The result uses [the `hbeta` condition](hyp:hbeta), [the `hkappa` condition](hyp:hkappa), [the `hc` condition](hyp:hc). [This is the stated conclusion](goal).
-/
lemma exp_balanced_edge_eventually_le_root
    (beta kappa c : ℝ) (hbeta : 0 < beta) (hkappa : 0 ≤ kappa) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-c * (n : ℝ) ^ (2 * beta / (2 * beta + kappa + 1))) ≤
        (n : ℝ) ^ (-(1 : ℝ) / 2) := by
  let a : ℝ := 2 * beta / (2 * beta + kappa + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have ho :=
    (isLittleO_exp_neg_mul_rpow_atTop hc (-(1 : ℝ) / (2 * a))).eventuallyLE
  have hoc := htend.eventually ho
  filter_upwards [hoc, eventually_ge_atTop 1] with n hn hn1
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), abs_of_pos (Real.rpow_pos_of_pos (by positivity) _)] at hn
  have hnpos : 0 < (n : ℝ) := by positivity
  calc
    Real.exp (-c * (n : ℝ) ^ (2 * beta / (2 * beta + kappa + 1))) =
        Real.exp (-c * (n : ℝ) ^ a) := by rfl
    _ ≤ ((n : ℝ) ^ a) ^ (-(1 : ℝ) / (2 * a)) := hn
    _ = (n : ℝ) ^ (-(1 : ℝ) / 2) := by
      rw [← Real.rpow_mul hnpos.le]
      congr 1
      field_simp

/-- The balance equation forces the effective local sample size to grow at
least at the edge-regime polynomial rate. The result uses [the `hn` condition](hyp:hn), [the `hbeta` condition](hyp:hbeta), [the `hkappa` condition](hyp:hkappa), [the `hdelta` condition](hyp:hdelta), [the `hh` condition](hyp:hh), [the `hbalance` condition](hyp:hbalance). [This is the stated conclusion](goal).
-/
lemma balancedEffectiveSample_ge_edge
    {n : ℕ} {beta kappa delta h : ℝ}
    (hn : 0 < n) (hbeta : 0 < beta) (hkappa : 0 ≤ kappa)
    (hdelta : 0 ≤ delta) (hh : 0 < h)
    (hbalance : (n : ℝ) * h ^ (2 * beta + 1) * (delta + h) ^ kappa = 1) :
    (n : ℝ) ^ (2 * beta / (2 * beta + kappa + 1)) ≤
      (n : ℝ) * h * (delta + h) ^ kappa := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let p : ℝ := 2 * beta + 1
  have hp : 0 < p := by dsimp [p]; linarith
  have hedge := balance_root_le_edge_scale (n : ℝ) delta h p kappa
    hnR hdelta hh hp hkappa (by simpa [p] using hbalance)
  have heff := effectiveSampleSize_eq_rpow hh hbalance
  rw [heff]
  have hpw := Real.rpow_le_rpow_of_nonpos hh hedge (by linarith : -2 * beta ≤ 0)
  calc
    (n : ℝ) ^ (2 * beta / (2 * beta + kappa + 1)) =
        ((n : ℝ) ^ (-1 / (p + kappa))) ^ (-2 * beta) := by
      rw [← Real.rpow_mul hnR.le]
      congr 1
      dsimp [p]
      field_simp
      <;> ring
    _ ≤ h ^ (-2 * beta) := hpw

set_option maxHeartbeats 1200000 in
/-- Uniform eventual expected-length upper bound for the concrete bias-aware
interval, including the supremum over all laws in [the admissible regime](hyp:hreg),
[is controlled by the frontier rate](goal). -/
lemma honestInterval_worstLength_eventually_le_frontier
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (deltaSeq : ℕ → ℝ), ThresholdSequence deltaBar deltaSeq →
      ∀ Bseq : ∀ n, SplitBlocks n,
        ∀ᶠ n in atTop,
          sSup {v : ℝ | ∃ P : ClampLaw J,
            ClampModel P beta kappa L cminus cplus pmin ∧ IidSampling P n ∧
            v = ∫ z, intervalLength
              (honestInterval (Bseq n) z (ellOf beta) beta kappa L cminus cplus
                (deltaSeq n) (infoBandwidth n (deltaSeq n) beta kappa deltaBar) alpha)
              ∂iidProduct P n} ≤
            C * clampFrontier n (deltaSeq n) kappa
              (infoBandwidth n (deltaSeq n) beta kappa deltaBar) beta := by
  rcases total_gram_stabilization J beta kappa L cminus cplus pmin
    deltaBar alpha hreg with ⟨Ct, ct, hCt, hct, hlambda, hstab⟩
  have hreg' := hreg
  rcases hreg' with
    ⟨hJ, hbeta, hkappa, hL, hcminus, hcminus_le, hcplus,
      hpmin, hpmin_le, hdeltaBar, hdeltaBar1, halpha, halpha1⟩
  let t : ℝ := Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2)
  let energyC : ℝ := Real.sqrt
    (336 * (4 * (ellOf beta + 1 : ℝ) /
      lambdaStar (ellOf beta) kappa cminus cplus ^ 2) /
      (pmin * cminus / (2 * (2 : ℝ) ^ kappa)))
  let biasC : ℝ := L * (2 * Real.sqrt (ellOf beta + 1 : ℝ) /
    lambdaStar (ellOf beta) kappa cminus cplus)
  let localC : ℝ := biasC + t * energyC
  let atomK : ℝ := cplus / (kappa + 1)
  let rootCoeff : ℝ := (3 / 2 : ℝ) + 3 * t
  let radiusC : ℝ := rootCoeff * localC + atomK * localC + 3 * t + Ct
  let C : ℝ := 2 * (3 * t + (J : ℝ) * radiusC) + 1
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have henergyC : 0 ≤ energyC := Real.sqrt_nonneg _
  have hbiasC : 0 ≤ biasC := by dsimp [biasC]; positivity
  have hlocalC : 0 ≤ localC := by dsimp [localC]; positivity
  have hatomK : 0 ≤ atomK := by
    dsimp [atomK]
    exact div_nonneg (by linarith) (by linarith)
  have hrootCoeff : 0 ≤ rootCoeff := by dsimp [rootCoeff]; positivity
  have hradiusC : 0 ≤ radiusC := by dsimp [radiusC]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro deltaSeq hdelta Bseq
  have hbal := infoBandwidth_eventually_balance beta kappa deltaBar hbeta hkappa
    ⟨hdeltaBar, hdeltaBar1⟩ deltaSeq hdelta
  have hdecay := exp_balanced_edge_eventually_le_root beta kappa ct hbeta hkappa hct
  filter_upwards [hbal, hdecay, eventually_ge_atTop 8] with n hbn hdecayN hn
  let delta := deltaSeq n
  let h := infoBandwidth n delta beta kappa deltaBar
  let r0 := (n : ℝ) ^ (-(1 : ℝ) / 2)
  let d0 := delta ^ (kappa + 1)
  let a0 := d0 * h ^ beta
  let b0 := t / Real.sqrt ((Bseq n).I0.card : ℝ)
  let b1 := t / Real.sqrt ((Bseq n).I1.card : ℝ)
  have hnpos : 0 < n := by omega
  have hh : 0 < h := by simpa [h, delta] using hbn.1
  have hhbar : h ≤ 1 - deltaBar := by simpa [h, delta] using hbn.2.1
  have hh1 : h ≤ 1 := hhbar.trans (by linarith)
  have hbalance : (n : ℝ) * h ^ (2 * beta + 1) * (delta + h) ^ kappa = 1 := by
    simpa [h, delta] using hbn.2.2
  have hdeltaN : delta ∈ Set.Icc (0 : ℝ) deltaBar := hdelta n
  have hupper : delta + h ≤ 1 := by linarith [hdeltaN.2, hhbar]
  have hr0 : 0 ≤ r0 := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hd0 : 0 ≤ d0 := Real.rpow_nonneg hdeltaN.1 _
  have hhbeta : 0 ≤ h ^ beta := Real.rpow_nonneg hh.le _
  have hhbeta1 : h ^ beta ≤ 1 := by
    simpa using Real.rpow_le_one hh.le hh1 hbeta.le
  have ha0 : 0 ≤ a0 := mul_nonneg hd0 hhbeta
  have hsqrt0 : Real.sqrt ((Bseq n).I0.card : ℝ)⁻¹ ≤ 3 * r0 := by
    apply splitBlock_invSqrt_le_root (by exact_mod_cast hnpos)
    have hc := (Bseq n).card_I0
    omega
  have hsqrt1 : Real.sqrt ((Bseq n).I1.card : ℝ)⁻¹ ≤ 3 * r0 := by
    apply splitBlock_invSqrt_le_root (by exact_mod_cast hnpos)
    have hc := (Bseq n).card_I1
    omega
  have hb0 : b0 ≤ 3 * t * r0 := by
    calc
      b0 = t * Real.sqrt ((Bseq n).I0.card : ℝ)⁻¹ := by
        simp [b0, div_eq_mul_inv, Real.sqrt_inv]
      _ ≤ t * (3 * r0) := mul_le_mul_of_nonneg_left hsqrt0 ht
      _ = 3 * t * r0 := by ring
  have hb1 : b1 ≤ 3 * t * r0 := by
    calc
      b1 = t * Real.sqrt ((Bseq n).I1.card : ℝ)⁻¹ := by
        simp [b1, div_eq_mul_inv, Real.sqrt_inv]
      _ ≤ t * (3 * r0) := mul_le_mul_of_nonneg_left hsqrt1 ht
      _ = 3 * t * r0 := by ring
  have hb10 : 0 ≤ b1 := by dsimp [b1]; positivity
  have heffLower := balancedEffectiveSample_ge_edge hnpos hbeta hkappa
    hdeltaN.1 hh hbalance
  have htailExp : Ct * Real.exp (-ct * (n : ℝ) * h * (delta + h) ^ kappa) ≤
      Ct * r0 := by
    apply mul_le_mul_of_nonneg_left _ hCt.le
    calc
      Real.exp (-ct * (n : ℝ) * h * (delta + h) ^ kappa) =
          Real.exp (-ct * ((n : ℝ) * h * (delta + h) ^ kappa)) := by
        congr 1
        ring
      _ ≤ Real.exp (-ct * (n : ℝ) ^
          (2 * beta / (2 * beta + kappa + 1))) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ ≤ r0 := by simpa [r0] using hdecayN
  apply honestInterval_modelSup_le J n (Bseq n) beta kappa L cminus cplus
    pmin deltaBar alpha delta h (C * clampFrontier n delta kappa h beta) hreg
  intro P hP
  letI : IsProbabilityMeasure P.dataMeasure := hP.probability
  letI : IsProbabilityMeasure (iidProduct P n) := by unfold iidProduct; infer_instance
  have hsampling : IidSampling P n := clampModel_iidSampling hP
  have htail (x : Fin J) :
      (iidProduct P n).real {z |
        ¬ GoodGramEvent (Bseq n) z x (ellOf beta) kappa cminus cplus delta h} ≤
        Ct * r0 := by
    exact (hstab P hP n hsampling (Bseq n) delta hdeltaN x).1 |>.trans htailExp
  have hradBound (x : Fin J) :
      (∫ z, stratumRadius (Bseq n) z x (ellOf beta) beta kappa L cminus cplus
        delta h t b1 ∂iidProduct P n) ≤ radiusC * (r0 + a0) := by
    have hfac := integral_stratumRadius_le_factored P (Bseq n) x beta kappa L
      cminus cplus delta h t b1 hJ hP.probability hbeta.le hL.le hh ht hb10 hlambda
    have hatom := integral_atomEstimate_le_envelope P (Bseq n) x beta kappa L
      cminus cplus pmin deltaBar alpha delta hP hreg (by
        have hc := (Bseq n).card_I1
        omega) hdeltaN
    have henergy := integral_sqrt_interceptWeight_energy_balanced_le
      (ell := ellOf beta) P hP hsampling (Bseq n) x hn hbeta hkappa hcminus
      (by linarith [hcplus] : 0 ≤ cplus) hpmin hdeltaN.1 hh hupper hlambda hbalance
    have hfirst :
        (∫ z, atomEstimate (Bseq n) z x delta ∂iidProduct P n) + b1 ≤
          rootCoeff * r0 + atomK * d0 := by
      calc
        _ ≤ ((1 / 2 : ℝ) * Real.sqrt ((Bseq n).I1.card : ℝ)⁻¹ +
            cplus * d0 / (kappa + 1)) + 3 * t * r0 :=
          add_le_add hatom hb1
        _ = ((1 / 2 : ℝ) * Real.sqrt ((Bseq n).I1.card : ℝ)⁻¹ +
            atomK * d0) + 3 * t * r0 := by
          dsimp [atomK]
          ring
        _ ≤ rootCoeff * r0 + atomK * d0 := by
          dsimp [rootCoeff]
          nlinarith [hsqrt1]
    have hsecond :
        L * h ^ beta * (2 * Real.sqrt (ellOf beta + 1 : ℝ) /
            lambdaStar (ellOf beta) kappa cminus cplus) +
          t * (∫ z, Real.sqrt (∑ i ∈ (Bseq n).I2,
            interceptWeight (Bseq n) z x (ellOf beta) kappa cminus cplus delta h i ^ 2)
            ∂iidProduct P n) ≤ localC * h ^ beta := by
      calc
        _ ≤ biasC * h ^ beta + t * (energyC * h ^ beta) := by
          apply add_le_add
          · dsimp [biasC]; ring_nf; exact le_rfl
          · exact mul_le_mul_of_nonneg_left henergy ht
        _ = localC * h ^ beta := by dsimp [localC]; ring
    have hprod :
        ((∫ z, atomEstimate (Bseq n) z x delta ∂iidProduct P n) + b1) *
          (L * h ^ beta * (2 * Real.sqrt (ellOf beta + 1 : ℝ) /
              lambdaStar (ellOf beta) kappa cminus cplus) +
            t * (∫ z, Real.sqrt (∑ i ∈ (Bseq n).I2,
              interceptWeight (Bseq n) z x (ellOf beta) kappa cminus cplus delta h i ^ 2)
              ∂iidProduct P n)) ≤
          rootCoeff * localC * r0 + atomK * localC * a0 := by
      have hfirst0 : 0 ≤ (∫ z, atomEstimate (Bseq n) z x delta
          ∂iidProduct P n) + b1 := by
        apply add_nonneg
        · exact integral_nonneg fun _ => (atomEstimate_mem_Icc (Bseq n) _ x delta).1
        · exact hb10
      have hsecond0 : 0 ≤
          L * h ^ beta * (2 * Real.sqrt (ellOf beta + 1 : ℝ) /
              lambdaStar (ellOf beta) kappa cminus cplus) +
            t * (∫ z, Real.sqrt (∑ i ∈ (Bseq n).I2,
              interceptWeight (Bseq n) z x (ellOf beta) kappa cminus cplus delta h i ^ 2)
              ∂iidProduct P n) := by positivity
      calc
        _ ≤ (rootCoeff * r0 + atomK * d0) * (localC * h ^ beta) :=
          mul_le_mul hfirst hsecond hsecond0
            (add_nonneg (mul_nonneg hrootCoeff hr0) (mul_nonneg hatomK hd0))
        _ = rootCoeff * localC * (r0 * h ^ beta) + atomK * localC * a0 := by
          dsimp [a0]
          ring
        _ ≤ rootCoeff * localC * r0 + atomK * localC * a0 := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left
              (mul_le_of_le_one_right hr0 hhbeta1) (mul_nonneg hrootCoeff hlocalC))
            le_rfl
    calc
      _ ≤ _ := hfac
      _ ≤ (rootCoeff * localC * r0 + atomK * localC * a0) +
          3 * t * r0 + Ct * r0 := by
        exact add_le_add (add_le_add hprod hb1) (htail x)
      _ ≤ radiusC * (r0 + a0) := by
        dsimp [radiusC]
        have hJunk : 0 ≤ atomK * localC := mul_nonneg hatomK hlocalC
        have hmain0 : 0 ≤ rootCoeff * localC + 3 * t + Ct := by positivity
        nlinarith [mul_nonneg hJunk hr0,
          mul_nonneg hmain0 ha0]
  have hradInt (x : Fin J) := stratumRadius_integrable P (Bseq n) x beta kappa L
    cminus cplus delta h t b1 hP.probability hbeta.le hL.le hh ht hb10 hlambda
  have hsumInt : Integrable (fun z : Fin n → ClampObs J => ∑ x : Fin J,
      stratumRadius (Bseq n) z x (ellOf beta) beta kappa L cminus cplus
        delta h t b1) (iidProduct P n) :=
    integrable_finsetSum Finset.univ fun x _ => hradInt x
  have hradiusInt : Integrable (fun z : Fin n → ClampObs J =>
      honestRadius (Bseq n) z beta kappa L cminus cplus delta h alpha)
      (iidProduct P n) := by
    simpa [honestRadius, t, b0, b1] using (integrable_const b0).add hsumInt
  have hlenInt : Integrable (fun z : Fin n → ClampObs J => intervalLength
      (honestInterval (Bseq n) z (ellOf beta) beta kappa L cminus cplus
        delta h alpha)) (iidProduct P n) := by
    refine Integrable.of_bound
      (honestInterval_length_measurable (Bseq n) beta kappa L cminus cplus
        delta h alpha |>.aestronglyMeasurable) 1 ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    exact honestInterval_length_le_one (Bseq n) beta kappa L cminus cplus delta h alpha z
  have hlenRad :
      (∫ z, intervalLength (honestInterval (Bseq n) z (ellOf beta) beta kappa L
        cminus cplus delta h alpha) ∂iidProduct P n) ≤
      ∫ z, 2 * honestRadius (Bseq n) z beta kappa L cminus cplus delta h alpha
        ∂iidProduct P n :=
    integral_mono hlenInt (hradiusInt.const_mul 2) fun z =>
      honestInterval_length_le_two_radius J n (Bseq n) beta kappa L cminus cplus
        pmin deltaBar alpha delta h hreg (by omega) hh.le z
  calc
    _ ≤ ∫ z, 2 * honestRadius (Bseq n) z beta kappa L cminus cplus delta h alpha
        ∂iidProduct P n := hlenRad
    _ = 2 * (b0 + ∑ x : Fin J, ∫ z, stratumRadius (Bseq n) z x
          (ellOf beta) beta kappa L cminus cplus delta h t b1 ∂iidProduct P n) := by
      rw [integral_const_mul]
      change 2 * (∫ z, b0 + ∑ x : Fin J, stratumRadius (Bseq n) z x
        (ellOf beta) beta kappa L cminus cplus delta h t b1 ∂iidProduct P n) = _
      rw [integral_add (integrable_const _) hsumInt, integral_const,
        integral_finset_sum Finset.univ (fun x _ => hradInt x)]
      simp
    _ ≤ 2 * (3 * t * r0 + (J : ℝ) * (radiusC * (r0 + a0))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      calc
        b0 + ∑ x : Fin J, ∫ z, stratumRadius (Bseq n) z x
              (ellOf beta) beta kappa L cminus cplus delta h t b1 ∂iidProduct P n ≤
            3 * t * r0 + ∑ _x : Fin J, radiusC * (r0 + a0) := by
          exact add_le_add hb0 (Finset.sum_le_sum fun x _ => hradBound x)
        _ = 3 * t * r0 + (J : ℝ) * (radiusC * (r0 + a0)) := by
          simp
    _ ≤ C * (r0 + a0) := by
      dsimp [C]
      have hrsum : 0 ≤ r0 + a0 := add_nonneg hr0 ha0
      nlinarith [mul_nonneg (mul_nonneg (by positivity : 0 ≤ 3 * t) hr0) ha0]
    _ = C * clampFrontier n delta kappa h beta := by
      simp [clampFrontier, r0, d0, a0]

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier

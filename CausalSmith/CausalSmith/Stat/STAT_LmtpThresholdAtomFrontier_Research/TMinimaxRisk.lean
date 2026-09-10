/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.UpperTotal
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.MinimaxFunctional
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.MinimaxDivergence
import Causalean.Stat.Minimax.ChiSquared
import Causalean.Stat.Minimax.MinimaxRisk

/-!
# Matched minimax absolute-risk frontier

The upper bound is attached to the concrete total-Gram estimator. The lower
bound contains both same-class experiments and their product-divergence bounds.
-/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open Filter MeasureTheory Set

noncomputable section

/-- Risk of the paper's concrete stabilized estimator. -/
def stabilizedEstimatorRisk (P : ClampLaw J) (n : ℕ) (B : SplitBlocks n)
    (beta kappa cminus cplus deltaBar delta : ℝ) : ℝ :=
  estimatorRisk P n delta (fun z =>
    totalGramEstimator B z (ellOf beta) kappa cminus cplus delta
      (infoBandwidth n delta beta kappa deltaBar))

/-- Worst-case risk of the concrete estimator over i.i.d. laws in the model. -/
def stabilizedWorstRisk (J n : ℕ) (B : SplitBlocks n)
    (beta kappa L cminus cplus pmin deltaBar delta : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ P : ClampLaw J,
    ClampModel P beta kappa L cminus cplus pmin ∧ IidSampling P n ∧
    v = stabilizedEstimatorRisk P n B beta kappa cminus cplus deltaBar delta}

/-- Product chi-squared divergence used by the same-class witnesses. -/
def productChiSq (P Q : ClampLaw J) (n : ℕ) : ℝ :=
  Causalean.Stat.chiSqDiv (iidProduct P n) (iidProduct Q n)

/-- The [product law from `P`](hyp:P) is absolutely continuous with respect to
the [product law from `Q`](hyp:Q), and its squared Radon--Nikodym deviation is
integrable for the [sample size `n`](hyp:n); together these conditions define
[well-posed real product chi-squared divergence](goal). -/
def ProperProductChiSq (P Q : ClampLaw J) (n : ℕ) : Prop :=
  iidProduct P n ≪ iidProduct Q n ∧
    Integrable (fun z => (((iidProduct P n).rnDeriv
      (iidProduct Q n) z).toReal - 1) ^ 2) (iidProduct Q n)

/-- Two witness laws share the complete `(X,A)` design distribution and its
law-pinned nuisance representation. -/
def SharedClampDesign (P Q : ClampLaw J) : Prop :=
  P.dataMeasure.map (fun o => (o.X, o.A)) =
      Q.dataMeasure.map (fun o => (o.X, o.A)) ∧
  P.px = Q.px ∧ P.pi = Q.pi

/-- The outcome in a lower-bound experiment is genuinely Bernoulli. -/
def BernoulliOutcomeLaw (P : ClampLaw J) : Prop :=
  ∀ᵐ o ∂P.dataMeasure, o.Y = 0 ∨ o.Y = 1

set_option maxHeartbeats 800000 in
/-- Uniform eventual upper bound for the concrete stabilized estimator,
including the supremum over all model laws. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
lemma stabilizedWorstRisk_eventually_le_frontier
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (deltaSeq : ℕ → ℝ), ThresholdSequence deltaBar deltaSeq →
      ∀ Bseq : ∀ n, SplitBlocks n,
        ∀ᶠ n in atTop,
          stabilizedWorstRisk J n (Bseq n) beta kappa L cminus cplus pmin
              deltaBar (deltaSeq n) ≤
            C * clampFrontier n (deltaSeq n) kappa
              (infoBandwidth n (deltaSeq n) beta kappa deltaBar) beta := by
  rcases total_gram_stabilization J beta kappa L cminus cplus pmin
    deltaBar alpha hreg with ⟨Ct, ct, hCt, hct, hlambda, hstab⟩
  have hreg' := hreg
  rcases hreg' with
    ⟨hJ, hbeta, hkappa, hL, hcminus, hcminus_le, hcplus,
      hpmin, hpmin_le, hdeltaBar, hdeltaBar1, halpha, halpha1⟩
  let noiseC : ℝ := (1 / 2 : ℝ) * Real.sqrt
    (336 * (4 * (ellOf beta + 1 : ℝ) /
      lambdaStar (ellOf beta) kappa cminus cplus ^ 2) /
      (pmin * cminus / (2 * (2 : ℝ) ^ kappa)))
  let biasC : ℝ := 2 * Real.sqrt (ellOf beta + 1 : ℝ) /
    lambdaStar (ellOf beta) kappa cminus cplus
  let localK : ℝ := noiseC + biasC * L + Ct / ct
  let atomK : ℝ := cplus / (kappa + 1)
  let C : ℝ := 2 * (1 + (J : ℝ)) * (1 + atomK * localK)
  have hnoiseC : 0 ≤ noiseC := by dsimp [noiseC]; positivity
  have hbiasC : 0 ≤ biasC := by dsimp [biasC]; positivity
  have hlocalK : 0 ≤ localK := by dsimp [localK]; positivity
  have hatomK : 0 ≤ atomK := by
    dsimp [atomK]
    exact div_nonneg (by linarith) (by linarith)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro deltaSeq hdelta Bseq
  have hbal := infoBandwidth_eventually_balance beta kappa deltaBar hbeta hkappa
    ⟨hdeltaBar, hdeltaBar1⟩ deltaSeq hdelta
  filter_upwards [hbal, eventually_ge_atTop 8] with n hbn hn
  let delta := deltaSeq n
  let h := infoBandwidth n delta beta kappa deltaBar
  let r0 := (n : ℝ) ^ (-(1 : ℝ) / 2)
  let a0 := delta ^ (kappa + 1) * h ^ beta
  have hnpos : 0 < n := by omega
  have hh : 0 < h := by simpa [h, delta] using hbn.1
  have hhbar : h ≤ 1 - deltaBar := by simpa [h, delta] using hbn.2.1
  have hh1 : h ≤ 1 := hhbar.trans (by linarith)
  have hbalance : (n : ℝ) * h ^ (2 * beta + 1) * (delta + h) ^ kappa = 1 := by
    simpa [h, delta] using hbn.2.2
  have hdeltaN : delta ∈ Set.Icc (0 : ℝ) deltaBar := hdelta n
  have hupper : delta + h ≤ 1 := by linarith [hdeltaN.2, hhbar]
  have hr0 : 0 ≤ r0 := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have ha0 : 0 ≤ a0 := mul_nonneg
    (Real.rpow_nonneg hdeltaN.1 _) (Real.rpow_nonneg hh.le _)
  have hsqrt0 : Real.sqrt ((Bseq n).I0.card : ℝ)⁻¹ ≤ 3 * r0 := by
    have hm : n ≤ 8 * (Bseq n).I0.card := by
      have := (Bseq n).card_I0
      omega
    exact splitBlock_invSqrt_le_root hnpos hm
  have hsqrt1 : Real.sqrt ((Bseq n).I1.card : ℝ)⁻¹ ≤ 3 * r0 := by
    have hm : n ≤ 8 * (Bseq n).I1.card := by
      have := (Bseq n).card_I1
      omega
    exact splitBlock_invSqrt_le_root hnpos hm
  apply csSup_le
  · let P0 := minimaxClampLaw J kappa (fun _ : Fin J × ℝ => 0)
    have hP0 : ClampModel P0 beta kappa L cminus cplus pmin := by
      exact minimaxCenter_mem_model J beta kappa L cminus cplus pmin deltaBar alpha hreg
    exact ⟨stabilizedEstimatorRisk P0 n (Bseq n) beta kappa cminus cplus
        deltaBar delta, P0, hP0, clampModel_iidSampling hP0, rfl⟩
  · intro v hv
    rcases hv with ⟨P, hP, hsampling, rfl⟩
    have htail (x : Fin J) :
        (iidProduct P n).real {z |
          ¬ GoodGramEvent (Bseq n) z x (ellOf beta) kappa cminus cplus delta h} ≤
          Ct * Real.exp (-ct * (n : ℝ) * h * (delta + h) ^ kappa) := by
      simpa [h, delta] using (hstab P hP n hsampling (Bseq n) delta hdeltaN x).1
    have hexp : Ct * Real.exp (-ct * (n : ℝ) * h * (delta + h) ^ kappa) ≤
        (Ct / ct) * h ^ beta :=
      balancedGramTail_le hnpos hbeta hh hh1 hCt.le hct hbalance
    have hexpl := totalGramEstimator_risk_le_explicit P hP hreg hsampling
      (Bseq n) hn hdeltaN hh hupper hbalance hlambda htail
    have hlocal :
        (1 / 2 : ℝ) * Real.sqrt
              (336 * (4 * (ellOf beta + 1 : ℝ) /
                lambdaStar (ellOf beta) kappa cminus cplus ^ 2) /
                (pmin * cminus / (2 * (2 : ℝ) ^ kappa))) * h ^ beta +
            (2 * Real.sqrt (ellOf beta + 1 : ℝ) /
              lambdaStar (ellOf beta) kappa cminus cplus) * L * h ^ beta +
            Ct * Real.exp (-ct * (n : ℝ) * h * (delta + h) ^ kappa) ≤
          localK * h ^ beta := by
      calc
        _ ≤ noiseC * h ^ beta + biasC * L * h ^ beta + (Ct / ct) * h ^ beta := by
          exact add_le_add (add_le_add le_rfl le_rfl) hexp
        _ = localK * h ^ beta := by simp [noiseC, biasC, localK]; ring
    have hraw : stabilizedEstimatorRisk P n (Bseq n) beta kappa cminus cplus
        deltaBar delta ≤ 2 * r0 + (J : ℝ) * (2 * r0 + atomK * localK * a0) := by
      unfold stabilizedEstimatorRisk estimatorRisk
      have hatomExpr0 : 0 ≤ cplus * delta ^ (kappa + 1) / (kappa + 1) :=
        div_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hdeltaN.1 _)) (by linarith)
      calc
        _ ≤ _ := hexpl
        _ ≤ 2 * r0 + (J : ℝ) *
            (2 * r0 + (cplus * delta ^ (kappa + 1) / (kappa + 1)) *
              (localK * h ^ beta)) := by
          apply add_le_add
          · nlinarith [hsqrt0]
          · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg J)
            apply add_le_add
            · nlinarith [hsqrt1]
            · exact mul_le_mul_of_nonneg_left hlocal hatomExpr0
        _ = 2 * r0 + (J : ℝ) * (2 * r0 + atomK * localK * a0) := by
          dsimp [atomK, a0]
          ring
    calc
      stabilizedEstimatorRisk P n (Bseq n) beta kappa cminus cplus deltaBar delta ≤
          2 * r0 + (J : ℝ) * (2 * r0 + atomK * localK * a0) := hraw
      _ ≤ C * (r0 + a0) := by
        have hq : 0 ≤ atomK * localK := mul_nonneg hatomK hlocalK
        have hJ0 : 0 ≤ (J : ℝ) := Nat.cast_nonneg J
        have hqa : 0 ≤ (atomK * localK) * a0 := mul_nonneg hq ha0
        have hcoeff : (J : ℝ) ≤ 2 * (1 + (J : ℝ)) := by
          have hJ1 : (J : ℝ) ≤ 1 + (J : ℝ) := le_add_of_nonneg_left zero_le_one
          have hsum0 : 0 ≤ 1 + (J : ℝ) := by positivity
          exact hJ1.trans (by linarith)
        change 2 * r0 + (J : ℝ) * (2 * r0 + atomK * localK * a0) ≤
          (2 * (1 + (J : ℝ)) * (1 + atomK * localK)) * (r0 + a0)
        calc
          _ = 2 * (1 + (J : ℝ)) * r0 +
              (J : ℝ) * ((atomK * localK) * a0) := by ring
          _ ≤ 2 * (1 + (J : ℝ)) * r0 +
              (2 * (1 + (J : ℝ))) * ((atomK * localK) * a0) := by
            apply add_le_add_right
            exact mul_le_mul_of_nonneg_right hcoeff hqa
          _ ≤ (2 * (1 + (J : ℝ)) * (1 + atomK * localK)) *
              (r0 + a0) := by
            have hfac : 0 ≤ 2 * (1 + (J : ℝ)) := by positivity
            have hrest : 0 ≤
                (2 * (1 + (J : ℝ))) * a0 +
                  (2 * (1 + (J : ℝ))) * ((atomK * localK) * r0) :=
              add_nonneg (mul_nonneg hfac ha0)
                (mul_nonneg hfac (mul_nonneg hq hr0))
            calc
              _ ≤ 2 * (1 + (J : ℝ)) * r0 +
                    2 * (1 + (J : ℝ)) * (atomK * localK * a0) +
                  (2 * (1 + (J : ℝ)) * a0 +
                    2 * (1 + (J : ℝ)) * (atomK * localK * r0)) :=
                le_add_of_nonneg_right hrest
              _ = _ := by ring
      _ = C * clampFrontier n delta kappa h beta := by
        simp [clampFrontier, r0, a0]

/-- A global Bernoulli regression mean shift of the advertised size. -/
def GlobalBernoulliShift (P Q : ClampLaw J) (eps : ℝ) : Prop :=
  SharedClampDesign P Q ∧ BernoulliOutcomeLaw P ∧ BernoulliOutcomeLaw Q ∧
  ∀ (x : Fin J) (a : ℝ), a ∈ Set.Icc (0 : ℝ) 1 →
    Q.mu x a = P.mu x a + eps

/-- [the stated minimax constant global shift property holds](goal) for [the specified `J` input](hyp:J), [the specified `kappa` input](hyp:kappa), [the specified `eps` input](hyp:eps), [the specified `heps` input](hyp:heps). -/
lemma minimaxConstant_globalShift (J : ℕ) (kappa eps : ℝ)
    (heps : |eps| ≤ 1 / 2) :
    GlobalBernoulliShift
      (minimaxClampLaw J kappa (fun _ : Fin J × ℝ => 0))
      (minimaxClampLaw J kappa (fun _ : Fin J × ℝ => eps)) eps := by
  have hmap0 := minimaxDataMeasure_map_design J kappa
    (fun _ : Fin J × ℝ => 0) measurable_const (fun _ => by norm_num)
  have hmap1 := minimaxDataMeasure_map_design J kappa
    (fun _ : Fin J × ℝ => eps) measurable_const (fun _ => heps)
  have hshared : SharedClampDesign
      (minimaxClampLaw J kappa (fun _ : Fin J × ℝ => 0))
      (minimaxClampLaw J kappa (fun _ : Fin J × ℝ => eps)) := by
    refine ⟨?_, rfl, rfl⟩
    change (minimaxDataMeasure J kappa (fun _ : Fin J × ℝ => 0)).map
        (fun o => (o.X, o.A)) =
      (minimaxDataMeasure J kappa (fun _ : Fin J × ℝ => eps)).map
        (fun o => (o.X, o.A))
    rw [hmap0, hmap1]
  refine ⟨hshared,
    minimaxDataMeasure_ae_bernoulli J kappa
      (fun _ : Fin J × ℝ => 0) measurable_const,
    minimaxDataMeasure_ae_bernoulli J kappa
      (fun _ : Fin J × ℝ => eps) measurable_const, ?_⟩
  intro x a ha
  simp [minimaxClampLaw]

set_option maxHeartbeats 800000 in
/-- The canonical constant Bernoulli shift supplies the global root-sample
witness, uniformly over every admissible threshold sequence. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
lemma globalBernoulli_witness_eventually
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha) :
    ∀ (deltaSeq : ℕ → ℝ), ThresholdSequence deltaBar deltaSeq →
      ∀ᶠ n in atTop, ∃ P0 P1 : ClampLaw J,
        ClampModel P0 beta kappa L cminus cplus pmin ∧
        ClampModel P1 beta kappa L cminus cplus pmin ∧
        IidSampling P0 n ∧ IidSampling P1 n ∧
        GlobalBernoulliShift P0 P1 ((n : ℝ) ^ (-(1 : ℝ) / 2)) ∧
        (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 : ℝ) / 2) ≤
          |clampFunctional P1 (deltaSeq n) - clampFunctional P0 (deltaSeq n)| ∧
        ProperProductChiSq P1 P0 n ∧
        productChiSq P1 P0 n ≤ Real.exp 4 := by
  intro deltaSeq hdelta
  have hreg' := hreg
  rcases hreg' with
    ⟨hJ, hbeta, hkappa, hL, hcminus, hcminus_le, hcplus,
      hpmin, hpmin_le, hdeltaBar, hdeltaBar1, halpha, halpha1⟩
  filter_upwards [eventually_ge_atTop 5] with n hn
  have hnpos : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  let eps : ℝ := (n : ℝ) ^ (-(1 : ℝ) / 2)
  have heps0 : 0 < eps := Real.rpow_pos_of_pos hnR _
  have hepshalf : |eps| ≤ 1 / 2 := by
    rw [abs_of_pos heps0]
    have hn4Nat : 4 ≤ n := by omega
    have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn4Nat
    calc
      eps ≤ (4 : ℝ) ^ (-(1 : ℝ) / 2) := by
        dsimp [eps]
        exact Real.rpow_le_rpow_of_nonpos (by norm_num) hn4 (by norm_num)
      _ = 1 / 2 := by norm_num
  have hepslt : |eps| < 1 / 2 := by
    rw [abs_of_pos heps0]
    have hn4 : (4 : ℝ) < n := by exact_mod_cast hn
    calc
      eps < (4 : ℝ) ^ (-(1 : ℝ) / 2) := by
        dsimp [eps]
        exact Real.rpow_lt_rpow_of_neg (by norm_num) hn4 (by norm_num)
      _ = 1 / 2 := by norm_num
  let P0 := minimaxClampLaw J kappa (fun _ : Fin J × ℝ => 0)
  let P1 := minimaxClampLaw J kappa (fun _ : Fin J × ℝ => eps)
  have hP0 : ClampModel P0 beta kappa L cminus cplus pmin := by
    exact minimaxCenter_mem_model J beta kappa L cminus cplus pmin deltaBar alpha hreg
  have hP1 : ClampModel P1 beta kappa L cminus cplus pmin := by
    exact minimaxConstant_mem_model J beta kappa L cminus cplus pmin deltaBar alpha
      eps hreg hepshalf
  have hshift : GlobalBernoulliShift P0 P1 eps := by
    exact minimaxConstant_globalShift J kappa eps hepshalf
  have hdelta1 : deltaSeq n ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(hdelta n).1, (hdelta n).2.trans hdeltaBar1.le⟩
  have hsep := minimaxGlobalSeparation J kappa (deltaSeq n) eps hJ hkappa
    hdelta1 hepshalf
  have hsepAbs : |clampFunctional P1 (deltaSeq n) -
      clampFunctional P0 (deltaSeq n)| = eps := by
    rw [show P1 = minimaxClampLaw J kappa (fun _ : Fin J × ℝ => eps) by rfl,
      show P0 = minimaxClampLaw J kappa (fun _ : Fin J × ℝ => 0) by rfl,
      hsep, abs_of_pos heps0]
  have hchi : productChiSq P1 P0 n ≤ Real.exp 4 := by
    change Causalean.Stat.chiSqDiv
      (Measure.pi (fun _ : Fin n => minimaxDataMeasure J kappa
        (fun _ : Fin J × ℝ => eps)))
      (Measure.pi (fun _ : Fin n => minimaxDataMeasure J kappa
        (fun _ : Fin J × ℝ => 0))) ≤ Real.exp 4
    simpa [eps] using minimaxConstant_productChiSq_le_exp_four J n kappa hJ hkappa hn
  have hac1 := minimaxDataMeasure_ac_center J kappa hJ hkappa
    (fun _ : Fin J × ℝ => eps) measurable_const (fun _ => hepslt)
  have hint1 := minimaxDataMeasure_sq_integrable_center J kappa hJ hkappa
    (fun _ : Fin J × ℝ => eps) measurable_const (fun _ => hepslt)
  letI : IsProbabilityMeasure (minimaxDataMeasure J kappa
      (fun _ : Fin J × ℝ => eps)) :=
    minimaxDataMeasure_isProbabilityMeasure J kappa hJ hkappa _ measurable_const
      (fun _ => hepshalf)
  letI : IsProbabilityMeasure (minimaxDataMeasure J kappa
      (fun _ : Fin J × ℝ => 0)) :=
    minimaxDataMeasure_isProbabilityMeasure J kappa hJ hkappa _ measurable_const
      (fun _ => by norm_num)
  have hac : iidProduct P1 n ≪ iidProduct P0 n := by
    simpa [P0, P1, iidProduct, minimaxClampLaw] using
      Causalean.Stat.pi_iid_absolutelyContinuous _ _ hac1 n
  have hint : Integrable (fun z => (((iidProduct P1 n).rnDeriv
      (iidProduct P0 n) z).toReal - 1) ^ 2) (iidProduct P0 n) := by
    simpa [P0, P1, iidProduct, minimaxClampLaw] using
      Causalean.Stat.pi_iid_integrable_sq_dev _ _ hac1 hint1 n
  refine ⟨P0, P1, hP0, hP1, clampModel_iidSampling hP0,
    clampModel_iidSampling hP1, ?_, ?_, ⟨hac, hint⟩, hchi⟩
  · simpa [eps] using hshift
  · rw [hsepAbs]
    change (1 / 2 : ℝ) * eps ≤ eps
    nlinarith [heps0]

/-- A common-design Bernoulli perturbation localized to a width-`h` window at
the threshold, with fixed small amplitude times `h^beta` and a continuous bump
supported on `[-1,1]`. -/
def LocalizedBernoulliPerturbation (P Q : ClampLaw J)
    (beta delta h amplitude : ℝ) : Prop :=
  SharedClampDesign P Q ∧ BernoulliOutcomeLaw P ∧ BernoulliOutcomeLaw Q ∧
  0 < amplitude ∧ amplitude ≤ 1 / 4 ∧
  ∃ bump : ℝ → ℝ,
    Continuous bump ∧ bump 0 = 1 ∧
    (∀ u, 0 ≤ bump u) ∧
    (∀ u, u ∉ Set.Icc (-1 : ℝ) 1 → bump u = 0) ∧
    (∀ u ∈ Set.Icc (-1 : ℝ) 1, |bump u| ≤ 1) ∧
    ∀ (x : Fin J) (a : ℝ), a ∈ Set.Icc (0 : ℝ) 1 →
      Q.mu x a - P.mu x a = amplitude * h ^ beta * bump ((a - delta) / h)

/-- [the stated minimax bump localized perturbation property holds](goal) for [the specified `J` input](hyp:J), [the specified `beta` input](hyp:beta), [the specified `kappa` input](hyp:kappa), [the specified `delta` input](hyp:delta), [the specified `h` input](hyp:h), [the specified `amplitude` input](hyp:amplitude), [the specified `hbeta` input](hyp:hbeta), [the specified `hh` input](hyp:hh), [the specified `hh1` input](hyp:hh1), [the specified `hamp` input](hyp:hamp), [the specified `hamp_le` input](hyp:hamp_le). -/
lemma minimaxBump_localizedPerturbation
    (J : ℕ) (beta kappa delta h amplitude : ℝ)
    (hbeta : 0 < beta) (hh : 0 < h) (hh1 : h ≤ 1)
    (hamp : 0 < amplitude) (hamp_le : amplitude ≤ 1 / 4) :
    let q := fun a : ℝ => amplitude * h ^ beta *
      CausalSmith.Stat.DoseResponseMinimax.doseBump ((a - delta) / h)
    LocalizedBernoulliPerturbation
      (minimaxClampLaw J kappa (fun _ : Fin J × ℝ => 0))
      (minimaxClampLaw J kappa (fun p => q p.2)) beta delta h amplitude := by
  dsimp only
  let q := fun a : ℝ => amplitude * h ^ beta *
    CausalSmith.Stat.DoseResponseMinimax.doseBump ((a - delta) / h)
  have hqmeas : Measurable q := by dsimp [q]; fun_prop
  have hq0 (a : ℝ) : 0 ≤ q a := by
    dsimp [q]
    exact mul_nonneg (mul_nonneg hamp.le (Real.rpow_nonneg hh.le _))
      (CausalSmith.Stat.DoseResponseMinimax.doseBump_nonneg _)
  have hqle (a : ℝ) : q a ≤ 1 / 4 := by
    have hb := CausalSmith.Stat.DoseResponseMinimax.doseBump_le_one ((a - delta) / h)
    have hhpow : h ^ beta ≤ 1 := Real.rpow_le_one hh.le hh1 hbeta.le
    dsimp [q]
    calc
      amplitude * h ^ beta *
          CausalSmith.Stat.DoseResponseMinimax.doseBump ((a - delta) / h) ≤
          amplitude * h ^ beta * 1 := by gcongr
      _ ≤ amplitude * 1 := by
        simpa using mul_le_mul_of_nonneg_left hhpow hamp.le
      _ ≤ 1 / 4 := by simpa using hamp_le
  have hqbound (a : ℝ) : |q a| ≤ 1 / 2 := by
    rw [abs_of_nonneg (hq0 a)]
    linarith [hqle a]
  have hmap0 := minimaxDataMeasure_map_design J kappa
    (fun _ : Fin J × ℝ => 0) measurable_const (fun _ => by norm_num)
  have hmap1 := minimaxDataMeasure_map_design J kappa
    (fun p : Fin J × ℝ => q p.2) (hqmeas.comp measurable_snd)
      (fun p => hqbound p.2)
  have hshared : SharedClampDesign
      (minimaxClampLaw J kappa (fun _ : Fin J × ℝ => 0))
      (minimaxClampLaw J kappa (fun p => q p.2)) := by
    refine ⟨?_, rfl, rfl⟩
    change (minimaxDataMeasure J kappa (fun _ : Fin J × ℝ => 0)).map
        (fun o => (o.X, o.A)) =
      (minimaxDataMeasure J kappa (fun p : Fin J × ℝ => q p.2)).map
        (fun o => (o.X, o.A))
    rw [hmap0, hmap1]
  refine ⟨hshared,
    minimaxDataMeasure_ae_bernoulli J kappa
      (fun _ : Fin J × ℝ => 0) measurable_const,
    minimaxDataMeasure_ae_bernoulli J kappa
      (fun p : Fin J × ℝ => q p.2) (hqmeas.comp measurable_snd),
    hamp, hamp_le, ?_⟩
  refine ⟨CausalSmith.Stat.DoseResponseMinimax.doseBump, ?_,
    CausalSmith.Stat.DoseResponseMinimax.doseBump_zero,
    CausalSmith.Stat.DoseResponseMinimax.doseBump_nonneg, ?_,
    fun u hu => CausalSmith.Stat.DoseResponseMinimax.doseBump_abs_le_one u, ?_⟩
  · exact (CausalSmith.Stat.DoseResponseMinimax.doseContDiffBump.contDiff
      (n := ⊤)).continuous
  · intro u hu
    apply CausalSmith.Stat.DoseResponseMinimax.doseBump_eq_zero_of_one_le_abs
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
    rcases hu with hu | hu
    · rw [abs_of_neg (by linarith)]; linarith
    · exact hu.le.trans (le_abs_self u)
  · intro x a ha
    simp [minimaxClampLaw, q]

set_option maxHeartbeats 800000 in
/-- The fixed smooth bump supplies the localized information-bandwidth witness
with a product chi-squared bound uniform in the threshold sequence and sample size. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
lemma localizedBernoulli_witness_eventually
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha) :
    ∃ amplitude D : ℝ, 0 < amplitude ∧ amplitude ≤ 1 / 4 ∧ 0 < D ∧
      ∀ (deltaSeq : ℕ → ℝ), ThresholdSequence deltaBar deltaSeq →
      ∀ᶠ n in atTop,
        let delta := deltaSeq n
        let h := infoBandwidth n delta beta kappa deltaBar
        ∃ Q0 Q1 : ClampLaw J,
          ClampModel Q0 beta kappa L cminus cplus pmin ∧
          ClampModel Q1 beta kappa L cminus cplus pmin ∧
          IidSampling Q0 n ∧ IidSampling Q1 n ∧
          LocalizedBernoulliPerturbation Q0 Q1 beta delta h amplitude ∧
          amplitude * delta ^ (kappa + 1) * h ^ beta ≤
            |clampFunctional Q1 delta - clampFunctional Q0 delta| ∧
          ProperProductChiSq Q1 Q0 n ∧
          productChiSq Q1 Q0 n ≤ D := by
  have hreg' := hreg
  rcases hreg' with
    ⟨hJ, hbeta, hkappa, hL, hcminus, hcminus_le, hcplus,
      hpmin, hpmin_le, hdeltaBar, hdeltaBar1, halpha, halpha1⟩
  obtain ⟨amplitude, hamp, hamp_le, hamp_model⟩ :=
    exists_minimaxBump_amplitude beta L hbeta hL
  let d0 : ℝ := 8 * (kappa + 1) * amplitude ^ 2
  let D : ℝ := Real.exp d0
  have hD : 0 < D := Real.exp_pos _
  refine ⟨amplitude, D, hamp, hamp_le, hD, ?_⟩
  intro deltaSeq hdelta
  have hbal := infoBandwidth_eventually_balance beta kappa deltaBar hbeta hkappa
    ⟨hdeltaBar, hdeltaBar1⟩ deltaSeq hdelta
  filter_upwards [hbal] with n hbn
  dsimp only
  let delta := deltaSeq n
  let h := infoBandwidth n delta beta kappa deltaBar
  let q := fun a : ℝ => amplitude * h ^ beta *
    CausalSmith.Stat.DoseResponseMinimax.doseBump ((a - delta) / h)
  let Q0 := minimaxClampLaw J kappa (fun _ : Fin J × ℝ => 0)
  let Q1 := minimaxClampLaw J kappa (fun p => q p.2)
  have hh : 0 < h := by simpa [h, delta] using hbn.1
  have hhbar : h ≤ 1 - deltaBar := by simpa [h, delta] using hbn.2.1
  have hh1 : h ≤ 1 := hhbar.trans (by linarith)
  have hbalance : (n : ℝ) * h ^ (2 * beta + 1) * (delta + h) ^ kappa = 1 := by
    simpa [h, delta] using hbn.2.2
  have hdeltaN : delta ∈ Set.Icc (0 : ℝ) deltaBar := hdelta n
  have hdelta1 : delta ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hdeltaN.1, hdeltaN.2.trans hdeltaBar1.le⟩
  have hshape := hamp_model hdelta1.1 hdelta1.2 hh hh1
  have hqmeas : Measurable q := by dsimp [q]; fun_prop
  have hq0 (a : ℝ) : 0 ≤ q a := by
    dsimp [q]
    exact mul_nonneg (mul_nonneg hamp.le (Real.rpow_nonneg hh.le _))
      (CausalSmith.Stat.DoseResponseMinimax.doseBump_nonneg _)
  have hqle (a : ℝ) : q a ≤ 1 / 4 := by
    have hb := CausalSmith.Stat.DoseResponseMinimax.doseBump_le_one ((a - delta) / h)
    have hhpow : h ^ beta ≤ 1 := Real.rpow_le_one hh.le hh1 hbeta.le
    dsimp [q]
    calc
      _ ≤ amplitude * h ^ beta * 1 := by gcongr
      _ ≤ amplitude * 1 := by
        simpa using mul_le_mul_of_nonneg_left hhpow hamp.le
      _ ≤ 1 / 4 := by simpa using hamp_le
  have hqbound (a : ℝ) : |q a| ≤ 1 / 2 := by
    rw [abs_of_nonneg (hq0 a)]
    linarith [hqle a]
  have hqstrict (p : Fin J × ℝ) : |q p.2| < 1 / 2 := by
    rw [abs_of_nonneg (hq0 p.2)]
    linarith [hqle p.2]
  have hQ0 : ClampModel Q0 beta kappa L cminus cplus pmin := by
    exact minimaxCenter_mem_model J beta kappa L cminus cplus pmin deltaBar alpha hreg
  have hQ1 : ClampModel Q1 beta kappa L cminus cplus pmin := by
    apply minimaxClampModel_of_taylor J beta kappa L cminus cplus pmin
      hJ hbeta hkappa hcminus_le hcplus hpmin_le q hqmeas hqbound
    exact hshape.1
    exact hshape.2.1
    exact hshape.2.2
  have hpert : LocalizedBernoulliPerturbation Q0 Q1 beta delta h amplitude := by
    simpa [Q0, Q1, q] using minimaxBump_localizedPerturbation
      J beta kappa delta h amplitude hbeta hh hh1 hamp hamp_le
  have hsep0 := minimaxLocalSeparation J beta kappa delta h amplitude
    hJ hbeta hkappa hdelta1 hh hh1 hamp.le hamp_le
  have hsep : amplitude * delta ^ (kappa + 1) * h ^ beta ≤
      |clampFunctional Q1 delta - clampFunctional Q0 delta| := by
    have hgap0 : 0 ≤ clampFunctional Q1 delta - clampFunctional Q0 delta :=
      le_trans (mul_nonneg
        (mul_nonneg hamp.le (Real.rpow_nonneg hdelta1.1 _))
        (Real.rpow_nonneg hh.le _)) (by simpa [Q0, Q1, q] using hsep0)
    rw [abs_of_nonneg hgap0]
    simpa [Q0, Q1, q] using hsep0
  let I : ℝ := ∫ p, 4 * ((fun p : Fin J × ℝ => q p.2) p) ^ 2
    ∂minimaxDesignMeasure J kappa
  have hIle : I ≤ 8 * (kappa + 1) * amplitude ^ 2 *
      h ^ (2 * beta + 1) * (delta + h) ^ kappa := by
    simpa [I, q] using minimaxLocal_designIntegral_le J beta kappa delta h amplitude
      hJ hkappa hdelta1.1 hh hamp.le
  have hnI : (n : ℝ) * I ≤ d0 := by
    dsimp [d0]
    calc
      (n : ℝ) * I ≤ (n : ℝ) *
          (8 * (kappa + 1) * amplitude ^ 2 * h ^ (2 * beta + 1) *
            (delta + h) ^ kappa) := mul_le_mul_of_nonneg_left hIle (Nat.cast_nonneg n)
      _ = 8 * (kappa + 1) * amplitude ^ 2 := by
        calc
          _ = (8 * (kappa + 1) * amplitude ^ 2) *
              ((n : ℝ) * h ^ (2 * beta + 1) * (delta + h) ^ kappa) := by ring
          _ = _ := by rw [hbalance, mul_one]
  have hchiEq := minimaxProduct_chiSqDiv_center J n kappa hJ hkappa
    (fun p : Fin J × ℝ => q p.2) (hqmeas.comp measurable_snd) hqstrict
  change 1 + Causalean.Stat.chiSqDiv
      (Measure.pi (fun _ : Fin n => minimaxDataMeasure J kappa
        (fun p : Fin J × ℝ => q p.2)))
      (Measure.pi (fun _ : Fin n => minimaxDataMeasure J kappa
        (fun _ : Fin J × ℝ => 0))) = (1 + I) ^ n at hchiEq
  have hI0 : 0 ≤ I := integral_nonneg_of_ae (ae_of_all _ fun p => by positivity)
  have hpow : (1 + I) ^ n ≤ D := by
    calc
      (1 + I) ^ n ≤ (Real.exp I) ^ n :=
        pow_le_pow_left₀ (by linarith) (by simpa [add_comm] using Real.add_one_le_exp I) n
      _ = Real.exp ((n : ℝ) * I) := by rw [Real.exp_nat_mul]
      _ ≤ Real.exp d0 := Real.exp_le_exp.mpr hnI
      _ = D := rfl
  have hchi : productChiSq Q1 Q0 n ≤ D := by
    change Causalean.Stat.chiSqDiv
      (Measure.pi (fun _ : Fin n => minimaxDataMeasure J kappa
        (fun p : Fin J × ℝ => q p.2)))
      (Measure.pi (fun _ : Fin n => minimaxDataMeasure J kappa
        (fun _ : Fin J × ℝ => 0))) ≤ D
    linarith [hchiEq, hpow]
  have hac1 := minimaxDataMeasure_ac_center J kappa hJ hkappa
    (fun p : Fin J × ℝ => q p.2) (hqmeas.comp measurable_snd) hqstrict
  have hint1 := minimaxDataMeasure_sq_integrable_center J kappa hJ hkappa
    (fun p : Fin J × ℝ => q p.2) (hqmeas.comp measurable_snd) hqstrict
  letI : IsProbabilityMeasure (minimaxDataMeasure J kappa
      (fun p : Fin J × ℝ => q p.2)) :=
    minimaxDataMeasure_isProbabilityMeasure J kappa hJ hkappa _
      (hqmeas.comp measurable_snd) (fun p => (hqstrict p).le)
  letI : IsProbabilityMeasure (minimaxDataMeasure J kappa
      (fun _ : Fin J × ℝ => 0)) :=
    minimaxDataMeasure_isProbabilityMeasure J kappa hJ hkappa _ measurable_const
      (fun _ => by norm_num)
  have hac : iidProduct Q1 n ≪ iidProduct Q0 n := by
    simpa [Q0, Q1, iidProduct, minimaxClampLaw] using
      Causalean.Stat.pi_iid_absolutelyContinuous _ _ hac1 n
  have hint : Integrable (fun z => (((iidProduct Q1 n).rnDeriv
      (iidProduct Q0 n) z).toReal - 1) ^ 2) (iidProduct Q0 n) := by
    simpa [Q0, Q1, iidProduct, minimaxClampLaw] using
      Causalean.Stat.pi_iid_integrable_sq_dev _ _ hac1 hint1 n
  exact ⟨Q0, Q1, hQ0, hQ1, clampModel_iidSampling hQ0,
    clampModel_iidSampling hQ1, hpert, hsep, ⟨hac, hint⟩, hchi⟩

/-- A close pair with a chi-squared budget below four gives an absolute-risk
lower bound for the observed minimax problem. The result uses [the `hP0` condition](hyp:hP0), [the `hP1` condition](hyp:hP1), [the `hdelta0` condition](hyp:hdelta0), [the `hdelta1` condition](hyp:hdelta1), [the `hgap0` condition](hyp:hgap0), [the `hsep` condition](hyp:hsep), [the `hac` condition](hyp:hac), [the `hint` condition](hyp:hint), [the `hchi0` condition](hyp:hchi0), [the `hchi4` condition](hyp:hchi4), [the `hchi` condition](hyp:hchi). [This is the stated conclusion](goal).
-/
lemma observedMinimaxRisk_lower_of_two_point
    (P0 P1 : ClampLaw J) (n : ℕ)
    (beta kappa L cminus cplus pmin delta gap chi : ℝ)
    (hP0 : ClampModel P0 beta kappa L cminus cplus pmin)
    (hP1 : ClampModel P1 beta kappa L cminus cplus pmin)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) (hgap0 : 0 ≤ gap)
    (hsep : gap ≤ |clampFunctional P1 delta - clampFunctional P0 delta|)
    (hac : iidProduct P1 n ≪ iidProduct P0 n)
    (hint : Integrable (fun z => (((iidProduct P1 n).rnDeriv
      (iidProduct P0 n) z).toReal - 1) ^ 2) (iidProduct P0 n))
    (hchi0 : 0 ≤ chi) (hchi4 : chi < 4)
    (hchi : productChiSq P1 P0 n ≤ chi) :
    ((1 - (1 / 2) * Real.sqrt chi) / 4) * gap ≤
      observedMinimaxRisk J n beta kappa L cminus cplus pmin delta := by
  let outer : Set ℝ := {r : ℝ | ∃ est : Estimator n J,
    ObservedMeasurableEstimator est ∧ (∀ z, est z ∈ Set.Icc (0 : ℝ) 1) ∧
    r = sSup {v : ℝ | ∃ P : ClampLaw J,
      ClampModel P beta kappa L cminus cplus pmin ∧
      v = estimatorRisk P n delta est}}
  change _ ≤ sInf outer
  have houter : outer.Nonempty := by
    let est : Estimator n J := fun _ => 0
    refine ⟨sSup {v : ℝ | ∃ P : ClampLaw J,
      ClampModel P beta kappa L cminus cplus pmin ∧
      v = estimatorRisk P n delta est}, est, measurable_const, ?_, rfl⟩
    intro z
    exact ⟨le_rfl, by norm_num⟩
  apply le_csInf houter
  intro r hr
  rcases hr with ⟨est, hest, hestrange, rfl⟩
  let risks : Set ℝ := {v : ℝ | ∃ P : ClampLaw J,
    ClampModel P beta kappa L cminus cplus pmin ∧
    v = estimatorRisk P n delta est}
  have hrisk_le (P : ClampLaw J)
      (hP : ClampModel P beta kappa L cminus cplus pmin) :
      estimatorRisk P n delta est ≤ 1 := by
    letI : IsProbabilityMeasure P.dataMeasure := hP.probability
    letI : IsProbabilityMeasure (iidProduct P n) := by
      unfold iidProduct
      infer_instance
    have htheta := clampFunctional_mem_Icc P hP hdelta0 hdelta1
    unfold estimatorRisk
    have hfint : Integrable (fun z => |est z - clampFunctional P delta|)
        (iidProduct P n) := by
      refine Integrable.of_bound ((hest.sub measurable_const).abs.aestronglyMeasurable) 1 ?_
      filter_upwards with z
      rw [Real.norm_eq_abs, abs_abs, abs_le]
      constructor <;> linarith [(hestrange z).1, (hestrange z).2,
        htheta.1, htheta.2]
    calc
      (∫ z, |est z - clampFunctional P delta| ∂iidProduct P n) ≤
          ∫ _z, (1 : ℝ) ∂iidProduct P n := by
        apply integral_mono_ae hfint (integrable_const 1)
        exact ae_of_all _ fun z => by
            rw [abs_le]
            constructor <;> linarith [(hestrange z).1, (hestrange z).2,
              htheta.1, htheta.2]
      (∫ _z, (1 : ℝ) ∂iidProduct P n) = 1 := by simp
  have hbdd : BddAbove risks := by
    refine ⟨1, ?_⟩
    intro v hv
    rcases hv with ⟨P, hP, rfl⟩
    exact hrisk_le P hP
  have hle0 : estimatorRisk P0 n delta est ≤ sSup risks := by
    apply le_csSup hbdd
    exact ⟨P0, hP0, rfl⟩
  have hle1 : estimatorRisk P1 n delta est ≤ sSup risks := by
    apply le_csSup hbdd
    exact ⟨P1, hP1, rfl⟩
  letI : IsProbabilityMeasure P0.dataMeasure := hP0.probability
  letI : IsProbabilityMeasure P1.dataMeasure := hP1.probability
  letI : IsProbabilityMeasure (iidProduct P0 n) := by
    unfold iidProduct
    infer_instance
  letI : IsProbabilityMeasure (iidProduct P1 n) := by
    unfold iidProduct
    infer_instance
  have htest := Causalean.Stat.two_point_lower_bound_of_chiSqDiv_le
    (P₀ := iidProduct P1 n) (P₁ := iidProduct P0 n) hest
    (θ₀ := clampFunctional P1 delta) (θ₁ := clampFunctional P0 delta)
    (s := gap / 2) (c := chi) (by convert hsep using 1 <;> ring) hac hint hchi
  have hfloor : 0 < (1 - (1 / 2) * Real.sqrt chi) / 2 := by
    have hsqrt : Real.sqrt chi < 2 := by
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
      convert hchi4 using 1 <;> norm_num
    linarith
  have hint0 : Integrable (fun z => |est z - clampFunctional P0 delta|)
      (iidProduct P0 n) := by
    refine Integrable.of_bound ((hest.sub measurable_const).abs.aestronglyMeasurable) 1 ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_abs]
    have ht := clampFunctional_mem_Icc P0 hP0 hdelta0 hdelta1
    rw [abs_le]
    constructor <;> linarith [(hestrange z).1, (hestrange z).2, ht.1, ht.2]
  have hint1 : Integrable (fun z => |est z - clampFunctional P1 delta|)
      (iidProduct P1 n) := by
    refine Integrable.of_bound ((hest.sub measurable_const).abs.aestronglyMeasurable) 1 ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_abs]
    have ht := clampFunctional_mem_Icc P1 hP1 hdelta0 hdelta1
    rw [abs_le]
    constructor <;> linarith [(hestrange z).1, (hestrange z).2, ht.1, ht.2]
  have hevent0 := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ fun z => abs_nonneg (est z - clampFunctional P1 delta)) hint1 (gap / 2)
  have hevent1 := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ fun z => abs_nonneg (est z - clampFunctional P0 delta)) hint0 (gap / 2)
  have hmaxEvent : ((1 - (1 / 2) * Real.sqrt chi) / 2) * (gap / 2) ≤
      max (estimatorRisk P1 n delta est) (estimatorRisk P0 n delta est) := by
    unfold estimatorRisk
    have hg2 : 0 ≤ gap / 2 := by positivity
    calc
      _ ≤ (gap / 2) * max
          ((iidProduct P1 n).real {z | gap / 2 ≤
            |est z - clampFunctional P1 delta|})
          ((iidProduct P0 n).real {z | gap / 2 ≤
            |est z - clampFunctional P0 delta|}) := by
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_left htest hg2
      _ = max ((gap / 2) * (iidProduct P1 n).real {z | gap / 2 ≤
            |est z - clampFunctional P1 delta|})
          ((gap / 2) * (iidProduct P0 n).real {z | gap / 2 ≤
            |est z - clampFunctional P0 delta|}) := by
              rw [mul_max_of_nonneg _ _ hg2]
      _ ≤ _ := max_le_max hevent0 hevent1
  calc
    ((1 - (1 / 2) * Real.sqrt chi) / 4) * gap =
        ((1 - (1 / 2) * Real.sqrt chi) / 2) * (gap / 2) := by ring
    _ ≤ max (estimatorRisk P1 n delta est) (estimatorRisk P0 n delta est) := hmaxEvent
    _ ≤ sSup risks := max_le hle1 hle0

/-- A quarter-strength constant Bernoulli shift gives the parametric component
of the minimax lower bound while keeping chi-squared below four. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
lemma observedMinimaxRisk_eventually_ge_root
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha) :
    ∃ c : ℝ, 0 < c ∧ ∀ (deltaSeq : ℕ → ℝ),
      ThresholdSequence deltaBar deltaSeq →
      ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ (-(1 : ℝ) / 2) ≤
        observedMinimaxRisk J n beta kappa L cminus cplus pmin (deltaSeq n) := by
  rcases hreg with ⟨hJ, hbeta, hkappa, hL, hcminus, hcminus_le, hcplus,
    hpmin, hpmin_le, hdeltaBar, hdeltaBar1, halpha, halpha1⟩
  let chi : ℝ := Real.exp (1 / 4 : ℝ) - 1
  let floor : ℝ := (1 - (1 / 2) * Real.sqrt chi) / 4
  let c : ℝ := floor / 4
  have hchi0 : 0 ≤ chi := by
    dsimp [chi]
    exact sub_nonneg.mpr (Real.one_le_exp (by norm_num))
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
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  let root : ℝ := (n : ℝ) ^ (-(1 : ℝ) / 2)
  let eps : ℝ := (1 / 4 : ℝ) * root
  have hroot : 0 < root := Real.rpow_pos_of_pos hnR _
  have heps : 0 < eps := mul_pos (by norm_num) hroot
  have hepsq : eps ≤ 1 / 4 := by
    have hroot1 : root ≤ 1 := by
      rw [show (1 : ℝ) = 1 ^ (-(1 : ℝ) / 2) by norm_num]
      exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hn) (by norm_num)
    dsimp [eps]
    nlinarith
  have hepsb : |eps| ≤ 1 / 2 := by rw [abs_of_pos heps]; linarith
  let P0 := minimaxClampLaw J kappa (fun _ : Fin J × ℝ => 0)
  let P1 := minimaxClampLaw J kappa (fun _ : Fin J × ℝ => eps)
  have hP0 : ClampModel P0 beta kappa L cminus cplus pmin :=
    minimaxCenter_mem_model J beta kappa L cminus cplus pmin deltaBar alpha
      ⟨hJ, hbeta, hkappa, hL, hcminus, hcminus_le, hcplus,
        hpmin, hpmin_le, hdeltaBar, hdeltaBar1, halpha, halpha1⟩
  have hP1 : ClampModel P1 beta kappa L cminus cplus pmin :=
    minimaxConstant_mem_model J beta kappa L cminus cplus pmin deltaBar alpha eps
      ⟨hJ, hbeta, hkappa, hL, hcminus, hcminus_le, hcplus,
        hpmin, hpmin_le, hdeltaBar, hdeltaBar1, halpha, halpha1⟩ hepsb
  have hdelta1 : deltaSeq n ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(hdelta n).1, (hdelta n).2.trans hdeltaBar1.le⟩
  have hsepEq := minimaxGlobalSeparation J kappa (deltaSeq n) eps hJ hkappa
    hdelta1 hepsb
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
  have hepsSq : eps ^ 2 = (1 / 16 : ℝ) * (n : ℝ)⁻¹ := by
    dsimp [eps]
    rw [mul_pow, hrootSq]
    norm_num
  letI : IsProbabilityMeasure (minimaxDesignMeasure J kappa) :=
    minimaxDesignMeasure_isProbabilityMeasure J kappa hJ hkappa
  have hintEq : (∫ p, 4 * ((fun _ : Fin J × ℝ => eps) p) ^ 2
      ∂minimaxDesignMeasure J kappa) = 4 * eps ^ 2 := by simp
  have hchiEq := minimaxProduct_chiSqDiv_center J n kappa hJ hkappa
    (fun _ : Fin J × ℝ => eps) measurable_const (fun _ => by
      rw [abs_of_pos heps]; linarith [hepsq])
  rw [hintEq] at hchiEq
  have hnE : (n : ℝ) * (4 * eps ^ 2) = 1 / 4 := by
    rw [hepsSq]
    field_simp [hnR.ne']
    ring
  have hpow : (1 + 4 * eps ^ 2) ^ n ≤ Real.exp (1 / 4 : ℝ) := by
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
    dsimp [chi]
    linarith [hchiEq, hpow]
  have hac1 := minimaxDataMeasure_ac_center J kappa hJ hkappa
    (fun _ : Fin J × ℝ => eps) measurable_const (fun _ => by
      rw [abs_of_pos heps]; linarith [hepsq])
  have hint1 := minimaxDataMeasure_sq_integrable_center J kappa hJ hkappa
    (fun _ : Fin J × ℝ => eps) measurable_const (fun _ => by
      rw [abs_of_pos heps]; linarith [hepsq])
  letI : IsProbabilityMeasure (minimaxDataMeasure J kappa
      (fun _ : Fin J × ℝ => eps)) :=
    minimaxDataMeasure_isProbabilityMeasure J kappa hJ hkappa _ measurable_const
      (fun _ => hepsb)
  letI : IsProbabilityMeasure (minimaxDataMeasure J kappa
      (fun _ : Fin J × ℝ => 0)) :=
    minimaxDataMeasure_isProbabilityMeasure J kappa hJ hkappa _ measurable_const
      (fun _ => by norm_num)
  have hac := Causalean.Stat.pi_iid_absolutelyContinuous _ _ hac1 n
  have hint := Causalean.Stat.pi_iid_integrable_sq_dev _ _ hac1 hint1 n
  have hlower := observedMinimaxRisk_lower_of_two_point P0 P1 n beta kappa L
    cminus cplus pmin (deltaSeq n) eps chi hP0 hP1 hdelta1.1 hdelta1.2
    heps.le hsep (by simpa [P0, P1, iidProduct, minimaxClampLaw] using hac)
    (by simpa [P0, P1, iidProduct, minimaxClampLaw] using hint) hchi0 hchi4 hchi
  dsimp [c, floor, eps, root] at hlower ⊢
  convert hlower using 1 <;> ring

set_option maxHeartbeats 800000 in
/-- A fixed contraction of the information bandwidth makes the localized
experiment close while preserving the local frontier order. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
lemma observedMinimaxRisk_eventually_ge_local
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha) :
    ∃ c : ℝ, 0 < c ∧ ∀ deltaSeq : ℕ → ℝ,
      ThresholdSequence deltaBar deltaSeq → ∀ᶠ n : ℕ in atTop,
      let h := infoBandwidth n (deltaSeq n) beta kappa deltaBar
      c * (deltaSeq n) ^ (kappa + 1) * h ^ beta ≤
        observedMinimaxRisk J n beta kappa L cminus cplus pmin (deltaSeq n) := by
  have hr := hreg
  rcases hr with ⟨hJ, hbeta, hkappa, hL, hcminus, hcminus_le, hcplus,
    hpmin, hpmin_le, hdeltaBar, hdeltaBar1, halpha, halpha1⟩
  obtain ⟨amplitude, hamp, hamp_le, hamp_model⟩ :=
    exists_minimaxBump_amplitude beta L hbeta hL
  let d0 : ℝ := 8 * (kappa + 1) * amplitude ^ 2
  let p : ℝ := 2 * beta + 1
  let t : ℝ := Real.exp (-(d0 + 1) / p)
  let chi : ℝ := Real.exp 1 - 1
  let floor : ℝ := (1 - (1 / 2) * Real.sqrt chi) / 4
  let c : ℝ := floor * amplitude * t ^ beta
  have hd0 : 0 ≤ d0 := by dsimp [d0]; positivity
  have hp : 0 < p := by dsimp [p]; linarith
  have ht : 0 < t := Real.exp_pos _
  have ht1 : t ≤ 1 := by
    dsimp [t]
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by linarith)) hp.le
  have htp : t ^ p = Real.exp (-(d0 + 1)) := by
    dsimp [t]
    rw [← Real.exp_mul]
    congr 1
    field_simp [hp.ne']
  have hdsmall : d0 * t ^ p ≤ 1 := by
    rw [htp]
    have hdexp : d0 ≤ Real.exp d0 := by
      exact (Real.add_one_le_exp d0).trans' (by linarith)
    calc
      d0 * Real.exp (-(d0 + 1)) ≤ Real.exp d0 * Real.exp (-(d0 + 1)) :=
        mul_le_mul_of_nonneg_right hdexp (Real.exp_pos _).le
      _ = Real.exp (-1) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hchi0 : 0 ≤ chi := by dsimp [chi]; exact sub_nonneg.mpr (Real.one_le_exp zero_le_one)
  have hchi4 : chi < 4 := by dsimp [chi]; linarith [Real.exp_one_lt_three]
  have hfloor : 0 < floor := by
    dsimp [floor]
    have hs : Real.sqrt chi < 2 := by
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
      convert hchi4 using 1 <;> norm_num
    linarith
  refine ⟨c, by dsimp [c]; positivity, ?_⟩
  intro deltaSeq hdelta
  have hbal := infoBandwidth_eventually_balance beta kappa deltaBar hbeta hkappa
    ⟨hdeltaBar, hdeltaBar1⟩ deltaSeq hdelta
  filter_upwards [hbal] with n hbn
  dsimp only
  let delta := deltaSeq n
  let h := infoBandwidth n delta beta kappa deltaBar
  let hs := t * h
  let q := fun a : ℝ => amplitude * hs ^ beta *
    CausalSmith.Stat.DoseResponseMinimax.doseBump ((a - delta) / hs)
  let P0 := minimaxClampLaw J kappa (fun _ : Fin J × ℝ => 0)
  let P1 := minimaxClampLaw J kappa (fun z => q z.2)
  have hh : 0 < h := hbn.1
  have hh1 : h ≤ 1 := hbn.2.1.trans (by linarith)
  have hhs : 0 < hs := mul_pos ht hh
  have hhs1 : hs ≤ 1 := (mul_le_of_le_one_left hh.le ht1).trans hh1
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
    have hb := CausalSmith.Stat.DoseResponseMinimax.doseBump_le_one ((a-delta)/hs)
    have hpw := Real.rpow_le_one hhs.le hhs1 hbeta.le
    dsimp [q]
    calc
      _ ≤ amplitude * hs ^ beta := by nlinarith [mul_nonneg hamp.le (Real.rpow_nonneg hhs.le beta)]
      _ ≤ amplitude := by simpa using mul_le_mul_of_nonneg_left hpw hamp.le
      _ ≤ 1 / 2 := by linarith
  have hqstrict (z : Fin J × ℝ) : |q z.2| < 1 / 2 := by
    rw [abs_of_nonneg (hq0 z.2)]
    have hb := CausalSmith.Stat.DoseResponseMinimax.doseBump_le_one ((z.2-delta)/hs)
    have hpw := Real.rpow_le_one hhs.le hhs1 hbeta.le
    have : q z.2 ≤ amplitude := by
      dsimp [q]
      calc
        _ ≤ amplitude * hs ^ beta := by
          nlinarith [mul_nonneg hamp.le (Real.rpow_nonneg hhs.le beta)]
        _ ≤ amplitude := by simpa using mul_le_mul_of_nonneg_left hpw hamp.le
    linarith [hamp_le]
  have hP0 := minimaxCenter_mem_model J beta kappa L cminus cplus pmin deltaBar alpha hreg
  have hP1 : ClampModel P1 beta kappa L cminus cplus pmin := by
    apply minimaxClampModel_of_taylor J beta kappa L cminus cplus pmin
      hJ hbeta hkappa hcminus_le hcplus hpmin_le q hqmeas hqbound
    exact hshape.1
    exact hshape.2.1
    exact hshape.2.2
  have hsep0 := minimaxLocalSeparation J beta kappa delta hs amplitude
    hJ hbeta hkappa hd hhs hhs1 hamp.le hamp_le
  have hsep : amplitude * delta ^ (kappa + 1) * hs ^ beta ≤
      |clampFunctional P1 delta - clampFunctional P0 delta| := by
    have hn : 0 ≤ clampFunctional P1 delta - clampFunctional P0 delta :=
      (mul_nonneg (mul_nonneg hamp.le (Real.rpow_nonneg hd.1 _))
        (Real.rpow_nonneg hhs.le _)).trans (by simpa [P0, P1, q] using hsep0)
    rw [abs_of_nonneg hn]
    simpa [P0, P1, q] using hsep0
  let I := ∫ z, 4 * ((fun z : Fin J × ℝ => q z.2) z)^2 ∂minimaxDesignMeasure J kappa
  have hI := minimaxLocal_designIntegral_le J beta kappa delta hs amplitude
    hJ hkappa hd.1 hhs hamp.le
  have hnI : (n : ℝ) * I ≤ 1 := by
    have hw : delta + hs ≤ delta + h := by dsimp [hs]; nlinarith [mul_le_of_le_one_left hh.le ht1]
    have hpoww := Real.rpow_le_rpow (add_nonneg hd.1 hhs.le) hw hkappa
    have hb := hbn.2.2
    calc
      _ ≤ (n : ℝ) * (8*(kappa+1)*amplitude^2*hs^(2*beta+1)*(delta+hs)^kappa) :=
        mul_le_mul_of_nonneg_left (by simpa [I, q] using hI) (Nat.cast_nonneg n)
      _ ≤ d0 * t ^ p * ((n:ℝ)*h^(2*beta+1)*(delta+h)^kappa) := by
        dsimp [d0, p, hs]
        rw [Real.mul_rpow ht.le hh.le]
        ring_nf
        gcongr
      _ = d0 * t ^ p := by rw [hb, mul_one]
      _ ≤ 1 := hdsmall
  have hchiEq := minimaxProduct_chiSqDiv_center J n kappa hJ hkappa
    (fun z : Fin J × ℝ => q z.2) (hqmeas.comp measurable_snd) hqstrict
  have hpow : (1 + I)^n ≤ Real.exp 1 := by
    calc
      _ ≤ (Real.exp I)^n := pow_le_pow_left₀ (by positivity)
        (by simpa [add_comm] using Real.add_one_le_exp I) n
      _ = Real.exp ((n:ℝ)*I) := by rw [Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr hnI
  have hchi : productChiSq P1 P0 n ≤ chi := by
    change Causalean.Stat.chiSqDiv _ _ ≤ chi
    dsimp [chi, P0, P1, iidProduct, minimaxClampLaw]
    change Causalean.Stat.chiSqDiv _ _ ≤ Real.exp 1 - 1
    change 1 + Causalean.Stat.chiSqDiv _ _ = (1+I)^n at hchiEq
    linarith
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
  letI : IsProbabilityMeasure (minimaxDataMeasure J kappa (fun z : Fin J×ℝ => q z.2)) :=
    minimaxDataMeasure_isProbabilityMeasure J kappa hJ hkappa _
      (hqmeas.comp measurable_snd) (fun z => hqstrict z |>.le)
  letI : IsProbabilityMeasure (minimaxDataMeasure J kappa (fun _ : Fin J×ℝ => 0)) :=
    minimaxDataMeasure_isProbabilityMeasure J kappa hJ hkappa _ measurable_const (fun _ => by norm_num)
  have hl := observedMinimaxRisk_lower_of_two_point P0 P1 n beta kappa L cminus cplus
    pmin delta (amplitude*delta^(kappa+1)*hs^beta) chi hP0 hP1 hd.1 hd.2
    (mul_nonneg (mul_nonneg hamp.le (Real.rpow_nonneg hd.1 _))
      (Real.rpow_nonneg hhs.le _)) hsep
    (by simpa [P0,P1,iidProduct,minimaxClampLaw] using
      Causalean.Stat.pi_iid_absolutelyContinuous _ _ hac1 n)
    (by simpa [P0,P1,iidProduct,minimaxClampLaw] using
      Causalean.Stat.pi_iid_integrable_sq_dev _ _ hac1 hint1 n)
    hchi0 hchi4 hchi
  dsimp [c, floor, hs]
  rw [Real.mul_rpow ht.le hh.le] at hl
  convert hl using 1 <;> ring

/-- The concrete stabilized estimator is an admissible competitor in the
observed minimax problem. The result uses [the `hreg` condition](hyp:hreg), [the `hdelta` condition](hyp:hdelta). [This is the stated conclusion](goal).
-/
lemma observedMinimaxRisk_le_stabilizedWorstRisk
    (J n : ℕ) (B : SplitBlocks n)
    (beta kappa L cminus cplus pmin deltaBar alpha delta : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) 1) :
    observedMinimaxRisk J n beta kappa L cminus cplus pmin delta ≤
      stabilizedWorstRisk J n B beta kappa L cminus cplus pmin deltaBar delta := by
  let est : Estimator n J := fun z =>
    totalGramEstimator B z (ellOf beta) kappa cminus cplus delta
      (infoBandwidth n delta beta kappa deltaBar)
  let outer : Set ℝ := {r : ℝ | ∃ e : Estimator n J,
    ObservedMeasurableEstimator e ∧ (∀ z, e z ∈ Set.Icc (0 : ℝ) 1) ∧
    r = sSup {v : ℝ | ∃ P : ClampLaw J,
      ClampModel P beta kappa L cminus cplus pmin ∧
      v = estimatorRisk P n delta e}}
  change sInf outer ≤ _
  have houterBelow : BddBelow outer := by
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with ⟨e, hemeas, herange, rfl⟩
    let risks : Set ℝ := {v : ℝ | ∃ P : ClampLaw J,
      ClampModel P beta kappa L cminus cplus pmin ∧
      v = estimatorRisk P n delta e}
    have hrisk_le (P : ClampLaw J)
        (hP : ClampModel P beta kappa L cminus cplus pmin) :
        estimatorRisk P n delta e ≤ 1 := by
      letI : IsProbabilityMeasure P.dataMeasure := hP.probability
      letI : IsProbabilityMeasure (iidProduct P n) := by
        unfold iidProduct
        infer_instance
      have htheta := clampFunctional_mem_Icc P hP hdelta.1 hdelta.2
      unfold estimatorRisk
      calc
        (∫ z, |e z - clampFunctional P delta| ∂iidProduct P n) ≤
            ∫ _z, (1 : ℝ) ∂iidProduct P n := by
          apply integral_mono_ae
          · exact Integrable.of_bound
              ((hemeas.sub measurable_const).abs.aestronglyMeasurable) 1
              (ae_of_all _ fun z => by
                rw [Real.norm_eq_abs, abs_abs, abs_le]
                constructor <;> linarith [(herange z).1, (herange z).2,
                  htheta.1, htheta.2])
          · exact integrable_const 1
          · exact ae_of_all _ fun z => by
              rw [abs_le]
              constructor <;> linarith [(herange z).1, (herange z).2,
                htheta.1, htheta.2]
        _ = 1 := by simp
    have hbdd : BddAbove risks := by
      refine ⟨1, ?_⟩
      rintro v ⟨P, hP, rfl⟩
      exact hrisk_le P hP
    let P0 := minimaxClampLaw J kappa (fun _ : Fin J × ℝ => 0)
    have hP0 : ClampModel P0 beta kappa L cminus cplus pmin :=
      minimaxCenter_mem_model J beta kappa L cminus cplus pmin deltaBar alpha hreg
    have hrisk0 : 0 ≤ estimatorRisk P0 n delta e := by
      unfold estimatorRisk
      exact integral_nonneg_of_ae (ae_of_all _ fun z => abs_nonneg _)
    exact hrisk0.trans (le_csSup hbdd ⟨P0, hP0, rfl⟩)
  apply csInf_le houterBelow
  refine ⟨est, ?_, ?_, ?_⟩
  · exact totalGramEstimator_measurable B kappa cminus cplus delta _
  · intro z
    exact clampUnit_mem_Icc _
  · unfold stabilizedWorstRisk
    congr 1
    ext v
    constructor
    · rintro ⟨P, hP, hsample, hv⟩
      refine ⟨P, hP, ?_⟩
      simpa [stabilizedEstimatorRisk, est] using hv
    · rintro ⟨P, hP, hv⟩
      refine ⟨P, hP, clampModel_iidSampling hP, ?_⟩
      simpa [stabilizedEstimatorRisk, est] using hv

/-- The minimax risk and concrete estimator risk are both comparable to the
regular-plus-atom frontier, with explicit global and localized witnesses. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
-- @node: thm:minimax-risk
theorem clamp_minimax_risk
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha) :
    ∃ c C amplitude : ℝ, 0 < c ∧ c < C ∧
    0 < amplitude ∧ amplitude ≤ 1 / 4 ∧
    ∀ (deltaSeq : ℕ → ℝ), ThresholdSequence deltaBar deltaSeq →
    ∀ Bseq : ∀ n, SplitBlocks n,
      ∀ᶠ n in atTop,
        let delta := deltaSeq n
        let h := infoBandwidth n delta beta kappa deltaBar
        let r := clampFrontier n delta kappa h beta
        c * r ≤ observedMinimaxRisk J n beta kappa L cminus cplus pmin delta ∧
        observedMinimaxRisk J n beta kappa L cminus cplus pmin delta ≤
          stabilizedWorstRisk J n (Bseq n) beta kappa L cminus cplus pmin
            deltaBar delta ∧
        stabilizedWorstRisk J n (Bseq n) beta kappa L cminus cplus pmin
            deltaBar delta ≤ C * r ∧
        (∃ P0 P1 : ClampLaw J,
          ClampModel P0 beta kappa L cminus cplus pmin ∧
          ClampModel P1 beta kappa L cminus cplus pmin ∧
          IidSampling P0 n ∧ IidSampling P1 n ∧
          GlobalBernoulliShift P0 P1 ((n : ℝ) ^ (-(1 : ℝ) / 2)) ∧
          c * (n : ℝ) ^ (-(1 : ℝ) / 2) ≤
            |clampFunctional P1 delta - clampFunctional P0 delta| ∧
          ProperProductChiSq P1 P0 n ∧
          productChiSq P1 P0 n ≤ C) ∧
        (∃ Q0 Q1 : ClampLaw J,
          ClampModel Q0 beta kappa L cminus cplus pmin ∧
          ClampModel Q1 beta kappa L cminus cplus pmin ∧
          IidSampling Q0 n ∧ IidSampling Q1 n ∧
          LocalizedBernoulliPerturbation Q0 Q1 beta delta h amplitude ∧
          c * delta ^ (kappa + 1) * h ^ beta ≤
            |clampFunctional Q1 delta - clampFunctional Q0 delta| ∧
          ProperProductChiSq Q1 Q0 n ∧
          productChiSq Q1 Q0 n ≤ C) := by
  have hreg' := hreg
  rcases hreg' with ⟨hJ, hbeta, hkappa, hL, hcminus, hcminus_le, hcplus,
    hpmin, hpmin_le, hdeltaBar, hdeltaBar1, halpha, halpha1⟩
  rcases stabilizedWorstRisk_eventually_le_frontier J beta kappa L cminus cplus
    pmin deltaBar alpha hreg with ⟨Cupper, hCupper, hupper⟩
  rcases observedMinimaxRisk_eventually_ge_root J beta kappa L cminus cplus
    pmin deltaBar alpha hreg with ⟨croot, hcroot, hroot⟩
  rcases observedMinimaxRisk_eventually_ge_local J beta kappa L cminus cplus
    pmin deltaBar alpha hreg with ⟨clocal, hclocal, hlocal⟩
  rcases localizedBernoulli_witness_eventually J beta kappa L cminus cplus
    pmin deltaBar alpha hreg with ⟨amplitude, D, hamp, hamp_le, hD, hwitnessLocal⟩
  let core : ℝ := min croot (min clocal (min (1 / 2 : ℝ) amplitude))
  let c : ℝ := core / 2
  let C : ℝ := Cupper + D + Real.exp 4 + c + 1
  have hcore : 0 < core := by
    dsimp [core]
    exact lt_min hcroot (lt_min hclocal (lt_min (by norm_num) hamp))
  have hc : 0 < c := div_pos hcore (by norm_num)
  have h2c_root : 2 * c ≤ croot := by
    dsimp [c, core]
    nlinarith [min_le_left croot (min clocal (min (1 / 2 : ℝ) amplitude))]
  have h2c_local : 2 * c ≤ clocal := by
    dsimp [c, core]
    have hm := min_le_right croot (min clocal (min (1 / 2 : ℝ) amplitude))
    have hm' := min_le_left clocal (min (1 / 2 : ℝ) amplitude)
    linarith
  have hc_half : c ≤ 1 / 2 := by
    dsimp [c, core]
    have hm := min_le_right croot (min clocal (min (1 / 2 : ℝ) amplitude))
    have hm' := min_le_right clocal (min (1 / 2 : ℝ) amplitude)
    have hm'' := min_le_left (1 / 2 : ℝ) amplitude
    linarith
  have hc_amp : c ≤ amplitude := by
    dsimp [c, core]
    have hm := min_le_right croot (min clocal (min (1 / 2 : ℝ) amplitude))
    have hm' := min_le_right clocal (min (1 / 2 : ℝ) amplitude)
    have hm'' := min_le_right (1 / 2 : ℝ) amplitude
    linarith
  have hC : 0 < C := by dsimp [C]; positivity
  have hcC : c < C := by
    dsimp [C]
    nlinarith [hCupper, hD, Real.exp_pos 4]
  have hCupperC : Cupper ≤ C := by
    dsimp [C]
    nlinarith [hD, Real.exp_pos 4, hc]
  have hDC : D ≤ C := by
    dsimp [C]
    nlinarith [hCupper, Real.exp_pos 4, hc]
  have hexpC : Real.exp 4 ≤ C := by
    dsimp [C]
    nlinarith [hCupper, hD, hc]
  refine ⟨c, C, amplitude, hc, hcC, hamp, hamp_le, ?_⟩
  intro deltaSeq hdelta Bseq
  have heu := hupper deltaSeq hdelta Bseq
  have her := hroot deltaSeq hdelta
  have hel := hlocal deltaSeq hdelta
  have heg := globalBernoulli_witness_eventually J beta kappa L cminus cplus
    pmin deltaBar alpha hreg deltaSeq hdelta
  have hew := hwitnessLocal deltaSeq hdelta
  have heb := infoBandwidth_eventually_balance beta kappa deltaBar hbeta hkappa
    ⟨hdeltaBar, hdeltaBar1⟩ deltaSeq hdelta
  filter_upwards [heu, her, hel, heg, hew, heb] with n hun hrn hln hgn hwn hbn
  dsimp only
  let delta := deltaSeq n
  let h := infoBandwidth n delta beta kappa deltaBar
  let r0 : ℝ := (n : ℝ) ^ (-(1 : ℝ) / 2)
  let a0 : ℝ := delta ^ (kappa + 1) * h ^ beta
  have hdelta1 : delta ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(hdelta n).1, (hdelta n).2.trans hdeltaBar1.le⟩
  have hr0 : 0 ≤ r0 := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have ha0 : 0 ≤ a0 := mul_nonneg
    (Real.rpow_nonneg (hdelta n).1 _)
    (Real.rpow_nonneg (by simpa [h, delta] using hbn.1.le) _)
  have hlower : c * (r0 + a0) ≤
      observedMinimaxRisk J n beta kappa L cminus cplus pmin delta := by
    have hprod0 : 0 ≤ (croot - 2 * c) * r0 :=
      mul_nonneg (sub_nonneg.mpr h2c_root) hr0
    have hprod1 : 0 ≤ (clocal - 2 * c) * a0 :=
      mul_nonneg (sub_nonneg.mpr h2c_local) ha0
    change croot * r0 ≤
      observedMinimaxRisk J n beta kappa L cminus cplus pmin delta at hrn
    have hln' : clocal * a0 ≤
        observedMinimaxRisk J n beta kappa L cminus cplus pmin delta := by
      dsimp at hln
      convert hln using 1 <;> simp [a0, delta, h] <;> ring
    nlinarith
  have hmiddle := observedMinimaxRisk_le_stabilizedWorstRisk J n (Bseq n)
    beta kappa L cminus cplus pmin deltaBar alpha delta hreg hdelta1
  have hr : 0 ≤ clampFrontier n delta kappa h beta := by
    exact add_nonneg hr0 ha0
  have hupper' : stabilizedWorstRisk J n (Bseq n) beta kappa L cminus cplus
      pmin deltaBar delta ≤ C * clampFrontier n delta kappa h beta :=
    hun.trans (mul_le_mul_of_nonneg_right hCupperC hr)
  rcases hgn with
    ⟨P0, P1, hP0, hP1, hiid0, hiid1, hshift, hsepG, hproperG, hchiG⟩
  rcases hwn with
    ⟨Q0, Q1, hQ0, hQ1, hqiid0, hqiid1, hpert, hsepL, hproperL, hchiL⟩
  have hsepG' : c * r0 ≤
      |clampFunctional P1 delta - clampFunctional P0 delta| :=
    (mul_le_mul_of_nonneg_right hc_half hr0).trans (by simpa [r0, delta] using hsepG)
  have hsepL' : c * a0 ≤
      |clampFunctional Q1 delta - clampFunctional Q0 delta| := by
    have hampsep : amplitude * a0 ≤
        |clampFunctional Q1 delta - clampFunctional Q0 delta| := by
      convert hsepL using 1 <;> simp [a0, delta, h] <;> ring
    exact (mul_le_mul_of_nonneg_right hc_amp ha0).trans hampsep
  refine ⟨?_, hmiddle, hupper', ?_, ?_⟩
  · simpa [clampFrontier, r0, a0, delta, h] using hlower
  · exact ⟨P0, P1, hP0, hP1, hiid0, hiid1,
      by simpa [r0] using hshift, hsepG', hproperG, hchiG.trans hexpC⟩
  · refine ⟨Q0, Q1, hQ0, hQ1, hqiid0, hqiid1,
      by simpa [delta, h] using hpert, ?_, hproperL, hchiL.trans hDC⟩
    convert hsepL' using 1 <;> simp [a0, delta, h] <;> ring

end


end CausalSmith.Stat.LmtpThresholdAtomFrontier

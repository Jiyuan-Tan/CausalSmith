/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.TMinimaxRisk
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.WeightedConcentration
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.ContinuityCriteriaLift
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.ContinuityRates
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.ContinuityRiskLower
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.ContinuityLengthLower
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.ContinuityProcedureBounds
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.ContinuityExpectedLength
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.HonestCoverage
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.HonestLengthLower
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.HonestIntervalBasic
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.HonestLengthUpper
import Causalean.Stat.Minimax.HonestConfidenceSet

/-!
# Uniformly honest confidence length frontier

The statement gives finite-sample eventual uniform coverage, expected-length
control for the concrete atom-fallback interval, and a converse for every
uniformly honest confidence procedure.
-/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open Filter MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The paper's confidence procedure at a fixed sample size. -/
def stabilizedInterval (B : SplitBlocks n) (beta kappa L cminus cplus deltaBar delta alpha : ℝ) :
    ConfidenceProcedure n J :=
  fun z => honestInterval B z (ellOf beta) beta kappa L cminus cplus delta
    (infoBandwidth n delta beta kappa deltaBar) alpha

/-- Worst-case coverage of the concrete interval over i.i.d. model laws. -/
def stabilizedCoverage (J n : ℕ) (B : SplitBlocks n)
    (beta kappa L cminus cplus pmin deltaBar delta alpha : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ P : ClampLaw J,
    ClampModel P beta kappa L cminus cplus pmin ∧ IidSampling P n ∧
    v = (iidProduct P n).real
      {z | clampFunctional P delta ∈
        stabilizedInterval B beta kappa L cminus cplus deltaBar delta alpha z}}

/-- Worst-case expected length of the concrete interval. -/
def stabilizedWorstLength (J n : ℕ) (B : SplitBlocks n)
    (beta kappa L cminus cplus pmin deltaBar delta alpha : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ P : ClampLaw J,
    ClampModel P beta kappa L cminus cplus pmin ∧ IidSampling P n ∧
    v = ∫ z, intervalLength
      (stabilizedInterval B beta kappa L cminus cplus deltaBar delta alpha z)
        ∂iidProduct P n}

/-- Worst-case expected length of any given confidence procedure. -/
def confidenceWorstLength (J n : ℕ)
    (beta kappa L cminus cplus pmin : ℝ) (C : ConfidenceProcedure n J) : ℝ≥0∞ :=
  sSup {v : ℝ≥0∞ | ∃ P : ClampLaw J,
    ClampModel P beta kappa L cminus cplus pmin ∧
    v = ∫⁻ z, intervalLengthENNReal (C z) ∂iidProduct P n}

/-- The modelwise finite-sample coverage inequality passes through the
worst-model infimum defining the paper's concrete coverage criterion. The result uses [the `hreg` condition](hyp:hreg), [the `hn` condition](hyp:hn), [the `hdelta` condition](hyp:hdelta), [the `hh` condition](hyp:hh), [the `hupper` condition](hyp:hupper). [This is the stated conclusion](goal).
-/
lemma stabilizedCoverage_ge
    (J n : ℕ) (B : SplitBlocks n)
    (beta kappa L cminus cplus pmin deltaBar delta alpha : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha)
    (hn : 4 ≤ n) (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar)
    (hh : 0 < infoBandwidth n delta beta kappa deltaBar)
    (hupper : delta + infoBandwidth n delta beta kappa deltaBar ≤ 1) :
    1 - alpha ≤ stabilizedCoverage J n B beta kappa L cminus cplus pmin
      deltaBar delta alpha := by
  have hreg' := hreg
  rcases hreg' with ⟨hJ, hbeta, hkappa, hL, hcminus, hcminusK, hcplus,
    hpmin, hpminJ, hdbar, hdbar1, ha, ha1⟩
  unfold stabilizedCoverage
  apply le_csInf
  · let P0 := minimaxClampLaw J kappa (fun _ : Fin J × ℝ => 0)
    have hP0 : ClampModel P0 beta kappa L cminus cplus pmin :=
      minimaxCenter_mem_model J beta kappa L cminus cplus pmin deltaBar alpha hreg
    exact ⟨(iidProduct P0 n).real {z | clampFunctional P0 delta ∈
      stabilizedInterval B beta kappa L cminus cplus deltaBar delta alpha z},
      P0, hP0, clampModel_iidSampling hP0, rfl⟩
  · intro v hv
    rcases hv with ⟨P, hP, _hiid, rfl⟩
    simpa [stabilizedInterval] using
      honestInterval_coverage_model P B beta kappa L cminus cplus pmin delta
        (infoBandwidth n delta beta kappa deltaBar) alpha hP hJ hbeta hL ha ha1
        hn hdelta.1 hupper hh
        (totalGram_lambdaStar_pos J beta kappa L cminus cplus pmin deltaBar alpha hreg)

/-- The concrete stabilized interval is an admissible uniformly covering
procedure at every sample size where the bandwidth lies inside the design
support. The result uses [the `hreg` condition](hyp:hreg), [the `hn` condition](hyp:hn), [the `hdelta` condition](hyp:hdelta), [the `hh` condition](hyp:hh), [the `hupper` condition](hyp:hupper). [This is the stated conclusion](goal).
-/
lemma stabilizedInterval_uniformCoverage
    (J n : ℕ) (B : SplitBlocks n)
    (beta kappa L cminus cplus pmin deltaBar delta alpha : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha)
    (hn : 4 ≤ n) (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar)
    (hh : 0 < infoBandwidth n delta beta kappa deltaBar)
    (hupper : delta + infoBandwidth n delta beta kappa deltaBar ≤ 1) :
    UniformCoverage J n beta kappa L cminus cplus pmin delta alpha
      (stabilizedInterval B beta kappa L cminus cplus deltaBar delta alpha) := by
  constructor
  · exact honestInterval_observedMeasurable J n B beta kappa L cminus cplus
      pmin deltaBar alpha delta hreg hn hh.le
  · intro P hP
    have hreg' := hreg
    rcases hreg' with ⟨hJ, hbeta, hkappa, hL, hcminus, hcminusK, hcplus,
      hpmin, hpminJ, hdbar, hdbar1, ha, ha1⟩
    simpa [stabilizedInterval] using
      honestInterval_coverage_model P B beta kappa L cminus cplus pmin delta
        (infoBandwidth n delta beta kappa deltaBar) alpha hP hJ hbeta hL ha ha1
        hn hdelta.1 hupper hh
        (totalGram_lambdaStar_pos J beta kappa L cminus cplus pmin deltaBar alpha hreg)

/-- The bias-aware interval is uniformly honest and rate-optimal in worst-case
expected length, including singular-Gram samples via its atom fallback. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
-- @node: thm:honest-length
theorem honest_coverage_and_length
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha) :
    ∃ c C : ℝ, 0 < c ∧ c < C ∧
    ∀ (deltaSeq : ℕ → ℝ), ThresholdSequence deltaBar deltaSeq →
    ∀ Bseq : ∀ n, SplitBlocks n,
      ∀ᶠ n in atTop,
        let delta := deltaSeq n
        let h := infoBandwidth n delta beta kappa deltaBar
        let r := clampFrontier n delta kappa h beta
        1 - alpha ≤ stabilizedCoverage J n (Bseq n) beta kappa L cminus cplus
          pmin deltaBar delta alpha ∧
        c * r ≤ stabilizedWorstLength J n (Bseq n) beta kappa L cminus cplus
          pmin deltaBar delta alpha ∧
        stabilizedWorstLength J n (Bseq n) beta kappa L cminus cplus
          pmin deltaBar delta alpha ≤ C * r ∧
        ENNReal.ofReal (c * r) ≤ observedMinimaxLength J n beta kappa L cminus cplus
          pmin delta alpha ∧
        ∀ Cn : ConfidenceProcedure n J,
          UniformCoverage J n beta kappa L cminus cplus pmin delta alpha Cn →
          ENNReal.ofReal (c * r) ≤
            confidenceWorstLength J n beta kappa L cminus cplus pmin Cn := by
  obtain ⟨Cu, hCu, huRaw⟩ := honestInterval_worstLength_eventually_le_frontier
    J beta kappa L cminus cplus pmin deltaBar alpha hreg
  have hu : ∀ (deltaSeq : ℕ → ℝ), ThresholdSequence deltaBar deltaSeq →
      ∀ Bseq : ∀ n, SplitBlocks n, ∀ᶠ n in atTop,
        stabilizedWorstLength J n (Bseq n) beta kappa L cminus cplus pmin
          deltaBar (deltaSeq n) alpha ≤ Cu * clampFrontier n (deltaSeq n) kappa
            (infoBandwidth n (deltaSeq n) beta kappa deltaBar) beta := by
    intro deltaSeq hdelta Bseq
    simpa [stabilizedWorstLength, stabilizedInterval] using huRaw deltaSeq hdelta Bseq
  obtain ⟨co, hco, ho⟩ := observedMinimaxLength_eventually_ge_frontier J beta
    kappa L cminus cplus pmin deltaBar alpha hreg
  obtain ⟨cp, hcp, hp⟩ := procedureWorstLength_eventually_ge_frontier J beta
    kappa L cminus cplus pmin deltaBar alpha hreg
  let c := min co cp / 2
  let C := Cu + c + 1
  have hc : 0 < c := by dsimp [c]; positivity
  have hcC : c < C := by dsimp [C]; linarith
  refine ⟨c, C, hc, hcC, ?_⟩
  intro deltaSeq hdelta Bseq
  have hbal := infoBandwidth_eventually_balance beta kappa deltaBar hreg.2.1
    hreg.2.2.1 ⟨hreg.2.2.2.2.2.2.2.2.2.1,
      hreg.2.2.2.2.2.2.2.2.2.2.1⟩ deltaSeq hdelta
  filter_upwards [hu deltaSeq hdelta Bseq, ho deltaSeq hdelta,
    hp deltaSeq hdelta, hbal, eventually_ge_atTop 8] with n hun hon hpn hbn hn
  let delta := deltaSeq n
  let h := infoBandwidth n delta beta kappa deltaBar
  let r := clampFrontier n delta kappa h beta
  have hdeltaN : delta ∈ Set.Icc (0 : ℝ) deltaBar := hdelta n
  have hh : 0 < h := by simpa [h, delta] using hbn.1
  have hupper : delta + h ≤ 1 := by
    have := hbn.2.1
    dsimp [h, delta]
    linarith [hdeltaN.2]
  have hrpos : 0 < r := by
    dsimp [r, clampFrontier]
    exact add_pos_of_pos_of_nonneg
      (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) _)
      (mul_nonneg (Real.rpow_nonneg hdeltaN.1 _) (Real.rpow_nonneg hh.le _))
  have hr : 0 ≤ r := hrpos.le
  have hcov : 1 - alpha ≤ stabilizedCoverage J n (Bseq n) beta kappa L
      cminus cplus pmin deltaBar delta alpha :=
    stabilizedCoverage_ge J n (Bseq n) beta kappa L cminus cplus pmin deltaBar
      delta alpha hreg (by omega) hdeltaN (by simpa [h]) (by simpa [h] using hupper)
  have hUC : UniformCoverage J n beta kappa L cminus cplus pmin delta alpha
      (stabilizedInterval (Bseq n) beta kappa L cminus cplus deltaBar delta alpha) :=
    stabilizedInterval_uniformCoverage J n (Bseq n) beta kappa L cminus cplus pmin
      deltaBar delta alpha hreg (by omega) hdeltaN (by simpa [h])
      (by simpa [h] using hupper)
  have hc_co : c ≤ co := by
    dsimp [c]
    have hm := min_le_left co cp
    nlinarith [hco]
  have hc_cp : c ≤ cp := by
    dsimp [c]
    have hm := min_le_right co cp
    nlinarith [hcp]
  have hobs : ENNReal.ofReal (c * r) ≤ observedMinimaxLength J n beta kappa L
      cminus cplus pmin delta alpha := by
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc_co hr)).trans
      (by simpa [r, h, delta] using hon)
  have hconcreteENN : ENNReal.ofReal (c * r) ≤ ENNReal.ofReal
      (stabilizedWorstLength J n (Bseq n) beta kappa L cminus cplus pmin
        deltaBar delta alpha) := by
    calc
      _ ≤ ENNReal.ofReal (cp * r) := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hc_cp hr)
      _ ≤ clampProcedureWorstLength J n beta kappa L cminus cplus pmin
          (stabilizedInterval (Bseq n) beta kappa L cminus cplus deltaBar delta alpha) := by
        simpa [r, h, delta] using hpn _ hUC
      _ ≤ _ := by
        apply clampProcedureWorstLength_honestInterval_le_ofReal
        rfl
  have hswpos : 0 < stabilizedWorstLength J n (Bseq n) beta kappa L
      cminus cplus pmin deltaBar delta alpha := by
    apply ENNReal.ofReal_pos.mp
    exact (ENNReal.ofReal_pos.2 (mul_pos hc hrpos)).trans_le hconcreteENN
  have hconcrete : c * r ≤ stabilizedWorstLength J n (Bseq n) beta kappa L
      cminus cplus pmin deltaBar delta alpha :=
    (ENNReal.ofReal_le_ofReal_iff hswpos.le).mp hconcreteENN
  have huC : stabilizedWorstLength J n (Bseq n) beta kappa L cminus cplus pmin
      deltaBar delta alpha ≤ C * r := by
    have hCuC : Cu ≤ C := by dsimp [C]; linarith
    have hun' : stabilizedWorstLength J n (Bseq n) beta kappa L cminus cplus pmin
        deltaBar delta alpha ≤ Cu * r := by simpa [r, h, delta] using hun
    exact hun'.trans (mul_le_mul_of_nonneg_right hCuC hr)
  refine ⟨hcov, hconcrete, huC, hobs, ?_⟩
  intro Cn hCn
  have hpc := hpn Cn hCn
  exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc_cp hr)).trans
    (by simpa [confidenceWorstLength, clampProcedureWorstLength, r, h, delta] using hpc)

/-- Worst-case continuity-only risk of the fixed one-half fallback estimator. -/
def contStabilizedWorstRisk (J n : ℕ) (B : SplitBlocks n)
    (kappa cminus cplus pmin deltaBar delta : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ (P : ClampLaw J)
      (hP : ContClampModel P kappa cminus cplus pmin deltaBar),
    IidSampling P n ∧
    v = contEstimatorRisk P n kappa cminus cplus pmin deltaBar delta hP
      (contFallbackEstimator B · delta)}

/-- Worst-case coverage of the continuity-only Hoeffding interval. -/
def contStabilizedCoverage (J n : ℕ) (B : SplitBlocks n)
    (kappa cminus cplus pmin deltaBar delta alpha : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ (P : ClampLaw J)
      (hP : ContClampModel P kappa cminus cplus pmin deltaBar),
    IidSampling P n ∧
    v = (iidProduct P n).real
      {z | contClampFunctional P kappa cminus cplus pmin deltaBar hP delta ∈
        contHoeffdingInterval B z delta alpha}}

/-- Worst-case extended expected length of the continuity-only interval. -/
def contStabilizedWorstLength (J n : ℕ) (B : SplitBlocks n)
    (kappa cminus cplus pmin deltaBar delta alpha : ℝ) : ℝ≥0∞ :=
  sSup {v : ℝ≥0∞ | ∃ (P : ClampLaw J)
      (_hP : ContClampModel P kappa cminus cplus pmin deltaBar),
    IidSampling P n ∧
    v = ∫⁻ z, intervalLengthENNReal (contHoeffdingInterval B z delta alpha)
      ∂iidProduct P n}

/-- Worst-case causal risk of the same continuity-only observed-sample
fallback estimator, over law-specific latent carriers. -/
def contCausalStabilizedWorstRisk (J n : ℕ) (B : SplitBlocks n)
    (kappa cminus cplus pmin deltaBar delta : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ (PF : FullDataLaw J)
      (_hPF : ContFullDataClampModel PF kappa cminus cplus pmin deltaBar),
    v = causalEstimatorRisk PF n delta (contFallbackEstimator B · delta)}

/-- Worst-case causal coverage of the same continuity-only interval, over
law-specific latent carriers. -/
def contCausalStabilizedCoverage (J n : ℕ) (B : SplitBlocks n)
    (kappa cminus cplus pmin deltaBar delta alpha : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ (PF : FullDataLaw J)
      (_hPF : ContFullDataClampModel PF kappa cminus cplus pmin deltaBar),
    v = (iidProduct PF.observedMargin n).real
      {z | causalClampMean PF delta ∈ contHoeffdingInterval B z delta alpha}}

/-- Worst-case causal expected length of the same continuity-only interval,
over law-specific latent carriers. -/
def contCausalStabilizedWorstLength (J n : ℕ) (B : SplitBlocks n)
    (kappa cminus cplus pmin deltaBar delta alpha : ℝ) : ℝ≥0∞ :=
  sSup {v : ℝ≥0∞ | ∃ (PF : FullDataLaw J)
      (_hPF : ContFullDataClampModel PF kappa cminus cplus pmin deltaBar),
    v = ∫⁻ z, intervalLengthENNReal (contHoeffdingInterval B z delta alpha)
      ∂iidProduct PF.observedMargin n}

/-- The fixed-fallback estimator is measurable and remains in the outcome
range. [This is the stated conclusion](goal).
-/
lemma contFallbackEstimator_admissible {J n : ℕ} (B : SplitBlocks n)
    (delta : ℝ) :
    ObservedMeasurableEstimator (fun z : Fin n → ClampObs J =>
      contFallbackEstimator B z delta) ∧
    ∀ z : Fin n → ClampObs J,
      contFallbackEstimator B z delta ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · unfold ObservedMeasurableEstimator contFallbackEstimator
    apply clampUnit_measurable'.comp
    exact (retainedEstimate_measurable B delta).add
      (measurable_const.mul (Finset.measurable_fun_sum _ fun x _ =>
        atomEstimate_measurable B x delta))
  · intro z
    exact clampUnit_mem_Icc _

/-- Surjectivity and identification equate the concrete observed and causal
worst-case risks. The result uses [the `hreg` condition](hyp:hreg), [the `hdelta` condition](hyp:hdelta). [This is the stated conclusion](goal).
-/
lemma contCausalStabilizedWorstRisk_eq_observed
    (J n : ℕ) (B : SplitBlocks n)
    (kappa cminus cplus pmin deltaBar delta alpha : ℝ)
    (hreg : ContRegimeConstants J kappa cminus cplus pmin deltaBar alpha)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar) :
    contCausalStabilizedWorstRisk J n B kappa cminus cplus pmin deltaBar delta =
      contStabilizedWorstRisk J n B kappa cminus cplus pmin deltaBar delta := by
  unfold contCausalStabilizedWorstRisk contStabilizedWorstRisk
  apply congrArg sSup
  ext v
  constructor
  · rintro ⟨PF, hPF, rfl⟩
    refine ⟨PF.observedMargin, hPF.observedModel,
      contClampModel_iidSampling hPF.observedModel, ?_⟩
    exact causalEstimatorRisk_eq_contEstimatorRisk J n kappa cminus cplus pmin
      deltaBar delta hreg.1 hdelta PF hPF _
  · rintro ⟨P, hP, _hiid, rfl⟩
    obtain ⟨PF, hPF, hmargin⟩ := exists_fullData_cont_lift P hP
      hreg.1.2.2.2.2.2.1
    subst P
    refine ⟨PF, hPF, ?_⟩
    exact (causalEstimatorRisk_eq_contEstimatorRisk J n kappa cminus cplus pmin
      deltaBar delta hreg.1 hdelta PF hPF _).symm

/-- Surjectivity and identification equate the concrete observed and causal
worst-case coverages. The result uses [the `hreg` condition](hyp:hreg), [the `hdelta` condition](hyp:hdelta). [This is the stated conclusion](goal).
-/
lemma contCausalStabilizedCoverage_eq_observed
    (J n : ℕ) (B : SplitBlocks n)
    (kappa cminus cplus pmin deltaBar delta alpha : ℝ)
    (hreg : ContRegimeConstants J kappa cminus cplus pmin deltaBar alpha)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar) :
    contCausalStabilizedCoverage J n B kappa cminus cplus pmin deltaBar delta alpha =
      contStabilizedCoverage J n B kappa cminus cplus pmin deltaBar delta alpha := by
  have htarget (PF : FullDataLaw J)
      (hPF : ContFullDataClampModel PF kappa cminus cplus pmin deltaBar) :
      causalClampMean PF delta = contClampFunctional PF.observedMargin kappa
        cminus cplus pmin deltaBar hPF.observedModel delta :=
    (continuity_causal_bridge J kappa cminus cplus pmin deltaBar PF hPF hreg.1).2
      delta hdelta
  unfold contCausalStabilizedCoverage contStabilizedCoverage
  apply congrArg sInf
  ext v
  constructor
  · rintro ⟨PF, hPF, rfl⟩
    refine ⟨PF.observedMargin, hPF.observedModel,
      contClampModel_iidSampling hPF.observedModel, ?_⟩
    rw [htarget PF hPF]
  · rintro ⟨P, hP, _hiid, rfl⟩
    obtain ⟨PF, hPF, hmargin⟩ := exists_fullData_cont_lift P hP
      hreg.1.2.2.2.2.2.1
    subst P
    refine ⟨PF, hPF, ?_⟩
    rw [htarget PF hPF]

/-- Surjectivity equates the concrete observed and causal worst-case expected
lengths. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
lemma contCausalStabilizedWorstLength_eq_observed
    (J n : ℕ) (B : SplitBlocks n)
    (kappa cminus cplus pmin deltaBar delta alpha : ℝ)
    (hreg : ContRegimeConstants J kappa cminus cplus pmin deltaBar alpha) :
    contCausalStabilizedWorstLength J n B kappa cminus cplus pmin deltaBar delta alpha =
      contStabilizedWorstLength J n B kappa cminus cplus pmin deltaBar delta alpha := by
  unfold contCausalStabilizedWorstLength contStabilizedWorstLength
  apply congrArg sSup
  ext v
  constructor
  · rintro ⟨PF, hPF, rfl⟩
    exact ⟨PF.observedMargin, hPF.observedModel,
      contClampModel_iidSampling hPF.observedModel, rfl⟩
  · rintro ⟨P, hP, _hiid, rfl⟩
    obtain ⟨PF, hPF, hmargin⟩ := exists_fullData_cont_lift P hP
      hreg.1.2.2.2.2.2.1
    exact ⟨PF, hPF, by rw [hmargin]⟩

/-- The fixed fallback is an admissible competitor for the observed minimax
risk criterion. The result uses [the `hreg` condition](hyp:hreg), [the `hdelta` condition](hyp:hdelta). [This is the stated conclusion](goal).
-/
lemma contFrontierCriteria_risk_le_stabilized
    (J n : ℕ) (B : SplitBlocks n)
    (kappa cminus cplus pmin deltaBar delta alpha : ℝ)
    (hreg : ContRegimeConstants J kappa cminus cplus pmin deltaBar alpha)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar) :
    (contFrontierCriteria J n kappa cminus cplus pmin deltaBar delta alpha).1 ≤
      contStabilizedWorstRisk J n B kappa cminus cplus pmin deltaBar delta := by
  simp only [contFrontierCriteria, Prod.fst]
  unfold contStabilizedWorstRisk
  let outer : Set ℝ := {r : ℝ | ∃ est : Estimator n J,
    ObservedMeasurableEstimator est ∧ (∀ z, est z ∈ Set.Icc (0 : ℝ) 1) ∧
    r = sSup {v : ℝ | ∃ (P : ClampLaw J)
      (hP : ContClampModel P kappa cminus cplus pmin deltaBar),
      v = contEstimatorRisk P n kappa cminus cplus pmin deltaBar delta hP est}}
  change sInf outer ≤ _
  have houterBelow : BddBelow outer := by
    refine ⟨0, ?_⟩
    rintro r ⟨est, hmeas, hrange, rfl⟩
    let risks : Set ℝ := {v : ℝ | ∃ (P : ClampLaw J)
      (hP : ContClampModel P kappa cminus cplus pmin deltaBar),
      v = contEstimatorRisk P n kappa cminus cplus pmin deltaBar delta hP est}
    have hbdd : BddAbove risks := by
      refine ⟨1, ?_⟩
      rintro v ⟨P, hP, rfl⟩
      letI : IsProbabilityMeasure P.dataMeasure := hP.probability
      letI : IsProbabilityMeasure (iidProduct P n) := by unfold iidProduct; infer_instance
      let target := contClampFunctional P kappa cminus cplus pmin deltaBar hP delta
      have ht := contClampFunctional_mem_Icc P kappa cminus cplus pmin deltaBar
        delta hP hreg.1 hdelta
      have hpoint (z : Fin n → ClampObs J) : |est z - target| ≤ 1 := by
        rw [abs_le]
        dsimp [target]
        constructor <;> linarith [(hrange z).1, (hrange z).2, ht.1, ht.2]
      unfold contEstimatorRisk
      change (∫ z, |est z - target| ∂iidProduct P n) ≤ 1
      have hmono := integral_mono_ae
        (Integrable.of_bound
          ((hmeas.sub (measurable_const : Measurable
            (fun _ : Fin n → ClampObs J => target))).abs.aestronglyMeasurable) 1
          (ae_of_all _ fun z => by
            rw [Real.norm_eq_abs, abs_abs]
            exact hpoint z))
        (integrable_const (μ := iidProduct P n) 1) (ae_of_all _ hpoint)
      simpa using hmono
    let P0 := minimaxClampLaw J kappa (fun _ : Fin J × ℝ => 0)
    have hP0 : ContClampModel P0 kappa cminus cplus pmin deltaBar :=
      minimaxClampModel_continuous J kappa cminus cplus pmin deltaBar
        hreg.1.1 hreg.1.2.1 hreg.1.2.2.2.1 hreg.1.2.2.2.2.1
        hreg.1.2.2.2.2.2.2.1 (fun _ => 0) measurable_const
        (fun _ => by norm_num) continuous_const.continuousOn
    have hnon : 0 ≤ contEstimatorRisk P0 n kappa cminus cplus pmin deltaBar
        delta hP0 est := by
      unfold contEstimatorRisk
      exact integral_nonneg_of_ae (ae_of_all _ fun z => abs_nonneg _)
    exact hnon.trans (le_csSup hbdd ⟨P0, hP0, rfl⟩)
  apply csInf_le houterBelow
  refine ⟨(fun z => contFallbackEstimator B z delta),
    (contFallbackEstimator_admissible B delta).1,
    (contFallbackEstimator_admissible B delta).2, ?_⟩
  apply congrArg sSup
  ext v
  constructor
  · rintro ⟨P, hP, _hiid, hv⟩
    exact ⟨P, hP, hv⟩
  · rintro ⟨P, hP, hv⟩
    exact ⟨P, hP, contClampModel_iidSampling hP, hv⟩

/-- The concrete continuity interval has uniform finite-sample coverage once
both deterministic blocks are nonempty. The result uses [the `HoeffdingBoundedAverage_of_gate` condition](hyp:HoeffdingBoundedAverage_of_gate), [the `hreg` condition](hyp:hreg), [the `hdelta` condition](hyp:hdelta), [the `hcard0` condition](hyp:hcard0), [the `hcard1` condition](hyp:hcard1). [This is the stated conclusion](goal).
-/
lemma contStabilizedCoverage_ge
    (HoeffdingBoundedAverage_of_gate : HoeffdingBoundedAverage)
    (J n : ℕ) (B : SplitBlocks n)
    (kappa cminus cplus pmin deltaBar delta alpha : ℝ)
    (hreg : ContRegimeConstants J kappa cminus cplus pmin deltaBar alpha)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar)
    (hcard0 : 0 < B.I0.card) (hcard1 : 0 < B.I1.card) :
    1 - alpha ≤ contStabilizedCoverage J n B kappa cminus cplus pmin
      deltaBar delta alpha := by
  unfold contStabilizedCoverage
  apply le_csInf
  · let P0 := minimaxClampLaw J kappa (fun _ : Fin J × ℝ => 0)
    have hP0 : ContClampModel P0 kappa cminus cplus pmin deltaBar :=
      minimaxClampModel_continuous J kappa cminus cplus pmin deltaBar
        hreg.1.1 hreg.1.2.1 hreg.1.2.2.2.1 hreg.1.2.2.2.2.1
        hreg.1.2.2.2.2.2.2.1 (fun _ => 0) measurable_const
        (fun _ => by norm_num) continuous_const.continuousOn
    exact ⟨(iidProduct P0 n).real {z |
      contClampFunctional P0 kappa cminus cplus pmin deltaBar hP0 delta ∈
        contHoeffdingInterval B z delta alpha}, P0, hP0,
      contClampModel_iidSampling hP0, rfl⟩
  · intro v hv
    rcases hv with ⟨P, hP, _hiid, rfl⟩
    exact contHoeffdingInterval_coverage_model HoeffdingBoundedAverage_of_gate
      P B kappa cminus cplus pmin deltaBar delta alpha hP hreg hdelta hcard0 hcard1

/-- The concrete fixed-fallback worst-case risk attains the continuity rate. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
lemma contStabilizedWorstRisk_eventually_le_frontier
    (J : ℕ) (kappa cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : ContRegimeConstants J kappa cminus cplus pmin deltaBar alpha) :
    ∃ C : ℝ, 0 < C ∧ ∀ deltaSeq : ℕ → ℝ,
      ThresholdSequence deltaBar deltaSeq → ∀ Bseq : ∀ n, SplitBlocks n,
      ∀ᶠ n : ℕ in atTop,
        contStabilizedWorstRisk J n (Bseq n) kappa cminus cplus pmin deltaBar
          (deltaSeq n) ≤ C * contFrontier n (deltaSeq n) kappa := by
  let C : ℝ := 3 * (1 + (J : ℝ)) * (1 + cplus / (kappa + 1))
  have hk1 : 0 < kappa + 1 := by linarith [hreg.1.2.1]
  have hcplus0 : 0 < cplus := hk1.trans_le hreg.1.2.2.2.2.1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro deltaSeq hdelta Bseq
  filter_upwards [eventually_ge_atTop 8] with n hn
  have hnpos : 0 < n := by omega
  have hcard0 : 0 < (Bseq n).I0.card := by
    have := (Bseq n).card_I0
    omega
  have hcard1 : 0 < (Bseq n).I1.card := by
    have := (Bseq n).card_I1
    omega
  let root : ℝ := (n : ℝ) ^ (-(1 : ℝ) / 2)
  let atom : ℝ := (deltaSeq n) ^ (kappa + 1)
  have hroot : 0 ≤ root := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hatom : 0 ≤ atom := Real.rpow_nonneg (hdelta n).1 _
  have hsqrt0 : Real.sqrt ((Bseq n).I0.card : ℝ)⁻¹ ≤ 3 * root := by
    apply splitBlock_invSqrt_le_root hnpos
    have := (Bseq n).card_I0
    omega
  have hsqrt1 : Real.sqrt ((Bseq n).I1.card : ℝ)⁻¹ ≤ 3 * root := by
    apply splitBlock_invSqrt_le_root hnpos
    have := (Bseq n).card_I1
    omega
  apply csSup_le
  · let P0 := minimaxClampLaw J kappa (fun _ : Fin J × ℝ => 0)
    have hP0 : ContClampModel P0 kappa cminus cplus pmin deltaBar :=
      minimaxClampModel_continuous J kappa cminus cplus pmin deltaBar
        hreg.1.1 hreg.1.2.1 hreg.1.2.2.2.1 hreg.1.2.2.2.2.1
        hreg.1.2.2.2.2.2.2.1 (fun _ => 0) measurable_const
        (fun _ => by norm_num) continuous_const.continuousOn
    exact ⟨contEstimatorRisk P0 n kappa cminus cplus pmin deltaBar
      (deltaSeq n) hP0 (contFallbackEstimator (Bseq n) · (deltaSeq n)),
      P0, hP0, contClampModel_iidSampling hP0, rfl⟩
  · intro v hv
    rcases hv with ⟨P, hP, _hiid, rfl⟩
    have he := contFallbackEstimator_risk_le_explicit P (Bseq n) kappa cminus
      cplus pmin deltaBar (deltaSeq n) hP hreg.1 (hdelta n) hcard0 hcard1
    have hcoef : (3 / 2 : ℝ) + (J : ℝ) * (3 / 4) ≤ C := by
      dsimp [C]
      have hJ : 0 ≤ (J : ℝ) := Nat.cast_nonneg J
      have hratio : 0 ≤ cplus / (kappa + 1) := by positivity
      nlinarith
    have hatomcoef : (J : ℝ) * ((1 / 2 : ℝ) * (cplus / (kappa + 1))) ≤ C := by
      dsimp [C]
      have hJ : 0 ≤ (J : ℝ) := Nat.cast_nonneg J
      have hratio : 0 ≤ cplus / (kappa + 1) := by positivity
      nlinarith
    calc
      _ ≤ (1 / 2 : ℝ) * (3 * root) +
          (J : ℝ) * ((1 / 4 : ℝ) * (3 * root) +
            (1 / 2 : ℝ) * (cplus * atom / (kappa + 1))) := by
        exact he.trans (add_le_add
          (mul_le_mul_of_nonneg_left hsqrt0 (by norm_num))
          (mul_le_mul_of_nonneg_left
            (add_le_add
              (mul_le_mul_of_nonneg_left hsqrt1 (by norm_num)) le_rfl)
            (Nat.cast_nonneg J)))
      _ = ((3 / 2 : ℝ) + (J : ℝ) * (3 / 4)) * root +
          ((J : ℝ) * ((1 / 2 : ℝ) * (cplus / (kappa + 1)))) * atom := by ring
      _ ≤ C * root + C * atom := add_le_add
        (mul_le_mul_of_nonneg_right hcoef hroot)
        (mul_le_mul_of_nonneg_right hatomcoef hatom)
      _ = C * contFrontier n (deltaSeq n) kappa := by
        dsimp [root, atom]
        unfold contFrontier
        ring

/-- The extended expected length of the concrete interval attains the same
continuity frontier. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
lemma contStabilizedWorstLength_eventually_le_frontier
    (J : ℕ) (kappa cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : ContRegimeConstants J kappa cminus cplus pmin deltaBar alpha) :
    ∃ C : ℝ, 0 < C ∧ ∀ deltaSeq : ℕ → ℝ,
      ThresholdSequence deltaBar deltaSeq → ∀ Bseq : ∀ n, SplitBlocks n,
      ∀ᶠ n : ℕ in atTop,
        contStabilizedWorstLength J n (Bseq n) kappa cminus cplus pmin deltaBar
          (deltaSeq n) alpha ≤ ENNReal.ofReal
            (C * contFrontier n (deltaSeq n) kappa) := by
  let K := Real.sqrt (Real.log (4 / alpha) / 2)
  let C : ℝ := 1 + 12 * K + (J : ℝ) * (3 / 2 + cplus / (kappa + 1))
  have hk1 : 0 < kappa + 1 := by linarith [hreg.1.2.1]
  have hcplus0 : 0 < cplus := hk1.trans_le hreg.1.2.2.2.2.1
  have hquot : 1 < 4 / alpha := by
    rw [lt_div_iff₀ hreg.2.1]
    linarith [hreg.2.2]
  have hloghalf : 0 ≤ Real.log (4 / alpha) / 2 :=
    div_nonneg (Real.log_pos hquot).le (by norm_num)
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hC : 0 < C := by
    dsimp [C]
    have hJ : 0 ≤ (J : ℝ) := Nat.cast_nonneg J
    have hratio : 0 ≤ cplus / (kappa + 1) := by positivity
    nlinarith
  refine ⟨C, hC, ?_⟩
  intro deltaSeq hdelta Bseq
  filter_upwards [eventually_ge_atTop 8] with n hn
  have hnpos : 0 < n := by omega
  have hcard0 : 0 < (Bseq n).I0.card := by
    have := (Bseq n).card_I0
    omega
  have hcard1 : 0 < (Bseq n).I1.card := by
    have := (Bseq n).card_I1
    omega
  let root : ℝ := (n : ℝ) ^ (-(1 : ℝ) / 2)
  let atom : ℝ := (deltaSeq n) ^ (kappa + 1)
  have hroot : 0 ≤ root := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hatom : 0 ≤ atom := Real.rpow_nonneg (hdelta n).1 _
  have hsqrt0 : Real.sqrt ((Bseq n).I0.card : ℝ)⁻¹ ≤ 3 * root := by
    apply splitBlock_invSqrt_le_root hnpos
    have := (Bseq n).card_I0
    omega
  have hsqrt1 : Real.sqrt ((Bseq n).I1.card : ℝ)⁻¹ ≤ 3 * root := by
    apply splitBlock_invSqrt_le_root hnpos
    have := (Bseq n).card_I1
    omega
  have ht0 : Real.sqrt (Real.log (4 / alpha) /
      (2 * ((Bseq n).I0.card : ℝ))) ≤ K * (3 * root) := by
    rw [show Real.log (4 / alpha) / (2 * ((Bseq n).I0.card : ℝ)) =
        (Real.log (4 / alpha) / 2) * (((Bseq n).I0.card : ℝ)⁻¹) by
      field_simp]
    rw [Real.sqrt_mul hloghalf]
    exact mul_le_mul_of_nonneg_left hsqrt0 hK
  have ht1 : Real.sqrt (Real.log (4 / alpha) /
      (2 * ((Bseq n).I1.card : ℝ))) ≤ K * (3 * root) := by
    rw [show Real.log (4 / alpha) / (2 * ((Bseq n).I1.card : ℝ)) =
        (Real.log (4 / alpha) / 2) * (((Bseq n).I1.card : ℝ)⁻¹) by
      field_simp]
    rw [Real.sqrt_mul hloghalf]
    exact mul_le_mul_of_nonneg_left hsqrt1 hK
  unfold contStabilizedWorstLength
  apply sSup_le
  intro v hv
  rcases hv with ⟨P, hP, _hiid, rfl⟩
  have he := contHoeffdingInterval_lintegral_length_le P (Bseq n) kappa cminus
    cplus pmin deltaBar (deltaSeq n) alpha hP hreg.1 (hdelta n) hcard1
  apply he.trans
  apply ENNReal.ofReal_le_ofReal
  have hrootcoef : 12 * K + (J : ℝ) * (3 / 2) ≤ C := by
    dsimp [C]
    have hJ : 0 ≤ (J : ℝ) := Nat.cast_nonneg J
    have hratio : 0 ≤ cplus / (kappa + 1) := by positivity
    nlinarith
  have hatomcoef : (J : ℝ) * (cplus / (kappa + 1)) ≤ C := by
    dsimp [C]
    have hJ : 0 ≤ (J : ℝ) := Nat.cast_nonneg J
    have hratio : 0 ≤ cplus / (kappa + 1) := by positivity
    nlinarith
  calc
    _ ≤ 2 * (K * (3 * root)) + 2 * (K * (3 * root)) +
        (J : ℝ) * ((1 / 2 : ℝ) * (3 * root) +
          cplus * atom / (kappa + 1)) := by
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left ht0 (by norm_num))
        (mul_le_mul_of_nonneg_left ht1 (by norm_num)))
        (mul_le_mul_of_nonneg_left
          (add_le_add
            (mul_le_mul_of_nonneg_left hsqrt1 (by norm_num)) le_rfl)
          (Nat.cast_nonneg J))
    _ = (12 * K + (J : ℝ) * (3 / 2)) * root +
        ((J : ℝ) * (cplus / (kappa + 1))) * atom := by ring
    _ ≤ C * root + C * atom := add_le_add
      (mul_le_mul_of_nonneg_right hrootcoef hroot)
      (mul_le_mul_of_nonneg_right hatomcoef hatom)
    _ = C * contFrontier n (deltaSeq n) kappa := by
      dsimp [root, atom]
      unfold contFrontier
      ring

/-- At a threshold converging to a positive interior point, neither the
observed nor causal continuity-only minimax risk can converge to zero. The result uses [the `hreg` condition](hyp:hreg), [the `hdelta` condition](hyp:hdelta), [the `hdelta0` condition](hyp:hdelta0), [the `htend` condition](hyp:htend). [This is the stated conclusion](goal).
-/
lemma contFrontierCriteria_fixed_positive_not_tendsto_zero
    (J : ℕ) (kappa cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : ContRegimeConstants J kappa cminus cplus pmin deltaBar alpha)
    (deltaSeq : ℕ → ℝ) (delta0 : ℝ)
    (hdelta : ThresholdSequence deltaBar deltaSeq)
    (hdelta0 : delta0 ∈ Set.Ioc (0 : ℝ) deltaBar)
    (htend : Tendsto deltaSeq atTop (nhds delta0)) :
    ¬ Tendsto
        (fun n => (contFrontierCriteria J n kappa cminus cplus pmin deltaBar
          (deltaSeq n) alpha).1) atTop (nhds 0) ∧
    ¬ Tendsto
        (fun n => (contFrontierCriteria J n kappa cminus cplus pmin deltaBar
          (deltaSeq n) alpha).2.2.1) atTop (nhds 0) := by
  obtain ⟨c, hc, hlower⟩ := contMinimaxRisk_eventually_ge_frontier J kappa
    cminus cplus pmin deltaBar alpha hreg
  have hk1 : 0 < kappa + 1 := by linarith [hreg.1.2.1]
  have hpow : Tendsto (fun n => c * (deltaSeq n) ^ (kappa + 1)) atTop
      (nhds (c * delta0 ^ (kappa + 1))) := by
    exact tendsto_const_nhds.mul
      ((Real.continuousAt_rpow_const delta0 (kappa + 1) (Or.inr hk1.le)).tendsto.comp htend)
  have hle : ∀ᶠ n : ℕ in atTop,
      c * (deltaSeq n) ^ (kappa + 1) ≤
        (contFrontierCriteria J n kappa cminus cplus pmin deltaBar
          (deltaSeq n) alpha).1 := by
    filter_upwards [hlower deltaSeq hdelta] with n hn
    have hr : 0 ≤ (n : ℝ) ^ (-(1 : ℝ) / 2) :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    calc
      c * (deltaSeq n) ^ (kappa + 1) ≤
          c * contFrontier n (deltaSeq n) kappa := by
        unfold contFrontier
        nlinarith
      _ ≤ _ := hn
  have hobs : ¬ Tendsto
      (fun n => (contFrontierCriteria J n kappa cminus cplus pmin deltaBar
        (deltaSeq n) alpha).1) atTop (nhds 0) := by
    intro hz
    have hlim : c * delta0 ^ (kappa + 1) ≤ 0 :=
      le_of_tendsto_of_tendsto hpow hz hle
    have : 0 < c * delta0 ^ (kappa + 1) :=
      mul_pos hc (Real.rpow_pos_of_pos hdelta0.1 _)
    linarith
  refine ⟨hobs, ?_⟩
  intro hcausal
  have heq : ∀ n,
      (contFrontierCriteria J n kappa cminus cplus pmin deltaBar
        (deltaSeq n) alpha).2.2.1 =
      (contFrontierCriteria J n kappa cminus cplus pmin deltaBar
        (deltaSeq n) alpha).1 := by
    intro n
    exact (contFrontierCriteria_observed_causal_eq J n kappa cminus cplus pmin
      deltaBar (deltaSeq n) alpha hreg (hdelta n)).1
  apply hobs
  exact hcausal.congr' (Filter.Eventually.of_forall heq)

/-- A threshold converging to a positive interior point also prevents the
observed minimax honest length from converging to zero. The result uses [the `hreg` condition](hyp:hreg), [the `hdelta` condition](hyp:hdelta), [the `hdelta0` condition](hyp:hdelta0), [the `htend` condition](hyp:htend). [This is the stated conclusion](goal).
-/
lemma contFrontierLength_fixed_positive_not_tendsto_zero
    (J : ℕ) (kappa cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : ContRegimeConstants J kappa cminus cplus pmin deltaBar alpha)
    (deltaSeq : ℕ → ℝ) (delta0 : ℝ)
    (hdelta : ThresholdSequence deltaBar deltaSeq)
    (hdelta0 : delta0 ∈ Set.Ioc (0 : ℝ) deltaBar)
    (htend : Tendsto deltaSeq atTop (nhds delta0)) :
    ¬ Tendsto
        (fun n => (contFrontierCriteria J n kappa cminus cplus pmin deltaBar
          (deltaSeq n) alpha).2.1) atTop (nhds 0) := by
  obtain ⟨c, hc, hlower⟩ := contMinimaxLength_eventually_ge_frontier J kappa
    cminus cplus pmin deltaBar alpha hreg
  have hk1 : 0 < kappa + 1 := by linarith [hreg.1.2.1]
  have hpowR : Tendsto (fun n => c * (deltaSeq n) ^ (kappa + 1)) atTop
      (nhds (c * delta0 ^ (kappa + 1))) :=
    tendsto_const_nhds.mul
      ((Real.continuousAt_rpow_const delta0 (kappa + 1) (Or.inr hk1.le)).tendsto.comp htend)
  have hpow : Tendsto (fun n => ENNReal.ofReal
      (c * (deltaSeq n) ^ (kappa + 1))) atTop
      (nhds (ENNReal.ofReal (c * delta0 ^ (kappa + 1)))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hpowR
  have hle : ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (c * (deltaSeq n) ^ (kappa + 1)) ≤
        (contFrontierCriteria J n kappa cminus cplus pmin deltaBar
          (deltaSeq n) alpha).2.1 := by
    filter_upwards [hlower deltaSeq hdelta] with n hn
    apply (ENNReal.ofReal_le_ofReal ?_).trans hn
    have hr := Real.rpow_nonneg (Nat.cast_nonneg n) (-(1 : ℝ) / 2)
    unfold contFrontier
    nlinarith
  intro hz
  have hlim : ENNReal.ofReal (c * delta0 ^ (kappa + 1)) ≤ 0 :=
    le_of_tendsto_of_tendsto hpow hz hle
  have hp : 0 < c * delta0 ^ (kappa + 1) :=
    mul_pos hc (Real.rpow_pos_of_pos hdelta0.1 _)
  have : (0 : ℝ≥0∞) < ENNReal.ofReal (c * delta0 ^ (kappa + 1)) :=
    ENNReal.ofReal_pos.mpr hp
  exact (not_lt_of_ge hlim) this

/-- Conditional on the disclosed Hoeffding gate, the fixed-fallback estimator
and interval attain the continuity-only frontier, with identical observed and
causal decision criteria. The result uses [the `HoeffdingBoundedAverage_of_gate` condition](hyp:HoeffdingBoundedAverage_of_gate), [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
-- @node: thm:continuity-only-frontier
theorem continuity_only_frontier
    (HoeffdingBoundedAverage_of_gate : HoeffdingBoundedAverage)
    (J : ℕ) (kappa cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : ContRegimeConstants J kappa cminus cplus pmin deltaBar alpha) :
    ∃ c C : ℝ, 0 < c ∧ c < C ∧
    (∀ (deltaSeq : ℕ → ℝ), ThresholdSequence deltaBar deltaSeq →
      ∀ Bseq : ∀ n, SplitBlocks n,
        ∀ᶠ n in atTop,
          let delta := deltaSeq n
          let s := contFrontier n delta kappa
          let crit := contFrontierCriteria J n kappa cminus cplus pmin
            deltaBar delta alpha
          c * s ≤ crit.1 ∧
          crit.1 ≤ contStabilizedWorstRisk J n (Bseq n) kappa cminus cplus pmin
            deltaBar delta ∧
          contStabilizedWorstRisk J n (Bseq n) kappa cminus cplus pmin
            deltaBar delta ≤ C * s ∧
          1 - alpha ≤ contStabilizedCoverage J n (Bseq n) kappa cminus cplus pmin
            deltaBar delta alpha ∧
          contStabilizedWorstLength J n (Bseq n) kappa cminus cplus pmin
            deltaBar delta alpha ≤ ENNReal.ofReal (C * s) ∧
          ENNReal.ofReal (c * s) ≤ crit.2.1 ∧
          crit.2.2.1 = crit.1 ∧ crit.2.2.2 = crit.2.1 ∧
          crit.2.2.1 ≤ contCausalStabilizedWorstRisk J n (Bseq n) kappa cminus
            cplus pmin deltaBar delta ∧
          contCausalStabilizedWorstRisk J n (Bseq n) kappa cminus cplus pmin
            deltaBar delta ≤ C * s ∧
          1 - alpha ≤ contCausalStabilizedCoverage J n (Bseq n) kappa cminus
            cplus pmin deltaBar delta alpha ∧
          contCausalStabilizedWorstLength J n (Bseq n) kappa cminus cplus pmin
            deltaBar delta alpha ≤ ENNReal.ofReal (C * s)) ∧
    AsympSeq
      (fun n => contFrontier n
        ((n : ℝ) ^ (-(1 : ℝ) / (2 * (kappa + 1)))) kappa)
      (fun n => (n : ℝ) ^ (-(1 : ℝ) / 2)) ∧
    AsympSeq (fun n => contFrontier n 0 kappa)
      (fun n => (n : ℝ) ^ (-(1 : ℝ) / 2)) ∧
    ∀ (deltaSeq : ℕ → ℝ) (delta0 : ℝ),
      ThresholdSequence deltaBar deltaSeq →
      delta0 ∈ Set.Ioc (0 : ℝ) deltaBar →
      Tendsto deltaSeq atTop (nhds delta0) →
      ¬ Tendsto
          (fun n => (contFrontierCriteria J n kappa cminus cplus pmin deltaBar
            (deltaSeq n) alpha).1) atTop (nhds 0) ∧
      ¬ Tendsto
          (fun n => (contFrontierCriteria J n kappa cminus cplus pmin deltaBar
            (deltaSeq n) alpha).2.1) atTop (nhds 0) := by
  obtain ⟨cr, hcr, hRiskLower⟩ := contMinimaxRisk_eventually_ge_frontier J kappa
    cminus cplus pmin deltaBar alpha hreg
  obtain ⟨cl, hcl, hLengthLower⟩ := contMinimaxLength_eventually_ge_frontier J kappa
    cminus cplus pmin deltaBar alpha hreg
  obtain ⟨CR, hCR, hRiskUpper⟩ :=
    contStabilizedWorstRisk_eventually_le_frontier J kappa cminus cplus pmin
      deltaBar alpha hreg
  obtain ⟨CL, hCL, hLengthUpper⟩ :=
    contStabilizedWorstLength_eventually_le_frontier J kappa cminus cplus pmin
      deltaBar alpha hreg
  let c := min cr cl
  let C := max CR CL + c + 1
  have hc : 0 < c := by dsimp [c]; positivity
  have hcC : c < C := by
    dsimp [C]
    have : 0 < max CR CL := lt_max_of_lt_left hCR
    linarith
  have hCRle : CR ≤ C := by
    dsimp [C]
    have := le_max_left CR CL
    linarith
  have hCLle : CL ≤ C := by
    dsimp [C]
    have := le_max_right CR CL
    linarith
  refine ⟨c, C, hc, hcC, ?_,
    contFrontier_elbow_asymp kappa hreg.1.2.1,
    contFrontier_zero_asymp kappa hreg.1.2.1, ?_⟩
  · intro deltaSeq hdelta Bseq
    filter_upwards [hRiskLower deltaSeq hdelta,
      hLengthLower deltaSeq hdelta,
      hRiskUpper deltaSeq hdelta Bseq,
      hLengthUpper deltaSeq hdelta Bseq,
      eventually_ge_atTop 8] with n hnRL hnLL hnRU hnLU hn8
    let delta := deltaSeq n
    let s := contFrontier n delta kappa
    let crit := contFrontierCriteria J n kappa cminus cplus pmin
      deltaBar delta alpha
    have hdeltaN : delta ∈ Set.Icc (0 : ℝ) deltaBar := hdelta n
    have hs : 0 ≤ s := by
      dsimp [s, delta]
      unfold contFrontier
      exact add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        (Real.rpow_nonneg (hdelta n).1 _)
    have hcard0 : 0 < (Bseq n).I0.card := by
      have := (Bseq n).card_I0
      omega
    have hcard1 : 0 < (Bseq n).I1.card := by
      have := (Bseq n).card_I1
      omega
    have hcritEq := contFrontierCriteria_observed_causal_eq J n kappa cminus
      cplus pmin deltaBar delta alpha hreg hdeltaN
    have hRiskEq := contCausalStabilizedWorstRisk_eq_observed J n (Bseq n)
      kappa cminus cplus pmin deltaBar delta alpha hreg hdeltaN
    have hCovEq := contCausalStabilizedCoverage_eq_observed J n (Bseq n)
      kappa cminus cplus pmin deltaBar delta alpha hreg hdeltaN
    have hLenEq := contCausalStabilizedWorstLength_eq_observed J n (Bseq n)
      kappa cminus cplus pmin deltaBar delta alpha hreg
    have hcov := contStabilizedCoverage_ge HoeffdingBoundedAverage_of_gate J n
      (Bseq n) kappa cminus cplus pmin deltaBar delta alpha hreg hdeltaN
      hcard0 hcard1
    have hlowRisk : c * s ≤ crit.1 := by
      exact (mul_le_mul_of_nonneg_right (min_le_left cr cl) hs).trans
        (by simpa [c, s, crit, delta] using hnRL)
    have hlowLen : ENNReal.ofReal (c * s) ≤ crit.2.1 := by
      exact (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (min_le_right cr cl) hs)).trans
        (by simpa [c, s, crit, delta] using hnLL)
    have hupRisk : contStabilizedWorstRisk J n (Bseq n) kappa cminus cplus
        pmin deltaBar delta ≤ C * s := by
      calc
        _ ≤ CR * s := by simpa [s, delta] using hnRU
        _ ≤ C * s := mul_le_mul_of_nonneg_right hCRle hs
    have hupLen : contStabilizedWorstLength J n (Bseq n) kappa cminus cplus
        pmin deltaBar delta alpha ≤ ENNReal.ofReal (C * s) := by
      calc
        _ ≤ ENNReal.ofReal (CL * s) := by simpa [s, delta] using hnLU
        _ ≤ ENNReal.ofReal (C * s) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCLle hs)
    refine ⟨hlowRisk,
      contFrontierCriteria_risk_le_stabilized J n (Bseq n) kappa cminus
        cplus pmin deltaBar delta alpha hreg hdeltaN,
      hupRisk, hcov, hupLen, hlowLen, hcritEq.1, hcritEq.2, ?_, ?_, ?_, ?_⟩
    · rw [hcritEq.1, hRiskEq]
      exact contFrontierCriteria_risk_le_stabilized J n (Bseq n) kappa cminus
        cplus pmin deltaBar delta alpha hreg hdeltaN
    · rw [hRiskEq]
      exact hupRisk
    · rw [hCovEq]
      exact hcov
    · rw [hLenEq]
      exact hupLen
  · intro deltaSeq delta0 hdelta hdelta0 htend
    exact ⟨(contFrontierCriteria_fixed_positive_not_tendsto_zero J kappa
      cminus cplus pmin deltaBar alpha hreg deltaSeq delta0 hdelta hdelta0 htend).1,
      contFrontierLength_fixed_positive_not_tendsto_zero J kappa cminus cplus
        pmin deltaBar alpha hreg deltaSeq delta0 hdelta hdelta0 htend⟩

end


end CausalSmith.Stat.LmtpThresholdAtomFrontier

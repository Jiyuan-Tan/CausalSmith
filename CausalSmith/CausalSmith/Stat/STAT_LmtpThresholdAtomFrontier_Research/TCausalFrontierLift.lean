/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.TCausalBridge
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.THonestLength
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.SurjectivityLift
import Causalean.Mathlib.Probability.Kernel.ParameterizedKernelQuantileRealization
import Mathlib.Probability.Kernel.Disintegration.Integral

/-!
# Lift of the observed frontier to the full-data causal class

All procedures remain functions only of the observed sample. The quantified
class is the full-data class, and the criteria are the two components of
`causalFrontierCriteria`.
-/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open Filter MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Mathlib's standard-Borel disintegration kernel discharges the paper's
regular-conditional-law gate. [This is the stated conclusion](goal).
-/
-- @node: standardBorelRegularConditionalLaw_mathlib
lemma standardBorelRegularConditionalLaw_mathlib :
    StandardBorelRegularConditionalLaw := by
  intro S T _ _ _ _ μ hμ
  let _ := hμ
  let _ : Nonempty T :=
    ⟨(Classical.choice (nonempty_of_isProbabilityMeasure μ)).2⟩
  let K : ProbabilityTheory.Kernel S T := μ.condKernel
  refine ⟨K, fun _ => inferInstance, ?_⟩
  intro B C hB hC
  have h := Measure.setLIntegral_condKernel
    (ρ := μ) (f := fun _ : S × T => (1 : ℝ≥0∞)) measurable_const hB hC
  simpa [K, Measure.fst] using h.symm

/-- Conditional on the disclosed regular-conditional-law gate, every observed
model law admits a structural full-data lift and the observed and causal
finite-sample criteria agree. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
-- @node: prop:observed-margin-surjectivity
theorem observed_margin_surjectivity
    (StandardBorelRegularConditionalLaw_of_gate :
      StandardBorelRegularConditionalLaw)
    (J : ℕ)
    (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha) :
    (∀ (P : ClampLaw J), ClampModel P beta kappa L cminus cplus pmin →
      ∃ PF : FullDataLaw J,
        FullDataClampModel PF beta kappa L cminus cplus pmin deltaBar ∧
          PF.observedMargin = P) ∧
    ∀ (n : ℕ) (delta : ℝ), delta ∈ Set.Icc (0 : ℝ) deltaBar →
      (causalFrontierCriteria J n beta kappa L cminus cplus pmin deltaBar
        delta alpha).1 =
        observedMinimaxRisk J n beta kappa L cminus cplus pmin delta ∧
      (causalFrontierCriteria J n beta kappa L cminus cplus pmin deltaBar
        delta alpha).2 =
        observedMinimaxLength J n beta kappa L cminus cplus pmin delta alpha := by
  have hpmin : 0 < pmin := hreg.2.2.2.2.2.2.2.1
  have hJ : 0 < J := hreg.1
  have hdeltaBar : deltaBar ≤ 1 :=
    (hreg.2.2.2.2.2.2.2.2.2.2.1).le
  have hsurj : ∀ (P : ClampLaw J), ClampModel P beta kappa L cminus cplus pmin →
      ∃ PF : FullDataLaw J,
        FullDataClampModel PF beta kappa L cminus cplus pmin deltaBar ∧
          PF.observedMargin = P := by
    intro P hP
    exact exists_fullData_holder_lift P hP hJ hpmin hdeltaBar
  refine ⟨hsurj, ?_⟩
  intro n delta hdelta
  have htarget (PF : FullDataLaw J)
      (hPF : FullDataClampModel PF beta kappa L cminus cplus pmin deltaBar) :
      causalClampMean PF delta = clampFunctional PF.observedMargin delta :=
    ((causal_bridge J beta kappa L cminus cplus pmin deltaBar alpha PF hPF hreg).2.2
      delta hdelta).2.2.2
  constructor
  · unfold causalFrontierCriteria observedMinimaxRisk
    apply congrArg sInf
    ext r
    constructor
    · rintro ⟨est, hm, hrange, rfl⟩
      refine ⟨est, hm, hrange, ?_⟩
      apply congrArg sSup
      ext v
      constructor
      · rintro ⟨PF, hPF, rfl⟩
        refine ⟨PF.observedMargin, hPF.observedModel, ?_⟩
        unfold causalEstimatorRisk estimatorRisk
        rw [htarget PF hPF]
      · rintro ⟨P, hP, rfl⟩
        obtain ⟨PF, hPF, hmargin⟩ := hsurj P hP
        refine ⟨PF, hPF, ?_⟩
        unfold causalEstimatorRisk estimatorRisk
        rw [htarget PF hPF, hmargin]
    · rintro ⟨est, hm, hrange, rfl⟩
      refine ⟨est, hm, hrange, ?_⟩
      apply congrArg sSup
      ext v
      constructor
      · rintro ⟨P, hP, rfl⟩
        obtain ⟨PF, hPF, hmargin⟩ := hsurj P hP
        refine ⟨PF, hPF, ?_⟩
        unfold causalEstimatorRisk estimatorRisk
        rw [htarget PF hPF, hmargin]
      · rintro ⟨PF, hPF, rfl⟩
        refine ⟨PF.observedMargin, hPF.observedModel, ?_⟩
        unfold causalEstimatorRisk estimatorRisk
        rw [htarget PF hPF]
  · unfold causalFrontierCriteria observedMinimaxLength UniformCoverage
    apply congrArg sInf
    ext r
    constructor
    · rintro ⟨C, hm, hcov, rfl⟩
      refine ⟨C, ⟨hm, ?_⟩, ?_⟩
      · intro P hP
        obtain ⟨PF, hPF, hmargin⟩ := hsurj P hP
        simpa only [hmargin, htarget PF hPF] using hcov PF hPF
      · apply congrArg sSup
        ext v
        constructor
        · rintro ⟨PF, hPF, rfl⟩
          exact ⟨PF.observedMargin, hPF.observedModel, rfl⟩
        · rintro ⟨P, hP, rfl⟩
          obtain ⟨PF, hPF, hmargin⟩ := hsurj P hP
          exact ⟨PF, hPF, by rw [hmargin]⟩
    · rintro ⟨C, ⟨hm, hcov⟩, rfl⟩
      refine ⟨C, hm, ?_, ?_⟩
      · intro PF hPF
        simpa only [htarget PF hPF] using hcov PF.observedMargin hPF.observedModel
      · apply congrArg sSup
        ext v
        constructor
        · rintro ⟨P, hP, rfl⟩
          obtain ⟨PF, hPF, hmargin⟩ := hsurj P hP
          exact ⟨PF, hPF, by rw [hmargin]⟩
        · rintro ⟨PF, hPF, rfl⟩
          exact ⟨PF.observedMargin, hPF.observedModel, rfl⟩

/-- Conditional on the same disclosed gate, the observed-margin map is onto
for the continuity-only class and its observed and causal criteria agree. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
-- @node: prop:continuity-observed-margin-surjectivity
theorem continuity_observed_margin_surjectivity
    (StandardBorelRegularConditionalLaw_of_gate :
      StandardBorelRegularConditionalLaw)
    (J : ℕ)
    (kappa cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : ContRegimeConstants J kappa cminus cplus pmin deltaBar alpha) :
    (∀ (P : ClampLaw J), ContClampModel P kappa cminus cplus pmin deltaBar →
      ∃ PF : FullDataLaw J,
        ContFullDataClampModel PF kappa cminus cplus pmin deltaBar ∧
          PF.observedMargin = P) ∧
    ∀ (n : ℕ) (delta : ℝ), delta ∈ Set.Icc (0 : ℝ) deltaBar →
      let crit := contFrontierCriteria J n kappa cminus cplus pmin
        deltaBar delta alpha
      crit.2.2.1 = crit.1 ∧ crit.2.2.2 = crit.2.1 := by
  rcases hreg.1 with ⟨hJ, hkappa, hcminus, hcminus_le, hcplus,
    hpmin, hpmin_le, hdeltaBar, hdeltaBar_one⟩
  have hdesign : ContDesignConstants J kappa cminus cplus pmin deltaBar :=
    ⟨hJ, hkappa, hcminus, hcminus_le, hcplus, hpmin, hpmin_le,
      hdeltaBar, hdeltaBar_one⟩
  have hsurj : ∀ (P : ClampLaw J),
      ContClampModel P kappa cminus cplus pmin deltaBar →
      ∃ PF : FullDataLaw J,
        ContFullDataClampModel PF kappa cminus cplus pmin deltaBar ∧
          PF.observedMargin = P := by
    intro P hP
    exact exists_fullData_cont_lift P hP hpmin
  refine ⟨hsurj, ?_⟩
  intro n delta hdelta
  have htarget (PF : FullDataLaw J)
      (hPF : ContFullDataClampModel PF kappa cminus cplus pmin deltaBar) :
      causalClampMean PF delta =
        contClampFunctional PF.observedMargin kappa cminus cplus pmin deltaBar
          hPF.observedModel delta :=
    (continuity_causal_bridge J kappa cminus cplus pmin deltaBar PF hPF hdesign).2
      delta hdelta
  dsimp only
  constructor
  · unfold contFrontierCriteria
    apply congrArg sInf
    ext r
    constructor
    · rintro ⟨est, hm, hrange, rfl⟩
      refine ⟨est, hm, hrange, ?_⟩
      apply congrArg sSup
      ext v
      constructor
      · rintro ⟨PF, hPF, rfl⟩
        refine ⟨PF.observedMargin, hPF.observedModel, ?_⟩
        unfold causalEstimatorRisk contEstimatorRisk
        rw [htarget PF hPF]
      · rintro ⟨P, hP, rfl⟩
        obtain ⟨PF, hPF, hmargin⟩ := hsurj P hP
        subst P
        refine ⟨PF, hPF, ?_⟩
        unfold causalEstimatorRisk contEstimatorRisk
        rw [htarget PF hPF]
    · rintro ⟨est, hm, hrange, rfl⟩
      refine ⟨est, hm, hrange, ?_⟩
      apply congrArg sSup
      ext v
      constructor
      · rintro ⟨P, hP, rfl⟩
        obtain ⟨PF, hPF, hmargin⟩ := hsurj P hP
        subst P
        refine ⟨PF, hPF, ?_⟩
        unfold causalEstimatorRisk contEstimatorRisk
        rw [htarget PF hPF]
      · rintro ⟨PF, hPF, rfl⟩
        refine ⟨PF.observedMargin, hPF.observedModel, ?_⟩
        unfold causalEstimatorRisk contEstimatorRisk
        rw [htarget PF hPF]
  · unfold contFrontierCriteria
    apply congrArg sInf
    ext r
    constructor
    · rintro ⟨C, hm, hcov, rfl⟩
      refine ⟨C, hm, ?_, ?_⟩
      · intro P hP
        obtain ⟨PF, hPF, hmargin⟩ := hsurj P hP
        subst P
        simpa only [htarget PF hPF] using hcov PF hPF
      · apply congrArg sSup
        ext v
        constructor
        · rintro ⟨PF, hPF, rfl⟩
          exact ⟨PF.observedMargin, hPF.observedModel, rfl⟩
        · rintro ⟨P, hP, rfl⟩
          obtain ⟨PF, hPF, hmargin⟩ := hsurj P hP
          exact ⟨PF, hPF, by rw [hmargin]⟩
    · rintro ⟨C, hm, hcov, rfl⟩
      refine ⟨C, hm, ?_, ?_⟩
      · intro PF hPF
        simpa only [htarget PF hPF] using hcov PF.observedMargin hPF.observedModel
      · apply congrArg sSup
        ext v
        constructor
        · rintro ⟨P, hP, rfl⟩
          obtain ⟨PF, hPF, hmargin⟩ := hsurj P hP
          exact ⟨PF, hPF, by rw [hmargin]⟩
        · rintro ⟨PF, hPF, rfl⟩
          exact ⟨PF.observedMargin, hPF.observedModel, rfl⟩

/-- Worst-case causal risk of the same observed-sample total-Gram estimator. -/
def causalStabilizedWorstRisk (J n : ℕ) (B : SplitBlocks n)
    (beta kappa L cminus cplus pmin deltaBar delta : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ PF : FullDataLaw J,
    FullDataClampModel PF beta kappa L cminus cplus pmin deltaBar ∧
    v = causalEstimatorRisk (PF := PF) (n := n) (delta := delta)
      (est := fun z => totalGramEstimator B z (ellOf beta) kappa cminus cplus
        delta (infoBandwidth n delta beta kappa deltaBar))}

/-- Worst-case full-data coverage of the same observed-sample interval. -/
def causalStabilizedCoverage (J n : ℕ) (B : SplitBlocks n)
    (beta kappa L cminus cplus pmin deltaBar delta alpha : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ PF : FullDataLaw J,
    FullDataClampModel PF beta kappa L cminus cplus pmin deltaBar ∧
    v = (iidProduct PF.observedMargin n).real
      {z | causalClampMean (PF := PF) (delta := delta) ∈
        stabilizedInterval B beta kappa L cminus cplus deltaBar delta alpha z}}

/-- Worst-case full-data expected length of that interval, as an extended
expectation so a non-integrable length contributes `∞`. -/
def causalStabilizedWorstLength (J n : ℕ) (B : SplitBlocks n)
    (beta kappa L cminus cplus pmin deltaBar delta alpha : ℝ) : ℝ≥0∞ :=
  sSup {v : ℝ≥0∞ | ∃ PF : FullDataLaw J,
    FullDataClampModel PF beta kappa L cminus cplus pmin deltaBar ∧
    v = ∫⁻ z, intervalLengthENNReal
        (stabilizedInterval B beta kappa L cminus cplus deltaBar delta alpha z)
        ∂iidProduct PF.observedMargin n}

/-- The convex-hull length of a closed real interval is its nonnegative
endpoint difference, including the empty-interval case. [This is the stated conclusion](goal).
-/
-- @node: intervalLength_Icc_eq
lemma intervalLength_Icc_eq (a b : ℝ) :
    intervalLength (Set.Icc a b) = max 0 (b - a) := by
  unfold intervalLength
  by_cases h : a ≤ b
  · simp [h]
  · have h' : b < a := lt_of_not_ge h
    simp [Set.Icc_eq_empty h, h'.le]

/-- The sample-dependent per-stratum radius is measurable. [This is the stated conclusion](goal).
-/
-- @node: stratumRadius_measurable
lemma stratumRadius_measurable {J n ell : ℕ} (B : SplitBlocks n) (x : Fin J)
    (beta kappa L cminus cplus delta h tAlpha b1 : ℝ) :
    Measurable fun z : Fin n → ClampObs J =>
      stratumRadius B z x ell beta kappa L cminus cplus delta h tAlpha b1 := by
  classical
  unfold stratumRadius
  refine Measurable.ite (goodGramEvent_measurable B x kappa cminus cplus delta h) ?_ ?_
  · have habs := Finset.measurable_fun_sum B.I2 fun i _ =>
      (interceptWeight_measurable (ell := ell) B x kappa cminus cplus delta h i).abs
    have hsq := Finset.measurable_fun_sum B.I2 fun i _ =>
      (interceptWeight_measurable (ell := ell) B x kappa cminus cplus delta h i).pow_const 2
    exact (((atomEstimate_measurable B x delta).add measurable_const).mul
      (((measurable_const.mul measurable_const).mul habs).add
        (measurable_const.mul hsq.sqrt))).add measurable_const
  · exact (atomEstimate_measurable B x delta).add measurable_const

/-- Once all three blocks are nonempty, the total displayed confidence radius
is nonnegative under the declared parameter restrictions. The result uses [the `hreg` condition](hyp:hreg), [the `hn` condition](hyp:hn), [the `hh` condition](hyp:hh). [This is the stated conclusion](goal).
-/
-- @node: stabilizedInterval_radius_nonneg
lemma stabilizedInterval_radius_nonneg
    (J n : ℕ) (B : SplitBlocks n)
    (beta kappa L cminus cplus pmin deltaBar alpha delta h : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha)
    (hn : 4 ≤ n) (hh : 0 ≤ h) :
    ∀ z : Fin n → ClampObs J,
      let tAlpha := Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2)
      let b0 := tAlpha / Real.sqrt (B.I0.card : ℝ)
      let b1 := tAlpha / Real.sqrt (B.I1.card : ℝ)
      0 ≤ b0 + ∑ x : Fin J,
        stratumRadius B z x (ellOf beta) beta kappa L cminus cplus delta h tAlpha b1 := by
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

/-- Length of the displayed bias-aware interval is measurable as a function
of the observed sample. [This is the stated conclusion](goal).
-/
-- @node: stabilizedInterval_length_measurable
lemma stabilizedInterval_length_measurable (J n : ℕ) (B : SplitBlocks n)
    (beta kappa L cminus cplus deltaBar delta alpha : ℝ) :
    Measurable fun z : Fin n → ClampObs J =>
      intervalLength (stabilizedInterval B beta kappa L cminus cplus deltaBar delta alpha z) := by
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
  have hc : Measurable center := totalGramEstimator_measurable B kappa cminus cplus delta _
  have hr : Measurable radius := measurable_const.add
    (Finset.measurable_fun_sum _ fun x _ =>
      stratumRadius_measurable B x beta kappa L cminus cplus delta _ tAlpha b1)
  have hlo : Measurable fun z => max 0 (center z - radius z) :=
    measurable_const.max (hc.sub hr)
  have hhi : Measurable fun z => min 1 (center z + radius z) :=
    measurable_const.min (hc.add hr)
  have hd : Measurable fun z =>
      min 1 (center z + radius z) - max 0 (center z - radius z) := hhi.sub hlo
  have hm : Measurable fun z =>
      max 0 (min 1 (center z + radius z) - max 0 (center z - radius z)) :=
    measurable_const.max hd
  simpa only [stabilizedInterval, honestInterval, intervalLength_Icc_eq,
    center, radius, tAlpha, b0, b1] using hm

/-- For sufficiently large samples the displayed endpoints are ordered and
measurable, hence the bias-aware construction is an admissible observed
confidence procedure. The result uses [the `hreg` condition](hyp:hreg), [the `hn` condition](hyp:hn), [the `hh` condition](hyp:hh). [This is the stated conclusion](goal).
-/
-- @node: stabilizedInterval_observedMeasurable
lemma stabilizedInterval_observedMeasurable
    (J n : ℕ) (B : SplitBlocks n)
    (beta kappa L cminus cplus pmin deltaBar alpha delta : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha)
    (hn : 4 ≤ n)
    (hh : 0 ≤ infoBandwidth n delta beta kappa deltaBar) :
    ObservedMeasurableInterval
      (stabilizedInterval (J := J) B beta kappa L cminus cplus deltaBar delta alpha) := by
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
  have hc : Measurable center := totalGramEstimator_measurable B kappa cminus cplus delta _
  have hr : Measurable radius := measurable_const.add
    (Finset.measurable_fun_sum _ fun x _ =>
      stratumRadius_measurable B x beta kappa L cminus cplus delta _ tAlpha b1)
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
        stabilizedInterval_radius_nonneg J n B beta kappa L cminus cplus pmin
          deltaBar alpha delta (infoBandwidth n delta beta kappa deltaBar) hreg hn hh z
    dsimp only [lo, hi]
    apply le_min
    · apply max_le
      · norm_num
      · dsimp only [center]
        rw [show totalGramEstimator B z (ellOf beta) kappa cminus cplus delta
          (infoBandwidth n delta beta kappa deltaBar) =
            clampUnit (retainedEstimate B z delta + ∑ x : Fin J,
              atomEstimate B z x delta * localRegressionEstimate B z x (ellOf beta)
                kappa cminus cplus delta
                  (infoBandwidth n delta beta kappa deltaBar)) by rfl]
        linarith [hcenter.2]
    · apply max_le
      · dsimp only [center]
        rw [show totalGramEstimator B z (ellOf beta) kappa cminus cplus delta
          (infoBandwidth n delta beta kappa deltaBar) =
            clampUnit (retainedEstimate B z delta + ∑ x : Fin J,
              atomEstimate B z x delta * localRegressionEstimate B z x (ellOf beta)
                kappa cminus cplus delta
                  (infoBandwidth n delta beta kappa deltaBar)) by rfl]
        linarith [hcenter.1]
      · linarith
  · intro z
    rfl

/-- Intersecting the bias-aware interval with the outcome range bounds its
convex-hull length by one on every sample. [This is the stated conclusion](goal).
-/
-- @node: stabilizedInterval_length_le_one
lemma stabilizedInterval_length_le_one (J n : ℕ) (B : SplitBlocks n)
    (beta kappa L cminus cplus deltaBar delta alpha : ℝ)
    (z : Fin n → ClampObs J) :
    intervalLength (stabilizedInterval B beta kappa L cminus cplus deltaBar delta alpha z) ≤ 1 := by
  simp only [stabilizedInterval, honestInterval, intervalLength_Icc_eq]
  apply max_le
  · norm_num
  · have hmin := min_le_left (1 : ℝ)
        (totalGramEstimator B z (ellOf beta) kappa cminus cplus delta
          (infoBandwidth n delta beta kappa deltaBar) +
          (Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2) /
              Real.sqrt (B.I0.card : ℝ) + ∑ x : Fin J,
            stratumRadius B z x (ellOf beta) beta kappa L cminus cplus delta
              (infoBandwidth n delta beta kappa deltaBar)
              (Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2))
              (Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2) /
                Real.sqrt (B.I1.card : ℝ))))
    have hmax := le_max_left (0 : ℝ)
        (totalGramEstimator B z (ellOf beta) kappa cminus cplus delta
          (infoBandwidth n delta beta kappa deltaBar) -
          (Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2) /
              Real.sqrt (B.I0.card : ℝ) + ∑ x : Fin J,
            stratumRadius B z x (ellOf beta) beta kappa L cminus cplus delta
              (infoBandwidth n delta beta kappa deltaBar)
              (Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2))
              (Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2) /
                Real.sqrt (B.I1.card : ℝ))))
    linarith

/-- A real expected-length bound for the concrete interval upgrades to the
extended expected-length convention used by the minimax criteria. The result uses [the `hupper` condition](hyp:hupper). [This is the stated conclusion](goal).
-/
-- @node: confidenceWorstLength_stabilizedInterval_le_ofReal
lemma confidenceWorstLength_stabilizedInterval_le_ofReal
    (J n : ℕ) (B : SplitBlocks n)
    (beta kappa L cminus cplus pmin deltaBar delta alpha U : ℝ)
    (hupper : stabilizedWorstLength J n B beta kappa L cminus cplus pmin
      deltaBar delta alpha ≤ U) :
    confidenceWorstLength J n beta kappa L cminus cplus pmin
      (stabilizedInterval B beta kappa L cminus cplus deltaBar delta alpha) ≤
        ENNReal.ofReal U := by
  unfold stabilizedWorstLength at hupper
  unfold confidenceWorstLength
  apply sSup_le
  intro v hv
  rcases hv with ⟨P, hP, rfl⟩
  letI : IsProbabilityMeasure P.dataMeasure := hP.probability
  letI : IsProbabilityMeasure (iidProduct P n) := by
    unfold iidProduct
    infer_instance
  let f := fun z : Fin n → ClampObs J =>
    intervalLength (stabilizedInterval B beta kappa L cminus cplus deltaBar delta alpha z)
  have hfmeas : Measurable f :=
    stabilizedInterval_length_measurable J n B beta kappa L cminus cplus deltaBar delta alpha
  have hfnn : ∀ᵐ z ∂iidProduct P n, 0 ≤ f z := ae_of_all _ fun _ => le_max_left _ _
  have hfint : Integrable f (iidProduct P n) := by
    refine Integrable.of_bound hfmeas.aestronglyMeasurable 1 ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    exact stabilizedInterval_length_le_one J n B beta kappa L cminus cplus
      deltaBar delta alpha z
  simp_rw [intervalLengthENNReal]
  rw [← ofReal_integral_eq_lintegral_ofReal hfint hfnn]
  apply ENNReal.ofReal_le_ofReal
  have hbdd : BddAbove {v : ℝ | ∃ Q : ClampLaw J,
      ClampModel Q beta kappa L cminus cplus pmin ∧ IidSampling Q n ∧
      v = ∫ z, intervalLength
        (stabilizedInterval B beta kappa L cminus cplus deltaBar delta alpha z)
          ∂iidProduct Q n} := by
    refine ⟨1, ?_⟩
    rintro w ⟨Q, hQ, _hiid, rfl⟩
    letI : IsProbabilityMeasure Q.dataMeasure := hQ.probability
    letI : IsProbabilityMeasure (iidProduct Q n) := by
      unfold iidProduct
      infer_instance
    have hqmeas := stabilizedInterval_length_measurable J n B beta kappa L cminus
      cplus deltaBar delta alpha
    have hqint : Integrable (fun z : Fin n → ClampObs J =>
        intervalLength (stabilizedInterval B beta kappa L cminus cplus deltaBar delta alpha z))
        (iidProduct Q n) := by
      refine Integrable.of_bound hqmeas.aestronglyMeasurable 1 ?_
      filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
      exact stabilizedInterval_length_le_one J n B beta kappa L cminus cplus
        deltaBar delta alpha z
    have hmono := integral_mono_ae hqint (integrable_const 1)
      (ae_of_all _ fun z => stabilizedInterval_length_le_one J n B beta kappa L
        cminus cplus deltaBar delta alpha z)
    simpa using hmono
  have hmem : (∫ z, f z ∂iidProduct P n) ∈ {v : ℝ | ∃ Q : ClampLaw J,
      ClampModel Q beta kappa L cminus cplus pmin ∧ IidSampling Q n ∧
      v = ∫ z, intervalLength
        (stabilizedInterval B beta kappa L cminus cplus deltaBar delta alpha z)
          ∂iidProduct Q n} := ⟨P, hP, clampModel_iidSampling hP, rfl⟩
  exact (le_csSup hbdd hmem).trans hupper

/-- Any uniformly honest concrete interval upper-bounds the observed minimax
expected length by its own worst-case length. The result uses [the `hC` condition](hyp:hC). [This is the stated conclusion](goal).
-/
-- @node: observedMinimaxLength_le_confidenceWorstLength
lemma observedMinimaxLength_le_confidenceWorstLength
    (J n : ℕ) (beta kappa L cminus cplus pmin delta alpha : ℝ)
    (C : ConfidenceProcedure n J)
    (hC : UniformCoverage J n beta kappa L cminus cplus pmin delta alpha C) :
    observedMinimaxLength J n beta kappa L cminus cplus pmin delta alpha ≤
      confidenceWorstLength J n beta kappa L cminus cplus pmin C := by
  unfold observedMinimaxLength confidenceWorstLength
  apply sInf_le
  exact ⟨C, hC, rfl⟩

/-- Surjectivity and identification transport the concrete estimator's
worst-case risk from the observed class to the full-data class. The result uses [the `hreg` condition](hyp:hreg), [the `hdelta` condition](hyp:hdelta). [This is the stated conclusion](goal).
-/
-- @node: causalStabilizedWorstRisk_eq_observed
lemma causalStabilizedWorstRisk_eq_observed
    (StandardBorelRegularConditionalLaw_of_gate :
      StandardBorelRegularConditionalLaw)
    (J n : ℕ) (B : SplitBlocks n)
    (beta kappa L cminus cplus pmin deltaBar alpha delta : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar) :
    causalStabilizedWorstRisk J n B beta kappa L cminus cplus pmin deltaBar delta =
      stabilizedWorstRisk J n B beta kappa L cminus cplus pmin deltaBar delta := by
  have hsurj := (observed_margin_surjectivity
    StandardBorelRegularConditionalLaw_of_gate J beta kappa L cminus cplus pmin
      deltaBar alpha hreg).1
  unfold causalStabilizedWorstRisk stabilizedWorstRisk
  congr 1
  ext v
  constructor
  · rintro ⟨PF, hPF, rfl⟩
    have hbridge := (causal_bridge J beta kappa L cminus cplus pmin deltaBar alpha
      PF hPF hreg).2.2 delta hdelta
    refine ⟨PF.observedMargin, hPF.observedModel,
      clampModel_iidSampling hPF.observedModel, ?_⟩
    simp only [causalEstimatorRisk, estimatorRisk, stabilizedEstimatorRisk,
      hbridge.2.2.2]
  · rintro ⟨P, hP, _hiid, rfl⟩
    rcases hsurj P hP with ⟨PF, hPF, rfl⟩
    have hbridge := (causal_bridge J beta kappa L cminus cplus pmin deltaBar alpha
      PF hPF hreg).2.2 delta hdelta
    refine ⟨PF, hPF, ?_⟩
    simp only [causalEstimatorRisk, estimatorRisk, stabilizedEstimatorRisk,
      hbridge.2.2.2]

/-- Surjectivity and identification transport coverage of the concrete
bias-aware interval. The result uses [the `hreg` condition](hyp:hreg), [the `hdelta` condition](hyp:hdelta). [This is the stated conclusion](goal).
-/
-- @node: causalStabilizedCoverage_eq_observed
lemma causalStabilizedCoverage_eq_observed
    (StandardBorelRegularConditionalLaw_of_gate :
      StandardBorelRegularConditionalLaw)
    (J n : ℕ) (B : SplitBlocks n)
    (beta kappa L cminus cplus pmin deltaBar alpha delta : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar) :
    causalStabilizedCoverage J n B beta kappa L cminus cplus pmin deltaBar delta alpha =
      stabilizedCoverage J n B beta kappa L cminus cplus pmin deltaBar delta alpha := by
  have hsurj := (observed_margin_surjectivity
    StandardBorelRegularConditionalLaw_of_gate J beta kappa L cminus cplus pmin
      deltaBar alpha hreg).1
  unfold causalStabilizedCoverage stabilizedCoverage
  congr 1
  ext v
  constructor
  · rintro ⟨PF, hPF, rfl⟩
    have hbridge := (causal_bridge J beta kappa L cminus cplus pmin deltaBar alpha
      PF hPF hreg).2.2 delta hdelta
    refine ⟨PF.observedMargin, hPF.observedModel,
      clampModel_iidSampling hPF.observedModel, ?_⟩
    congr 2
    ext z
    simp only [hbridge.2.2.2]
  · rintro ⟨P, hP, _hiid, rfl⟩
    rcases hsurj P hP with ⟨PF, hPF, rfl⟩
    have hbridge := (causal_bridge J beta kappa L cminus cplus pmin deltaBar alpha
      PF hPF hreg).2.2 delta hdelta
    refine ⟨PF, hPF, ?_⟩
    congr 2
    ext z
    simp only [hbridge.2.2.2]

/-- Expected interval length depends only on the observed margin, so
surjectivity transports its worst case without any target calculation. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
-- @node: causalStabilizedWorstLength_eq_confidenceWorstLength
lemma causalStabilizedWorstLength_eq_confidenceWorstLength
    (StandardBorelRegularConditionalLaw_of_gate :
      StandardBorelRegularConditionalLaw)
    (J n : ℕ) (B : SplitBlocks n)
    (beta kappa L cminus cplus pmin deltaBar alpha delta : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha) :
    causalStabilizedWorstLength J n B beta kappa L cminus cplus pmin deltaBar delta alpha =
      confidenceWorstLength J n beta kappa L cminus cplus pmin
        (stabilizedInterval B beta kappa L cminus cplus deltaBar delta alpha) := by
  have hsurj := (observed_margin_surjectivity
    StandardBorelRegularConditionalLaw_of_gate J beta kappa L cminus cplus pmin
      deltaBar alpha hreg).1
  unfold causalStabilizedWorstLength confidenceWorstLength
  congr 1
  ext v
  constructor
  · rintro ⟨PF, hPF, rfl⟩
    exact ⟨PF.observedMargin, hPF.observedModel, rfl⟩
  · rintro ⟨P, hP, rfl⟩
    rcases hsurj P hP with ⟨PF, hPF, rfl⟩
    exact ⟨PF, hPF, rfl⟩

/-- Identification transports both observed brackets to the full-data class;
the same observed estimator and interval attain both causal frontiers. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
-- @node: thm:causal-frontier-lift
theorem causal_frontier_lift
    (J : ℕ)
    (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha) :
    ∃ c C : ℝ, 0 < c ∧ c < C ∧
    ∀ (deltaSeq : ℕ → ℝ), ThresholdSequence deltaBar deltaSeq →
    ∀ Bseq : ∀ n, SplitBlocks n,
      ∀ᶠ n in atTop,
        let delta := deltaSeq n
        let h := infoBandwidth n delta beta kappa deltaBar
        let r := clampFrontier n delta kappa h beta
        let crit := causalFrontierCriteria J n beta kappa L cminus cplus
          pmin deltaBar delta alpha
        ObservedMeasurableEstimator (n := n) (J := J)
          (fun z : Fin n → ClampObs J =>
            totalGramEstimator (Bseq n) z (ellOf beta) kappa cminus cplus delta h) ∧
        ObservedMeasurableInterval (n := n) (J := J)
          (stabilizedInterval (J := J) (Bseq n) beta kappa L cminus cplus deltaBar
            delta alpha) ∧
        c * r ≤ crit.1 ∧
        crit.1 ≤ causalStabilizedWorstRisk J n (Bseq n) beta kappa L
          cminus cplus pmin deltaBar delta ∧
        causalStabilizedWorstRisk J n (Bseq n) beta kappa L
          cminus cplus pmin deltaBar delta ≤ C * r ∧
        1 - alpha ≤ causalStabilizedCoverage J n (Bseq n) beta kappa L
          cminus cplus pmin deltaBar delta alpha ∧
        causalStabilizedWorstLength J n (Bseq n) beta kappa L
          cminus cplus pmin deltaBar delta alpha ≤ ENNReal.ofReal (C * r) ∧
        ENNReal.ofReal (c * r) ≤ crit.2 ∧
        crit.2 ≤ ENNReal.ofReal (C * r) := by
  rcases hreg with ⟨hJ, hbeta, hkappa, hL, hcminus, hcminus_le, hcplus,
    hpmin, hpmin_le, hdeltaBar, hdeltaBar1, halpha, halpha_half⟩
  have hreg' : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha :=
    ⟨hJ, hbeta, hkappa, hL, hcminus, hcminus_le, hcplus, hpmin, hpmin_le,
      hdeltaBar, hdeltaBar1, halpha, halpha_half⟩
  have hgate : StandardBorelRegularConditionalLaw.{0, 0} := by
    exact standardBorelRegularConditionalLaw_mathlib.{0, 0}
  rcases clamp_minimax_risk J beta kappa L cminus cplus pmin deltaBar alpha hreg' with
    ⟨cRisk, CRisk, amplitude, hcRisk, hcRiskC, hamp, hamp_le, hRisk⟩
  rcases honest_coverage_and_length J beta kappa L cminus cplus pmin deltaBar alpha
      hreg' with ⟨cLen, CLen, hcLen, hcLenC, hLength⟩
  let c := min cRisk cLen
  let C := max CRisk CLen
  have hc : 0 < c := lt_min hcRisk hcLen
  have hcC : c < C :=
    lt_of_le_of_lt (min_le_left _ _) (hcRiskC.trans_le (le_max_left _ _))
  refine ⟨c, C, hc, hcC, ?_⟩
  intro deltaSeq hdeltaSeq Bseq
  have hBand := infoBandwidth_eventually_balance beta kappa deltaBar hbeta hkappa
    ⟨hdeltaBar, hdeltaBar1⟩ deltaSeq hdeltaSeq
  have hRisk' := hRisk deltaSeq hdeltaSeq Bseq
  have hLength' := hLength deltaSeq hdeltaSeq Bseq
  filter_upwards [hRisk', hLength', hBand, eventually_ge_atTop 4] with
    n hnRisk hnLength hnBand hn4
  dsimp only at hnRisk hnLength ⊢
  let delta := deltaSeq n
  let h := infoBandwidth n delta beta kappa deltaBar
  let r := clampFrontier n delta kappa h beta
  have hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar := hdeltaSeq n
  have hupper : delta + infoBandwidth n delta beta kappa deltaBar ≤ 1 := by
    dsimp [delta]
    linarith [hdelta.2, hnBand.2.1]
  have hr : 0 ≤ r := by
    dsimp [r, clampFrontier, h, delta]
    exact add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (mul_nonneg (Real.rpow_nonneg hdelta.1 _)
        (Real.rpow_nonneg hnBand.1.le _))
  have hcRisk' : c ≤ cRisk := min_le_left _ _
  have hcLen' : c ≤ cLen := min_le_right _ _
  have hCRisk : CRisk ≤ C := le_max_left _ _
  have hCLen : CLen ≤ C := le_max_right _ _
  have hcrit := (observed_margin_surjectivity
    hgate J beta kappa L cminus cplus pmin
      deltaBar alpha hreg').2 n delta hdelta
  have hriskEq := causalStabilizedWorstRisk_eq_observed
    hgate J n (Bseq n) beta kappa L cminus
      cplus pmin deltaBar alpha delta hreg' hdelta
  have hcovEq := causalStabilizedCoverage_eq_observed
    hgate J n (Bseq n) beta kappa L cminus
      cplus pmin deltaBar alpha delta hreg' hdelta
  have hmeasEst : ObservedMeasurableEstimator
      (fun z : Fin n → ClampObs J =>
        totalGramEstimator (Bseq n) z (ellOf beta) kappa cminus cplus delta h) := by
    exact totalGramEstimator_measurable (Bseq n) kappa cminus cplus delta h
  have hmeasInt := stabilizedInterval_observedMeasurable J n (Bseq n) beta kappa L
    cminus cplus pmin deltaBar alpha delta hreg' hn4 hnBand.1.le
  have huniform := stabilizedInterval_uniformCoverage J n (Bseq n) beta kappa L
    cminus cplus pmin deltaBar delta alpha hreg' hn4 hdelta hnBand.1
      hupper
  have hlenExt := confidenceWorstLength_stabilizedInterval_le_ofReal J n (Bseq n)
    beta kappa L cminus cplus pmin deltaBar delta alpha (CLen * r)
      hnLength.2.2.1
  have hlenC : confidenceWorstLength J n beta kappa L cminus cplus pmin
      (stabilizedInterval (Bseq n) beta kappa L cminus cplus deltaBar delta alpha) ≤
        ENNReal.ofReal (C * r) :=
    hlenExt.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCLen hr))
  have hminUpper := observedMinimaxLength_le_confidenceWorstLength J n beta kappa L
    cminus cplus pmin delta alpha _ huniform
  refine ⟨hmeasEst, hmeasInt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcrit.1]
    exact (mul_le_mul_of_nonneg_right hcRisk' hr).trans hnRisk.1
  · rw [hcrit.1, hriskEq]
    exact hnRisk.2.1
  · rw [hriskEq]
    exact hnRisk.2.2.1.trans (mul_le_mul_of_nonneg_right hCRisk hr)
  · rw [hcovEq]
    exact hnLength.1
  · rw [causalStabilizedWorstLength_eq_confidenceWorstLength
      hgate J n (Bseq n) beta kappa L cminus
        cplus pmin deltaBar alpha delta hreg']
    exact hlenC
  · rw [hcrit.2]
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcLen' hr)).trans
      hnLength.2.2.2.1
  · rw [hcrit.2]
    exact hminUpper.trans hlenC

end


end CausalSmith.Stat.LmtpThresholdAtomFrontier

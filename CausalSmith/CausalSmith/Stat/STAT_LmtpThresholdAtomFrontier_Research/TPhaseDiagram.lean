/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.FixedPositive

/-!
# Four-regime threshold phase diagram

This module assembles the rate comparisons and the zero-threshold reduction.
-/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open Filter MeasureTheory Set Topology

noncomputable section

/-- At the identity threshold, the stabilized interval is eventually uniformly
honest over the bounded-outcome model. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
lemma zero_threshold_stabilizedCoverage_eventually
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha) :
    ∀ Bseq : ∀ n, SplitBlocks n,
      ∀ᶠ n in atTop,
        1 - alpha ≤ stabilizedCoverage J n (Bseq n) beta kappa L cminus cplus
          pmin deltaBar 0 alpha := by
  rcases honest_coverage_and_length J beta kappa L cminus cplus pmin deltaBar
    alpha hreg with ⟨c, C, hc, hcC, hlength⟩
  have hzero : ThresholdSequence deltaBar (fun _ => 0) := by
    intro n
    exact ⟨le_rfl, hreg.2.2.2.2.2.2.2.2.2.1.le⟩
  intro Bseq
  filter_upwards [hlength (fun _ => 0) hzero Bseq] with n hn
  exact hn.1

/-- At the identity threshold, the bias-aware interval's worst-case expected
length inherits the root-sample-size sandwich from the honest-length theorem. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
-- @node: zero_threshold_stabilizedWorstLength_asymp
lemma zero_threshold_stabilizedWorstLength_asymp
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha) :
    ∀ Bseq : ∀ n, SplitBlocks n,
      AsympSeq
        (fun n => stabilizedWorstLength J n (Bseq n) beta kappa L cminus cplus
          pmin deltaBar 0 alpha)
        (fun n => (n : ℝ) ^ (-(1 : ℝ) / 2)) := by
  rcases honest_coverage_and_length J beta kappa L cminus cplus pmin deltaBar
    alpha hreg with ⟨c, C, hc, hcC, hlength⟩
  have hzero : ThresholdSequence deltaBar (fun _ => 0) := by
    intro n
    exact ⟨le_rfl, hreg.2.2.2.2.2.2.2.2.2.1.le⟩
  intro Bseq
  refine ⟨c, C, hc, hcC.le, ?_⟩
  filter_upwards [hlength (fun _ => 0) hzero Bseq] with n hn
  dsimp at hn
  have hfront :
      clampFrontier n 0 kappa (infoBandwidth n 0 beta kappa deltaBar) beta =
        (n : ℝ) ^ (-(1 : ℝ) / 2) := by
    simp [clampFrontier,
      Real.zero_rpow (by linarith [hreg.2.2.1] : kappa + 1 ≠ 0)]
  rw [hfront] at hn
  exact ⟨hn.2.1, hn.2.2.1⟩

/-- The critical scale is separated from the design-edge scale; below, at, and
above it the frontier has the four rates stated in the paper. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
-- @node: thm:phase-diagram
theorem clamp_phase_diagram
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha) :
    Tendsto (fun n => deltaCrit n beta kappa / deltaEdge n beta kappa)
      atTop atTop ∧
    ∀ (deltaSeq : ℕ → ℝ), ThresholdSequence deltaBar deltaSeq →
      let hSeq := fun n => infoBandwidth n (deltaSeq n) beta kappa deltaBar
      let atomSeq := fun n =>
        (deltaSeq n) ^ (kappa + 1) * (hSeq n) ^ beta
      let rSeq := fun n => clampFrontier n (deltaSeq n) kappa (hSeq n) beta
      (Tendsto (fun n => deltaSeq n / deltaCrit n beta kappa) atTop (nhds 0) →
        AsympSeq rSeq (fun n => (n : ℝ) ^ (-(1 : ℝ) / 2))) ∧
      (∀ c0 : ℝ, 0 < c0 →
        Tendsto (fun n => deltaSeq n / deltaCrit n beta kappa) atTop (nhds c0) →
        AsympSeq atomSeq (fun n => (n : ℝ) ^ (-(1 : ℝ) / 2)) ∧
        AsympSeq rSeq (fun n => (n : ℝ) ^ (-(1 : ℝ) / 2))) ∧
      (Tendsto (fun n => deltaSeq n / deltaCrit n beta kappa) atTop atTop →
        Tendsto deltaSeq atTop (nhds 0) →
        AsympSeq rSeq (fun n =>
          (deltaSeq n) ^ (kappa + 1) *
            ((n : ℝ) * (deltaSeq n) ^ kappa) ^
              (-beta / (2 * beta + 1)))) ∧
      (∀ delta0 : ℝ, delta0 ∈ Set.Ioc (0 : ℝ) deltaBar →
        Tendsto deltaSeq atTop (nhds delta0) →
        AsympSeq rSeq (fun n => (n : ℝ) ^ (-beta / (2 * beta + 1)))) ∧
      (∀ (n : ℕ) (P : ClampLaw J),
        ClampModel P beta kappa L cminus cplus pmin →
        (∀ x : Fin J, atomMass P x 0 = 0) ∧
        clampFunctional P 0 = ∫ o, o.Y ∂P.dataMeasure ∧
        clampFrontier n 0 kappa (infoBandwidth n 0 beta kappa deltaBar) beta =
          (n : ℝ) ^ (-(1 : ℝ) / 2)) ∧
      (∀ (n : ℕ) (P : ClampLaw J) (B : SplitBlocks n),
        ClampModel P beta kappa L cminus cplus pmin →
        let h := infoBandwidth n 0 beta kappa deltaBar
        (fun z : Fin n → ClampObs J =>
          totalGramEstimator B z (ellOf beta) kappa cminus cplus 0 h) =ᵐ[iidProduct P n]
        (fun z => clampUnit (blockAverage B.I0 z (fun o => o.Y)))) ∧
      ∀ Bseq : ∀ n, SplitBlocks n,
        (∀ᶠ n in atTop,
          1 - alpha ≤ stabilizedCoverage J n (Bseq n) beta kappa L cminus cplus
            pmin deltaBar 0 alpha) ∧
        AsympSeq
          (fun n => stabilizedWorstRisk J n (Bseq n) beta kappa L cminus cplus
            pmin deltaBar 0)
          (fun n => (n : ℝ) ^ (-(1 : ℝ) / 2)) ∧
        AsympSeq
          (fun n => stabilizedWorstLength J n (Bseq n) beta kappa L cminus cplus
            pmin deltaBar 0 alpha)
          (fun n => (n : ℝ) ^ (-(1 : ℝ) / 2)) := by
  refine ⟨critical_scale_div_edge_scale_tendsto_top J beta kappa L cminus cplus
    pmin deltaBar alpha hreg, ?_⟩
  intro deltaSeq hdelta
  dsimp
  refine ⟨regular_frontier_asymp J beta kappa L cminus cplus pmin deltaBar
      alpha hreg deltaSeq hdelta, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c0 hc0 hratio
    exact critical_atom_and_frontier_asymp J beta kappa L cminus cplus pmin
      deltaBar alpha c0 hreg hc0 deltaSeq hdelta hratio
  · intro hratio _hzero
    exact supercritical_frontier_asymp J beta kappa L cminus cplus pmin
      deltaBar alpha hreg deltaSeq hdelta hratio
  · intro delta0 hdelta0 htend
    exact fixed_positive_frontier_asymp J beta kappa L cminus cplus pmin
      deltaBar alpha delta0 hreg hdelta0.1 deltaSeq hdelta htend
  · intro n P hmodel
    refine ⟨(zero_threshold_atom_and_frontier J n P beta kappa deltaBar
      hreg.2.2.1).1, zero_threshold_functional J P beta kappa L cminus cplus
        pmin hmodel, ?_⟩
    exact (zero_threshold_atom_and_frontier J n P beta kappa deltaBar
      hreg.2.2.1).2
  · intro n P B hmodel
    exact zero_threshold_totalGramEstimator J n P B beta kappa L cminus cplus
      pmin deltaBar hmodel
  · intro Bseq
    exact ⟨zero_threshold_stabilizedCoverage_eventually J beta kappa L cminus
      cplus pmin deltaBar alpha hreg Bseq,
      zero_threshold_stabilizedWorstRisk_asymp J beta kappa L cminus cplus
        pmin deltaBar alpha hreg Bseq,
      zero_threshold_stabilizedWorstLength_asymp J beta kappa L cminus cplus
        pmin deltaBar alpha hreg Bseq⟩

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier

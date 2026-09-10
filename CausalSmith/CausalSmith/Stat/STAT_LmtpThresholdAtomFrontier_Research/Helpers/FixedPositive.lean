/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.PhaseRates

/-!
# Fixed-positive-threshold frontier

This module closes the fixed-threshold branch from the moving-threshold rate lemmas.
-/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open Filter MeasureTheory Set Topology

noncomputable section

/-- If the threshold converges to a positive constant, the actual frontier has
the fixed-threshold nonparametric order. The result uses [the `hreg` condition](hyp:hreg), [the `hdelta0` condition](hyp:hdelta0), [the `hdelta` condition](hyp:hdelta), [the `htend` condition](hyp:htend). [This is the stated conclusion](goal).
-/
-- @node: fixed_positive_frontier_asymp
lemma fixed_positive_frontier_asymp
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha delta0 : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha)
    (hdelta0 : 0 < delta0) (deltaSeq : ℕ → ℝ)
    (hdelta : ThresholdSequence deltaBar deltaSeq)
    (htend : Tendsto deltaSeq atTop (nhds delta0)) :
    AsympSeq
      (fun n => clampFrontier n (deltaSeq n) kappa
        (infoBandwidth n (deltaSeq n) beta kappa deltaBar) beta)
      (fun n => (n : ℝ) ^ (-beta / (2 * beta + 1))) := by
  rcases hreg with ⟨hJ, hbeta, hkappa, hL, hcminus, hcm, hcp, hpmin,
    hpminJ, hdeltaBar_pos, hdeltaBar_lt, halpha, halpha_lt⟩
  have hreg' : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha :=
    ⟨hJ, hbeta, hkappa, hL, hcminus, hcm, hcp, hpmin, hpminJ,
      hdeltaBar_pos, hdeltaBar_lt, halpha, halpha_lt⟩
  have hratio := fixed_positive_threshold_ratio_critical_top J beta kappa L cminus
    cplus pmin deltaBar alpha delta0 hreg' hdelta0 deltaSeq htend
  have hsuper := supercritical_frontier_asymp J beta kappa L cminus cplus pmin
    deltaBar alpha hreg' deltaSeq hdelta hratio
  let a : ℝ := (beta * kappa + 2 * beta + kappa + 1) / (2 * beta + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have hpow : Tendsto (fun n => (deltaSeq n) ^ a) atTop (nhds (delta0 ^ a)) :=
    (Real.continuousAt_rpow_const delta0 a (Or.inr ha.le)).tendsto.comp htend
  have hbase : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) ^ (-beta / (2 * beta + 1)) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hinterior : AsympSeq
      (fun n => (deltaSeq n) ^ (kappa + 1) *
        ((n : ℝ) * (deltaSeq n) ^ kappa) ^ (-beta / (2 * beta + 1)))
      (fun n => (n : ℝ) ^ (-beta / (2 * beta + 1))) := by
    apply asympSeq_of_tendsto_div_pos _ _ (delta0 ^ a)
      (Real.rpow_pos_of_pos hdelta0 _)
    · exact hbase
    · refine hpow.congr' ?_
      filter_upwards [eventually_gt_atTop 0,
        htend (Ioi_mem_nhds hdelta0)] with n hn hd
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      have hexact := atom_interior_scale_exact (n : ℝ) (deltaSeq n) beta kappa
        hnR hd hbeta
      have hflat : ((n : ℝ) * (deltaSeq n) ^ kappa) ^
          (-beta / (2 * beta + 1)) =
          (((n : ℝ) * (deltaSeq n) ^ kappa) ^
            (-(1 : ℝ) / (2 * beta + 1))) ^ beta := by
        rw [← Real.rpow_mul
          (mul_nonneg hnR.le (Real.rpow_nonneg hd.le kappa))]
        congr 1
        ring
      rw [hflat, hexact]
      rw [mul_div_cancel_left₀]
      exact (Real.rpow_pos_of_pos hnR _).ne'
  exact asympSeq_trans hsuper hinterior


end

end CausalSmith.Stat.LmtpThresholdAtomFrontier

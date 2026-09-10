/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.ContinuityCriteriaTransport
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.SurjectivityLift

/-! # Concrete transport of continuity-only decision criteria -/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory Set

noncomputable section

/-- Identification rewrites the causal risk of every observed-sample
estimator as the corresponding continuity-only observed risk. The result uses [the `hreg` condition](hyp:hreg), [the `hdelta` condition](hyp:hdelta), [the `hPF` condition](hyp:hPF). [This is the stated conclusion](goal).
-/
lemma causalEstimatorRisk_eq_contEstimatorRisk
    (J n : ℕ) (kappa cminus cplus pmin deltaBar delta : ℝ)
    (hreg : ContDesignConstants J kappa cminus cplus pmin deltaBar)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar)
    (PF : FullDataLaw J)
    (hPF : ContFullDataClampModel PF kappa cminus cplus pmin deltaBar)
    (est : Estimator n J) :
    causalEstimatorRisk PF n delta est =
      contEstimatorRisk PF.observedMargin n kappa cminus cplus pmin deltaBar
        delta hPF.observedModel est := by
  unfold causalEstimatorRisk contEstimatorRisk
  rw [(continuity_causal_bridge J kappa cminus cplus pmin deltaBar PF hPF
    hreg).2 delta hdelta]

/-- The paper's quantile lift and identification bridge instantiate the
abstract transport interface without importing the later frontier theorem. The result uses [the `hreg` condition](hyp:hreg), [the `hdelta` condition](hyp:hdelta). [This is the stated conclusion](goal).
-/
lemma contFrontierCriteria_observed_causal_eq
    (J n : ℕ) (kappa cminus cplus pmin deltaBar delta alpha : ℝ)
    (hreg : ContRegimeConstants J kappa cminus cplus pmin deltaBar alpha)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar) :
    let crit := contFrontierCriteria J n kappa cminus cplus pmin
      deltaBar delta alpha
    crit.2.2.1 = crit.1 ∧ crit.2.2.2 = crit.2.1 := by
  have hsurj : ∀ (P : ClampLaw J),
      ContClampModel P kappa cminus cplus pmin deltaBar →
      ∃ PF : FullDataLaw J,
        ContFullDataClampModel PF kappa cminus cplus pmin deltaBar ∧
          PF.observedMargin = P := by
    intro P hP
    exact exists_fullData_cont_lift P hP hreg.1.2.2.2.2.2.1
  have htarget : ∀ (PF : FullDataLaw J)
      (hPF : ContFullDataClampModel PF kappa cminus cplus pmin deltaBar),
      causalClampMean PF delta =
        contClampFunctional PF.observedMargin kappa cminus cplus pmin deltaBar
          hPF.observedModel delta := by
    intro PF hPF
    exact (continuity_causal_bridge J kappa cminus cplus pmin deltaBar PF hPF
      hreg.1).2 delta hdelta
  exact contFrontierCriteria_eq_of_surjective J n kappa cminus cplus pmin
    deltaBar delta alpha hsurj htarget

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier

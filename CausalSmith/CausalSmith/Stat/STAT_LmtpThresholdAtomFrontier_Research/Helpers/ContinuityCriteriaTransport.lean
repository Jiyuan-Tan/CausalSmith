/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Basic

/-! # Abstract transport of continuity-only decision criteria -/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory Set

noncomputable section

/-- Surjectivity of the observed-margin map and point identification of the
causal target are sufficient to identify both continuity-only causal decision
criteria with their observed counterparts. The result uses [the `hsurj` condition](hyp:hsurj), [the `htarget` condition](hyp:htarget). [This is the stated conclusion](goal).
-/
lemma contFrontierCriteria_eq_of_surjective
    (J n : ℕ) (kappa cminus cplus pmin deltaBar delta alpha : ℝ)
    (hsurj : ∀ (P : ClampLaw J),
      ContClampModel P kappa cminus cplus pmin deltaBar →
      ∃ PF : FullDataLaw J,
        ContFullDataClampModel PF kappa cminus cplus pmin deltaBar ∧
          PF.observedMargin = P)
    (htarget : ∀ (PF : FullDataLaw J)
      (hPF : ContFullDataClampModel PF kappa cminus cplus pmin deltaBar),
      causalClampMean PF delta =
        contClampFunctional PF.observedMargin kappa cminus cplus pmin deltaBar
          hPF.observedModel delta) :
    let crit := contFrontierCriteria J n kappa cminus cplus pmin
      deltaBar delta alpha
    crit.2.2.1 = crit.1 ∧ crit.2.2.2 = crit.2.1 := by
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

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier

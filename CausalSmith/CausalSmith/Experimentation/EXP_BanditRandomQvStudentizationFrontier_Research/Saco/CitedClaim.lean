/- Frozen citation carrier for Saco (2026), Theorem 5.14. -/

import CausalSmith.Experimentation.EXP_BanditRandomQvStudentizationFrontier_Research.Saco.Class

/-! # Saco Theorem 5.14 cited claim -/

open Filter MeasureTheory Topology

namespace CausalSmith.Experimentation.BanditRandomQV

noncomputable section

/-- Gabriel Saco (2026), *Fixed-Horizon Self-Normalized Inference for Adaptive
Experiments via Martingale AIPW/DML with Logged Propensities*,
arXiv:2602.15559v1, Assumptions 3.2, 3.5--3.10, 4.5, 4.8, 5.11;
Theorem 5.14 and equations (5.5)--(5.6). -/
-- @node: lem:saco-pointwise-rqv-pivot
def SacoTheorem514Claim : Sort 0 :=
  ∀ (Ω 𝒳 : Type) [_mΩ : MeasurableSpace Ω] [_mX : MeasurableSpace 𝒳]
    (W : SacoArrayWorld Ω 𝒳) (epsilon CY CM vmin : ℝ),
    SacoSourceConditions W epsilon CY CM vmin →
    CDFConverges W.law
      (fun n ω => if W.realizedQV n ω = 0 then 0 else
        W.scoreSum n ω / Real.sqrt (W.realizedQV n ω))
      Causalean.Mathlib.stdNormalCDF ∧
    CDFConverges W.law
      (fun n ω => if W.sampleVariance n ω = 0 then 0 else
        Real.sqrt (W.N n) * (W.thetaHat n ω - W.theta0 n) /
          Real.sqrt (W.sampleVariance n ω))
      Causalean.Mathlib.stdNormalCDF ∧
    ∀ alpha, 0 < alpha → alpha < 1 → Tendsto
      (fun n => (W.law n {ω | W.theta0 n ∈ Set.Icc
        (W.thetaHat n ω - Causalean.Mathlib.probit (1 - alpha / 2) *
          Real.sqrt (W.sampleVariance n ω / W.N n))
        (W.thetaHat n ω + Causalean.Mathlib.probit (1 - alpha / 2) *
          Real.sqrt (W.sampleVariance n ω / W.N n))}).toReal)
      atTop (𝓝 (1 - alpha))

end

end CausalSmith.Experimentation.BanditRandomQV

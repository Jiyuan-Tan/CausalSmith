/- Uniform AIPW inference after early-measurable suffix-QV stabilization. -/

import CausalSmith.Experimentation.EXP_BanditRandomQvStudentizationFrontier_Research.Saco.Class

/-! # Repaired Saco AIPW pivot -/

open Filter MeasureTheory Topology Set

namespace CausalSmith.Experimentation.BanditRandomQV

noncomputable section

/-- The variance-growth-only assertion rejected by the counterexample.  This
is deliberately separate from the cited carrier and adds no premise to the
repaired theorem. -/
def SacoVarianceGrowthOnlyClaim : Prop :=
  ∀ (Ω 𝒳 : Type) [_mΩ : MeasurableSpace Ω] [_mX : MeasurableSpace 𝒳]
    (W : SacoArrayWorld Ω 𝒳) (epsilon CY CM vmin : ℝ),
    SacoSourceConditions W epsilon CY CM vmin →
    CDFConverges W.law
      (fun n ω => if W.realizedQV n ω = 0 then 0 else
        W.scoreSum n ω / Real.sqrt (W.realizedQV n ω))
      Causalean.Mathlib.stdNormalCDF

-- @node: thm:saco-early-stabilized-aipw-pivot
theorem saco_early_stabilized_aipw_pivot
    {Ω 𝒳 I : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] [Nonempty I]
    (W : I → SacoArrayWorld Ω 𝒳) (epsilon CY CM vmin lambdaMin : ℝ)
    (k : ℕ → ℕ) (Lambda : ℕ → I → Ω → ℝ)
    (hClass : SacoEarlyStabilizedAIPWClass W epsilon CY CM vmin lambdaMin k Lambda) :
    (∀ n i, martingaleDifference ((W i).law n) ((W i).scoredFiltration n)
      ((W i).N n) ((W i).increment n)) ∧
    (∃ CX : ℝ, CX = 512 * (1 + epsilon⁻¹) ^ 4 * (2 * CY + 2 * CM) + 128 * CY ∧
      ∀ n i s, 1 ≤ s → s ≤ (W i).N n →
        ∫ ω, |(W i).increment n s ω| ^ 4 ∂(W i).law n ≤ CX) ∧
    UniformInProbability (fun n i => (W i).law n)
      (fun n i ω => (W i).realizedQV n ω /
        (((W i).N n : ℝ) * Lambda n i ω)) (fun _ _ _ => 1) ∧
    UniformCDFConverges (fun n i => (W i).law n)
      (fun n i ω => if (W i).realizedQV n ω = 0 then 0 else
        (W i).scoreSum n ω / Real.sqrt ((W i).realizedQV n ω))
      Causalean.Mathlib.stdNormalCDF ∧
    UniformCDFConverges (fun n i => (W i).law n)
      (fun n i ω => if (W i).sampleVariance n ω = 0 then 0 else
        Real.sqrt ((W i).N n) * ((W i).thetaHat n ω - (W i).theta0 n) /
          Real.sqrt ((W i).sampleVariance n ω))
      Causalean.Mathlib.stdNormalCDF ∧
    (∀ alpha, 0 < alpha → alpha < 1 → ∀ eps > 0, ∀ᶠ n in atTop, ∀ i,
      |((W i).law n {ω | (W i).theta0 n ∈ Icc
        ((W i).thetaHat n ω - Causalean.Mathlib.probit (1 - alpha / 2) *
          Real.sqrt ((W i).sampleVariance n ω / (W i).N n))
        ((W i).thetaHat n ω + Causalean.Mathlib.probit (1 - alpha / 2) *
          Real.sqrt ((W i).sampleVariance n ω / (W i).N n))}).toReal -
        (1 - alpha)| ≤ eps) ∧
    ¬ SacoVarianceGrowthOnlyClaim := by sorry

end

end CausalSmith.Experimentation.BanditRandomQV

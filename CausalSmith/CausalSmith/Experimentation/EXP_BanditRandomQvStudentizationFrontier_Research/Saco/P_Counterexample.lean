/- Counterexample to the variance-growth-only Saco pivot claim. -/

import CausalSmith.Experimentation.EXP_BanditRandomQvStudentizationFrontier_Research.Saco.CitedClaim
import CausalSmith.Experimentation.EXP_BanditRandomQvStudentizationFrontier_Research.P_EndogenousQVObstruction
import Mathlib.Probability.CondVar

/-! # Saco Theorem 5.14 counterexample -/

open MeasureTheory ProbabilityTheory

namespace CausalSmith.Experimentation.BanditRandomQV

noncomputable section

def sacoNoncenteredMean : ℝ :=
  2 / Real.sqrt (2 * Real.pi) * (Real.sqrt (3 / 28) - 1 / Real.sqrt 8)

/-- The shared, fully identified witness used both by the reductio and by the
strict-inclusion theorem. -/
def IsSacoCounterexample {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]
    (W : SacoArrayWorld Ω 𝒳) : Prop :=
  SacoSourceConditions W (1 / 4) (313 / 16) (41 / 16) 4 ∧
  (∀ n, W.N n = 2 * (n + 1)) ∧
  (∀ n, W.theta0 n = 1) ∧
  (∀ n, W.scoredSet n = Finset.Icc 1 (2 * (n + 1))) ∧
  (∀ n s, 1 ≤ s → s ≤ W.N n →
    W.scoredFiltration n (s - 1) =
      (W.row n).ℱ (W.scoredTime n (s - 1) - 1)) ∧
  (∀ n t ω, (W.row n).propensity t ω = 1 / 2 ∨
    (W.row n).propensity t ω = 1 / 4) ∧
  (∀ n s, 1 ≤ s → s ≤ W.N n →
    W.increment n s = fun ω => W.phiHat n (W.scoredTime n (s - 1)) ω - 1) ∧
  (∀ n s, 1 ≤ s → s ≤ W.N n →
    (W.law n)[(fun ω => (W.increment n s ω) ^ 2) |
      W.scoredFiltration n (s - 1)] =ᵐ[W.law n]
      fun ω => if s ≤ n + 1 then 4 else
        if W.scoreSum (n / 2) ω > 0 then 16 / 3 else 4)

def SacoCounterexampleWitnessStatement : Prop :=
    let Ω := ℕ → (Bool × Bool)
    ∃ (W : SacoArrayWorld Ω Unit) (epsilon CY CM vmin : ℝ)
      (muL : Measure (ℝ × ℝ)) (Z V : ℝ × ℝ → ℝ),
      SacoSourceConditions W epsilon CY CM vmin ∧
      IsSacoCounterexample W ∧
      epsilon = 1 / 4 ∧ CY = 313 / 16 ∧ CM = 41 / 16 ∧ vmin = 4 ∧
      (∀ n, W.N n = 2 * (n + 1)) ∧
      (∀ n, W.theta0 n = 1) ∧
      (∀ n t, t ∈ W.scoredSet n →
        (ProbabilityTheory.condVar (W.preTreatment n t) (W.outcome n t) (W.law n)
          =ᵐ[W.law n] fun ω =>
            1 + (W.row n).propensity t ω * (1 - (W.row n).propensity t ω)) ∧
        ∀ᵐ ω ∂W.law n, 1 ≤
          ProbabilityTheory.condVar (W.preTreatment n t) (W.outcome n t) (W.law n) ω) ∧
      (∀ n s, 1 ≤ s → s ≤ W.N n →
        let t := W.scoredTime n (s - 1)
        let p := (W.row n).propensity t
        ((W.law n)[(fun ω => if W.increment n s ω = (p ω)⁻¹ then 1 else 0) |
            W.scoredFiltration n (s - 1)] =ᵐ[W.law n] p) ∧
        ((W.law n)[(fun ω => if W.increment n s ω = -((1 - p ω)⁻¹) then 1 else 0) |
            W.scoredFiltration n (s - 1)] =ᵐ[W.law n] fun ω => 1 - p ω) ∧
        ((W.law n)[W.increment n s | W.scoredFiltration n (s - 1)]
          =ᵐ[W.law n] fun _ => 0) ∧
        ((W.law n)[(fun ω => (W.increment n s ω) ^ 2) |
            W.scoredFiltration n (s - 1)]
          =ᵐ[W.law n] fun ω => (p ω)⁻¹ + (1 - p ω)⁻¹) ∧
        ∀ᵐ ω ∂W.law n,
          (p ω)⁻¹ + (1 - p ω)⁻¹ = 4 ∨
          (p ω)⁻¹ + (1 - p ω)⁻¹ = 16 / 3) ∧
      (∀ n, ∀ᵐ ω ∂W.law n, 4 * W.N n ≤ W.predictableQV n ω) ∧
      (∀ n, W.realizedQV n = fun ω =>
        ∑ s ∈ Finset.Icc 1 (W.N n), (W.increment n s ω) ^ 2) ∧
      standardNormalUnder muL Z ∧ standardNormalUnder muL V ∧ IndepFun Z V muL ∧
      CDFConverges W.law
        (fun n ω => if W.realizedQV n ω = 0 then 0 else
          W.scoreSum n ω / Real.sqrt (W.realizedQV n ω))
        (fun x => (muL {zv | endogenousLimit (Z zv) (V zv) ≤ x}).toReal) ∧
      CDFConverges W.law
        (fun n ω => if W.sampleVariance n ω = 0 then 0 else
          Real.sqrt (W.N n) * (W.thetaHat n ω - W.theta0 n) /
            Real.sqrt (W.sampleVariance n ω))
        (fun x => (muL {zv | endogenousLimit (Z zv) (V zv) ≤ x}).toReal) ∧
      (∫ zv, endogenousLimit (Z zv) (V zv) ∂muL) = sacoNoncenteredMean ∧
      sacoNoncenteredMean ≠ 0 ∧
      ¬ CDFConverges W.law
        (fun n ω => if W.realizedQV n ω = 0 then 0 else
          W.scoreSum n ω / Real.sqrt (W.realizedQV n ω))
        Causalean.Mathlib.stdNormalCDF

theorem saco_theorem_5_14_counterexample_witness :
    SacoCounterexampleWitnessStatement := by sorry

-- @node: prop:saco-theorem-5-14-counterexample
theorem saco_theorem_5_14_counterexample (hSaco : SacoTheorem514Claim) :
    SacoCounterexampleWitnessStatement ∧ ¬ SacoTheorem514Claim := by sorry

end

end CausalSmith.Experimentation.BanditRandomQV

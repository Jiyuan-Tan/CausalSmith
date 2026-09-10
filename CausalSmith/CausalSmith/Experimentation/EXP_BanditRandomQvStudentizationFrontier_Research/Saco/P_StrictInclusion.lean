/- The counterexample fails every early-measurable stabilization scheme. -/

import CausalSmith.Experimentation.EXP_BanditRandomQvStudentizationFrontier_Research.Saco.P_Counterexample
import Mathlib.Data.Nat.Choose.Central

/-! # Strictness of the early-stabilized repair -/

open Filter MeasureTheory Topology

namespace CausalSmith.Experimentation.BanditRandomQV

noncomputable section

-- @node: prop:saco-counterexample-violates-early-stabilization
theorem saco_counterexample_violates_early_stabilization :
    let Ω := ℕ → (Bool × Bool)
    SacoCounterexampleWitnessStatement ∧
    ∃ (W : SacoArrayWorld Ω Unit) (epsilon CY CM vmin : ℝ),
      IsSacoCounterexample W ∧ SacoSourceConditions W epsilon CY CM vmin ∧
      (∀ n, W.N n = 2 * (n + 1)) ∧
      (∀ n t ω, (W.row n).propensity t ω = 1 / 2 ∨
        (W.row n).propensity t ω = 1 / 4) ∧
      (∀ n s ω, |W.increment n s ω| ≤ 4) ∧
      ∀ (k : ℕ → ℕ) (Lambda : ℕ → Ω → ℝ),
        Tendsto (fun n => (k n : ℝ) / W.N n) atTop (𝓝 0) →
        (∀ n, k n < W.N n) →
        (∀ n, Measurable[W.scoredFiltration n (k n)] (Lambda n)) →
        (∀ n, ∀ᵐ ω ∂W.law n, 0 < Lambda n ω) →
        ¬ TendstoInProbability W.law
          (fun n ω => (∑ s ∈ Finset.Icc (k n + 1) (W.N n),
            (W.law n)[(fun ω' => (W.increment n s ω') ^ 2) |
              W.scoredFiltration n (s - 1)] ω) /
              ((W.N n : ℝ) * Lambda n ω))
          (fun _ _ => 1) := by sorry

end

end CausalSmith.Experimentation.BanditRandomQV

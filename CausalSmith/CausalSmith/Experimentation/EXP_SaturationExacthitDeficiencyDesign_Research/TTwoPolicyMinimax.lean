import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.GaussianGame
import Causalean.Mathlib.Probability.StdNormalCDF

/-! # Closed-form two-policy minimax allocation -/

open Set

namespace CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

noncomputable section

/-- Sharp two-policy Gaussian regret constant. -/
def gaussianRegretConstant : ℝ := sSup {y : ℝ | ∃ x ∈ Ici (0 : ℝ),
  y = x * Causalean.Mathlib.stdNormalCDF (-x)}
-- @realizes \kappa(max_{x≥0} x Phi(-x))

/-- The deterministic sign selector for the two-policy contrast. -/
def twoPolicySignSelector : (ActiveIndex (Finset.univ : Finset (Fin 2)) → ℝ) → Fin 2 → ℝ :=
  fun x a => if x ⟨0, by simp⟩ - x ⟨1, by simp⟩ ≥ 0 then
    if a = 0 then 1 else 0 else if a = 1 then 1 else 0

/-- The four-unit policies with saturations `(1/4,1/2)`. -/
def fourUnitPolicyCounts : Fin 2 → ℕ := ![1, 2]

-- @node: thm:two-policy-minimax
/-- For two actions the sign rule attains `kappa * sqrt(v₁/r₁+v₂/r₂)`;
the exact-count and Bernoulli allocation formulas and the four-unit witness follow. -/
theorem two_policy_minimax (n : ℕ) (m : Fin 2 → ℕ) (p v r : Fin 2 → ℝ)
    (hv : ∀ k, 0 < v k) (hr : ∀ k, 0 < r k)
    (hmenu : WellFormedMenu n 2 m) (hp : InSimplex p) :
    let B := (hitMatrix n m p).1
    (∀ i j, B i j ∈ Ioo (0 : ℝ) 1) ∧
    gaussianGlobalValueReal Finset.univ v r =
      gaussianRegretConstant * Real.sqrt (v 0 / r 0 + v 1 / r 1) ∧
    GaussianSelector Finset.univ twoPolicySignSelector ∧
    gaussianSelectorWorstRisk Finset.univ v r twoPolicySignSelector =
      ENNReal.ofReal (gaussianRegretConstant * Real.sqrt (v 0 / r 0 + v 1 / r 1)) ∧
    (twoPolicyAllocation B v).2.2 = Real.sqrt (v 0) /
      (Real.sqrt (v 0) + Real.sqrt (v 1)) ∧
    (∀ alpha ∈ Ioo (0 : ℝ) 1,
      v 0 / (twoPolicyAllocation B v).2.2 + v 1 / (1 - (twoPolicyAllocation B v).2.2) ≤
        v 0 / alpha + v 1 / (1 - alpha)) ∧
    (twoPolicyAllocation B v).2.1 =
      sInf {t : ℝ | t ∈ Icc 0 1 ∧ ∀ s ∈ Icc (0 : ℝ) 1,
        twoPolicyObjective B v t ≤ twoPolicyObjective B v s} ∧
    (B 0 0 > B 0 1 ∧ B 1 1 > B 1 0 →
      (((twoPolicyAllocation B v).2.1 = 0 ↔
          v 0 / v 1 ≤ (B 1 1 - B 1 0) * B 0 1 ^ 2 /
            ((B 0 0 - B 0 1) * B 1 1 ^ 2)) ∧
       ((twoPolicyAllocation B v).2.1 = 1 ↔
          (B 1 1 - B 1 0) * B 0 0 ^ 2 /
            ((B 0 0 - B 0 1) * B 1 0 ^ 2) ≤ v 0 / v 1) ∧
       (((twoPolicyAllocation B v).2.1 ≠ 0 ∧ (twoPolicyAllocation B v).2.1 ≠ 1) →
          (twoPolicyAllocation B v).2.1 =
            (B 1 1 * Real.sqrt (v 0 * (B 0 0 - B 0 1) /
              (v 1 * (B 1 1 - B 1 0))) - B 0 1) /
            ((B 0 0 - B 0 1) + (B 1 1 - B 1 0) *
              Real.sqrt (v 0 * (B 0 0 - B 0 1) /
                (v 1 * (B 1 1 - B 1 0))))) ∧
        ∀ t, t ∈ Icc (0 : ℝ) 1 →
          twoPolicyObjective B v (twoPolicyAllocation B v).2.1 ≤ twoPolicyObjective B v t)) ∧
    (let B4 := (hitMatrix 4 fourUnitPolicyCounts (fun _ => 1 / 2)).1
     let v4 : Fin 2 → ℝ := fun _ => 1
     let optimizedRegretRatio :=
       (faceMechanismValues B4 Finset.univ v4).1 /
         (faceMechanismValues B4 Finset.univ v4).2
     let optimizedClusterCountRatio := optimizedRegretRatio ^ 2
     B4 0 0 = 27 / 64 ∧ B4 0 1 = 1 / 4 ∧
      B4 1 0 = 27 / 128 ∧ B4 1 1 = 3 / 8 ∧
      (twoPolicyAllocation B4 v4).2.1 = -80 + 288 * Real.sqrt 462 / 77 ∧
      optimizedRegretRatio = Real.sqrt (43 / 54 + Real.sqrt 462 / 27) ∧
      optimizedClusterCountRatio = 43 / 54 + Real.sqrt 462 / 27 ∧
      (twoPolicyAllocation B4 v4).2.1 ∈ Icc 0.39383577842 0.39383577844 ∧
      optimizedRegretRatio ∈
        Icc 1.26189430296 1.26189430298 ∧
      optimizedClusterCountRatio ∈ Icc 1.59237723185 1.59237723187) := by sorry

end

end CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

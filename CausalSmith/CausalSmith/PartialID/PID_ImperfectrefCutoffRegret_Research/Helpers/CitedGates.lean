import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Explicit cited logical gates used conditionally by this paper. -/

open MeasureTheory
open scoped BigOperators

namespace CausalSmith.PartialID.ImperfectrefCutoffRegret

/-- Massart, Pascal (1990), “The Tight Constant in the Dvoretzky--Kiefer--Wolfowitz
Inequality,” Annals of Probability 18(3), 1269--1283, immediately after Theorem 1
and in the abstract, DOI 10.1214/aop/1176990746:
`P(√n sup_x |F̂_n(x)-F(x)| > λ) ≤ 2 exp(-2λ²)`.

This cited proposition is substrate supplied to consumers as an explicit hypothesis. -/
-- @node: lem:dkw-massart-two-sided
def DkwMassartTwoSided : Sort 0 :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {N : ℕ} (Y : Fin N → Ω → ℝ) (F : ℝ → ℝ) (Fn : Ω → ℝ → ℝ),
    ((∀ i, Measurable (Y i)) ∧ ProbabilityTheory.iIndepFun Y μ ∧
      (∀ i y, F y = μ.real {ω | Y i ω ≤ y}) ∧
      (∀ ω y, Fn ω y = (N : ℝ)⁻¹ *
        ∑ i : Fin N, if Y i ω ≤ y then 1 else 0)) →
    (∀ l : ℝ, 0 < l →
      μ.real {ω | l < Real.sqrt (N : ℝ) * (⨆ y : ℝ, |Fn ω y - F y|)} ≤
        2 * Real.exp (-2 * l ^ 2))

end CausalSmith.PartialID.ImperfectrefCutoffRegret

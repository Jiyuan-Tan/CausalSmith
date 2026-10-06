module
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Cited logical substrate gate for the Laurent moment pair. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Set

-- @node: lem:legal-laurent-moment-pair
/-- Zhenghao Zeng, Sivaraman Balakrishnan, Yanjun Han, and Edward H. Kennedy
(2026), *Causal Inference with High-dimensional Discrete Covariates*,
arXiv:2405.00118v3, Appendix D.3, display (32), the following separation
display, and Lemma 7. This is a cited assumption, with no consumer in this
paper's dependency graph. -/
def ZengLegalLaurentMomentPair : Sort 0 :=
  ∃ a₀ η : ℝ, 0 < a₀ ∧ 0 < η ∧ ∃ J₀ : ℕ,
    ∀ J : ℕ, J₀ ≤ J → a₀ / (J : ℝ) ^ 2 ≤ 1 ∧
      ∃ omegaPlus omegaMinus : Measure ℝ,
        IsProbabilityMeasure omegaPlus ∧ IsProbabilityMeasure omegaMinus ∧
        omegaPlus ((Icc (a₀ / (J : ℝ) ^ 2) 1)ᶜ) = 0 ∧
        omegaMinus ((Icc (a₀ / (J : ℝ) ^ 2) 1)ᶜ) = 0 ∧
        (∀ r : ℤ, -1 ≤ r → r ≤ 3 * (J : ℤ) →
          (∫ x, x ^ r ∂omegaPlus) = ∫ x, x ^ r ∂omegaMinus) ∧
        η ≤ (∫ x, x / (x + a₀ / (J : ℝ) ^ 2) ∂omegaPlus) -
          (∫ x, x / (x + a₀ / (J : ℝ) ^ 2) ∂omegaMinus)

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

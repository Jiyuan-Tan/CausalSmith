/- Compactness of laws on a bounded Loewner interval. -/

import CausalSmith.Experimentation.EXP_BanditRandomQvStudentizationFrontier_Research.Basic
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-! # Compact covariance-law subsequences -/

open Filter MeasureTheory Topology

namespace CausalSmith.Experimentation.BanditRandomQV

noncomputable section

def covarianceInterval (d : ℕ) (a b : ℝ) : Set (Mat d) :=
  {A | transpose A = A ∧ psdLE (a • identMat d) A ∧ psdLE A (b • identMat d)}

-- @node: lem:compact-covariance-law-subsequence
lemma compact_covariance_law_subsequence {d : ℕ}
    [MeasurableSpace (Mat d)] [BorelSpace (Mat d)] (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b)
    (law : ℕ → ProbabilityMeasure {A : Mat d // A ∈ covarianceInterval d a b}) :
    ∃ (nk : ℕ → ℕ) (mu : ProbabilityMeasure {A : Mat d // A ∈ covarianceInterval d a b}),
      StrictMono nk ∧ ∀ f : {A : Mat d // A ∈ covarianceInterval d a b} → ℝ,
        Continuous f → Tendsto
          (fun k => ∫ A, f A ∂(law (nk k) : Measure _)) atTop
          (𝓝 (∫ A, f A ∂(mu : Measure _))) := by sorry

end

end CausalSmith.Experimentation.BanditRandomQV

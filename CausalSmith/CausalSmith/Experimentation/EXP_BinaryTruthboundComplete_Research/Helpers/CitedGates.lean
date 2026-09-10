import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance

/-!
# Cited logical interface

A. W. van der Vaart, *Asymptotic Statistics* (1998), Proposition 2.27, pp. 20–21:
the Lindeberg–Feller theorem for independent triangular arrays.
-/

open scoped BigOperators ProbabilityTheory ENNReal
open Filter Topology

namespace CausalSmith.Experimentation.BinaryTruthbound

open MeasureTheory ProbabilityTheory

/-- Van der Vaart (1998), Proposition 2.27: independent centered triangular arrays satisfying
the Lindeberg condition converge after total-standard-deviation normalization to `N(0,1)`. -/
-- @node: lem:lindeberg-feller-independent-array
def LindebergFellerIndependentArray : Sort 0 :=
  ∀ (k : ℕ → ℕ) (Omega : ℕ → Type) [∀ n, MeasurableSpace (Omega n)]
    (P : ∀ n, Measure (Omega n)) [∀ n, IsProbabilityMeasure (P n)]
    (Y : ∀ n, Fin (k n) → Omega n → ℝ),
    (∀ n, iIndepFun (Y n) (P n)) →
    (∀ n j, Measurable (Y n j)) →
    (∀ n j, MemLp (Y n j) 2 (P n)) →
    (∀ n j, ∫ w, Y n j w ∂P n = 0) →
    (∀ n, 0 < ∑ j, variance (Y n j) (P n)) →
    (∀ ε : ℝ, 0 < ε →
      Tendsto (fun n =>
        ((∑ j, variance (Y n j) (P n))⁻¹) *
          ∑ j, ∫ w,
            (Y n j w) ^ 2 *
              if ε * Real.sqrt (∑ i, variance (Y n i) (P n)) < |Y n j w| then 1 else 0
            ∂P n)
        atTop (𝓝 0)) →
    TendstoInDistribution
      (fun n w => (∑ j, Y n j w) / Real.sqrt (∑ j, variance (Y n j) (P n)))
      atTop (fun x : ℝ => x) P (gaussianReal 0 1)

end CausalSmith.Experimentation.BinaryTruthbound

module
public import Causalean.Stat.UStatistic.Variance
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Moments.Variance

/-!
# Localized unordered order-two U-statistics

This module fixes the finite product law, unordered pair set, statistic, and the two
localization masses used in a variance bound. The row mass squares the conditional
weight before integrating; the pair mass integrates the weight once over each variable.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Causalean.Stat.UStatistic.LocalizedVariance

variable {X : Type*} [MeasurableSpace X]

/-- A [kernel](hyp:H), [localization weight](hyp:W), and [nonnegative envelope scale](hyp:M)
form a localized symmetric kernel when both functions are measurable and symmetric,
the weight lies between zero and one, and the kernel is bounded by the scaled weight. -/
structure LocalizedKernel (H W : X → X → ℝ) (M : ℝ) : Prop where
  measurable_kernel : Measurable fun z : X × X => H z.1 z.2
  measurable_weight : Measurable fun z : X × X => W z.1 z.2
  symmetric_kernel : ∀ x y, H x y = H y x
  symmetric_weight : ∀ x y, W x y = W y x
  weight_nonneg : ∀ x y, 0 ≤ W x y
  weight_le_one : ∀ x y, W x y ≤ 1
  envelope_nonneg : 0 ≤ M
  envelope : ∀ x y, |H x y| ≤ M * W x y

/-- A [probability law](hyp:P) and [sample size](hyp:n) determine [the product law of independent
observations](goal) with that common marginal distribution. -/
noncomputable def iidLaw (P : Measure X) (n : ℕ) : Measure (Fin n → X) :=
  Measure.pi fun _ : Fin n => P

/-- A [sample size](hyp:n) determines [its unordered distinct index pairs](goal), represented by
the unique orientation whose first index is smaller. -/
def pairIndices (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 < p.2

/-- A [sample size](hyp:n), [two-observation kernel](hyp:H), and [realized sample](hyp:ω)
determine [the unordered order-two U-statistic](goal), the average kernel value over distinct
unordered pairs of observations (each pair evaluated with the lower-indexed observation first).
With fewer than two observations there are no pairs and the value is zero. -/
noncomputable def uStatistic (n : ℕ) (H : X → X → ℝ) (ω : Fin n → X) : ℝ :=
  ((pairIndices n).card : ℝ)⁻¹ *
    ∑ p ∈ pairIndices n, H (ω p.1) (ω p.2)

/-- A [probability law](hyp:P) and [localization weight](hyp:W) determine [the pair mass](goal),
the weight's expectation under two independent draws. -/
noncomputable def pairMass (P : Measure X) (W : X → X → ℝ) : ℝ :=
  ∫ x, ∫ y, W x y ∂P ∂P

/-- A [probability law](hyp:P) and [localization weight](hyp:W) determine [the squared row
mass](goal), the expectation of the square of its conditional one-draw mass. -/
noncomputable def rowMassSq (P : Measure X) (W : X → X → ℝ) : ℝ :=
  ∫ x, (∫ y, W x y ∂P) ^ 2 ∂P

/-- Two [finite index pairs](hyp:p,q) satisfy [the shared-index relation](goal) when they have
at least one endpoint in common. -/
def SharesIndex {n : ℕ} (p q : Fin n × Fin n) : Prop :=
  p.1 = q.1 ∨ p.1 = q.2 ∨ p.2 = q.1 ∨ p.2 = q.2

/-- Two [finite index pairs](hyp:p,q) have [a decidable shared-index relation](goal). -/
instance {n : ℕ} (p q : Fin n × Fin n) : Decidable (SharesIndex p q) := by
  unfold SharesIndex
  infer_instance

/-- A [two-observation kernel](hyp:H), [index pair](hyp:p), and [sample realization](hyp:ω)
determine [the pair's kernel value](goal). -/
noncomputable def pairValue {n : ℕ} (H : X → X → ℝ)
    (p : Fin n × Fin n) (ω : Fin n → X) : ℝ :=
  H (ω p.1) (ω p.2)

end Causalean.Stat.UStatistic.LocalizedVariance

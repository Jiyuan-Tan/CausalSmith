module
public import Causalean.Stat.Concentration.VC.Separability
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Countable empirical processes: common notation

Uses the existing population-centered empirical average. Ghost and signed sums
are normalized by the sample size. Symmetrization theorems require a positive
sample size; threshold measurability also covers the empty sample.
The finite Boolean sign average has exactly the uniform Rademacher law.
-/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Causalean.Stat.EmpiricalProcess.Countable

/-- A uniformly bounded class of real functions on [a measurable sample
space](hyp:Ω), indexed by [an index set](hyp:ι), consists of [the indexed
functions](hyp:f), [a common bound](hyp:bound) that is
[nonnegative](hyp:bound_nonneg), [measurability of every
function](hyp:measurable), and [the absolute value of every function being
at most the bound at every point](hyp:bounded). -/
structure BoundedClass (Ω ι : Type*) [MeasurableSpace Ω] where
  f : ι → Ω → ℝ
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  measurable : ∀ i, Measurable (f i)
  bounded : ∀ i x, |f i x| ≤ bound

/-- [The centered supremum](goal) of [an indexed function class](hyp:f) on
[a sample](hyp:x) relative to [a population measure μ](hyp:μ) is [the
supremum over the class of the absolute difference between each function's
empirical average and its population integral](step:1). -/
def centeredSup {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : ι → Ω → ℝ) {n : ℕ} (x : Fin n → Ω) : ℝ :=
  ⨆ i, |Causalean.Stat.Concentration.centeredEmpiricalAverage μ x (f i)|

/-- [The ghost supremum](goal) of [an indexed function class](hyp:f) on
[two samples x and y of the same size n](hyp:x,y) is [the supremum over the
class of the absolute difference between the two samples' empirical
averages, that is, of |(1/n) Σ_j (f(x_j) − f(y_j))|](step:1). -/
def ghostSup {Ω ι : Type*} (f : ι → Ω → ℝ) {n : ℕ}
    (x y : Fin n → Ω) : ℝ :=
  ⨆ i, |(n : ℝ)⁻¹ * ∑ j, (f i (x j) - f i (y j))|

/-- [The signed supremum](goal) of [an indexed function class](hyp:f) on
[a sample of size n](hyp:x) under [a sign vector σ](hyp:σ) is [the
supremum over the class of the absolute normalized Rademacher sum
|(1/n) Σ_j σ_j f(x_j)|](step:1). -/
def signedSup {Ω ι : Type*} (f : ι → Ω → ℝ) {n : ℕ}
    (x : Fin n → Ω) (σ : Fin n → Bool) : ℝ :=
  ⨆ i, |(n : ℝ)⁻¹ * ∑ j, (if σ j then (1 : ℝ) else -1) * f i (x j)|

/-- [The signed ghost supremum](goal) of [an indexed function class](hyp:f)
on [two samples x and y of the same size n](hyp:x,y) under [a sign vector
σ](hyp:σ) is [the supremum over the class of
|(1/n) Σ_j σ_j (f(x_j) − f(y_j))|, one sign per paired
difference](step:1). -/
def signedGhostSup {Ω ι : Type*} (f : ι → Ω → ℝ) {n : ℕ}
    (x y : Fin n → Ω) (σ : Fin n → Bool) : ℝ :=
  ⨆ i, |(n : ℝ)⁻¹ * ∑ j,
    (if σ j then (1 : ℝ) else -1) * (f i (x j) - f i (y j))|

/-- [The sign average](goal) of [a real function of sign vectors of length
n](hyp:H) is [its sum over all 2^n sign vectors divided by 2^n](step:1),
the expectation under independent uniform Rademacher signs. -/
def signAverage {n : ℕ} (H : (Fin n → Bool) → ℝ) : ℝ :=
  (∑ σ, H σ) / (2 : ℝ)^n

end Causalean.Stat.EmpiricalProcess.Countable

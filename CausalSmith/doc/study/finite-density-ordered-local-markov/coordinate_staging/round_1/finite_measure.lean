/-!
# Finiteness of a normalized finite-DAG density law

This module records the measure-theoretic finiteness consequence of pointwise normalization of
all local factors.  It is separated from conditional independence so downstream proofs can obtain
the `IsFiniteMeasure` instance required by Mathlib's `CondIndepFun` API.
-/

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Causalean.Graph.FiniteDensity

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {X : V → Type*} [∀ i, MeasurableSpace (X i)]
variable {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
variable {G : Causalean.DAG V}

/-- The [observational density of a normalized finite DAG factorization](hyp:B) [has finite
integral against the product reference measure](goal). -/
theorem Factorization.lintegral_observationalDensity_lt_top
    (B : Factorization G X μ) :
    ∫⁻ x, B.observationalDensity x ∂Measure.pi μ < ∞ := by
  /-
  Evaluate `B.lmarginal_compl_observationalDensity_eq` at the empty retained set after splitting
  on whether the full dependent product `∀ i, X i` is empty.  In the inhabited case, evaluate
  the all-coordinate marginal at an anchor assignment and rewrite it as the full lintegral.  In
  the empty case the product measure, hence the integral, is zero.  Do not assume coordinate
  nonemptiness.
  -/
  classical
  by_cases h : Nonempty (∀ i, X i)
  · let x : ∀ i, X i := Classical.choice h
    have hmarg := B.lmarginal_compl_observationalDensity_eq (A := ∅) (by
      intro i hi
      simp at hi)
    have hlin : ∫⁻ v, B.observationalDensity v ∂Measure.pi μ = 1 := by
      rw [MeasureTheory.lintegral_eq_lmarginal_univ x]
      simpa [Factorization.partialDensity] using congrFun hmarg x
    rw [hlin]
    exact ENNReal.one_lt_top
  · let _ : IsEmpty (∀ i, X i) := not_nonempty_iff.mp h
    rw [MeasureTheory.lintegral_of_isEmpty]
    exact ENNReal.zero_lt_top

/-- The [observational measure induced by a normalized finite DAG factorization](hyp:B) [is a
finite measure](goal). -/
noncomputable instance Factorization.instIsFiniteMeasureObservationalMeasure
    (B : Factorization G X μ) : IsFiniteMeasure B.observationalMeasure := by
  rw [Factorization.observationalMeasure]
  exact isFiniteMeasure_withDensity
    (ne_of_lt B.lintegral_observationalDensity_lt_top)

end Causalean.Graph.FiniteDensity

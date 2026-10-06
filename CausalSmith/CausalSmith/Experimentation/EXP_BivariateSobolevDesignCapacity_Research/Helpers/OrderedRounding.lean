module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.RoundingRowBudget

/-! # Ordered boundary rounding guarantee

The Borel component is assembled from the finite arithmetic and changing-basis
proofs. Finite termination follows from the active trace and phase invariant;
fairness follows by successive fresh-seed integration. Exact direction-lottery
covariance, test-row variance, norm-energy increments, and localized projection
contraction, exact active-rank counts, and retained-row invariance are proved;
finite move-moment accumulation and the geometric phase allowance are proved;
predictably selected actual moves have additive moments and exact interval energy
budgets; measurable predictable halving intervals partition the actual trace. The row
budget follows from the uniform move comparison and the energy telescope after
the first loss of protection.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity
-- @node: lem:ordered-prefix-rounding
/-- Ordered boundary rounding is Borel, terminates within n moves, is fair, and controls
every prefix row without a full-rank or general-position assumption. This uses [the hrows hypothesis](hyp:hrows), [the stated conclusion](goal). -/
lemma ordered_prefix_rounding (n : ℕ) (rows : ℕ → Fin n → ℝ) (Λ : ℝ)
    (hrows : ∀ h i, 1 ≤ h → |rows h i| ≤ Λ) :
    Measurable (fun a : (Fin (n / 4) → Fin n → ℝ) × RoundingSeeds n =>
      orderedBoundaryRounding n a.1 a.2) ∧
    (∀ seeds, (∀ h, seeds h ∈ Icc (0 : ℝ) 1) →
      ∀ i, (roundingIteration (rowPrefix rows) seeds n).1 i =
        sgn (orderedBoundaryRounding n (rowPrefix rows) seeds i)) ∧
    (∀ i, ∫ seeds, sgn (orderedBoundaryRounding n (rowPrefix rows) seeds i)
      ∂roundingSeedLaw n = 0) ∧
    (∀ h, 1 ≤ h → (∫ seeds,
      (∑ i, rows h i * sgn (orderedBoundaryRounding n (rowPrefix rows) seeds i)) ^ 2
        ∂roundingSeedLaw n) ≤ 32 * Λ ^ 2 * (min h n : ℕ)) := by
  refine ⟨orderedBoundaryRounding_measurable n, ?_⟩
  refine ⟨fun seeds _ i => roundingIteration_terminal_eq_sign _ seeds i, ?_⟩
  refine ⟨orderedBoundaryRounding_fair (rowPrefix rows), ?_⟩
  exact fun h hh => orderedBoundaryRounding_row_bound rows Λ hrows h hh

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity

module
public import Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk.PoissonCell
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Product-law Poisson occupancy bounds

These lemmas separate the independent-coordinate integral identity from the
finite product comparison used in the birthday-scale occupancy estimate.
-/

public section

namespace Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open scoped NNReal

/-- The Laplace transform of the sum of usable counts from independent
two-arm Poisson cells is the product of the individual cell transforms,
including an empty alphabet and zero-intensity cells. -/
theorem poisson_usable_integral_eq_prod {d : ℕ}
    (u v : Fin d → ℝ≥0) :
    (∫ z : Fin d → ℕ × ℕ,
      Real.exp (-(∑ k, (usablePoissonPairCount (z k) : ℝ)))
      ∂Measure.pi (fun k =>
        (poissonMeasure (u k)).prod (poissonMeasure (v k)))) =
    ∏ k, poissonCellLaplace (u k) (v k) := by
  -- Rewrite exp of the finite sum as a finite product and apply
  -- `integral_fintype_prod_eq_prod` from Mathlib.MeasureTheory.Integral.Pi.
  have hfun :
      (fun z : Fin d → ℕ × ℕ =>
        Real.exp (-(∑ k, (usablePoissonPairCount (z k) : ℝ)))) =
      (fun z => ∏ k, Real.exp (-(usablePoissonPairCount (z k) : ℝ))) := by
    funext z
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
  rw [hfun]
  simpa only [poissonCellLaplace] using
    (MeasureTheory.integral_fintype_prod_eq_prod
      (fun _ (r : ℕ × ℕ) => Real.exp (-(usablePoissonPairCount r : ℝ)))
      (μ := fun k => (poissonMeasure (u k)).prod (poissonMeasure (v k))))

/-- Take [two vectors of Poisson arm intensities over finitely many cells, a real
number x attached to each cell, and two real exponents a and b](hyp:u,v,x,a,b).
If [every cell with x at most one has one-cell Laplace factor at most
exp(−a·x²)](hyp:hlight) and [every cell with x above one has one-cell Laplace
factor at most exp(−b·x)](hyp:hheavy), then [the product of the one-cell
Laplace factors over all cells is at most exp(−(a·S₂ + b·S₁)), where S₂ is the
sum of x² over the cells with x at most one and S₁ is the sum of x over the
cells with x above one](goal). -/
theorem poisson_cell_product_le_exp_sum {d : ℕ}
    (u v : Fin d → ℝ≥0) (x : Fin d → ℝ) (a b : ℝ)
    (hlight : ∀ k, x k ≤ 1 →
      poissonCellLaplace (u k) (v k) ≤ Real.exp (-(a * x k ^ 2)))
    (hheavy : ∀ k, 1 < x k →
      poissonCellLaplace (u k) (v k) ≤ Real.exp (-(b * x k))) :
    (∏ k, poissonCellLaplace (u k) (v k)) ≤
      Real.exp (-(a * ∑ k ∈ Finset.univ.filter (fun k ↦ x k ≤ 1), x k ^ 2 +
        b * ∑ k ∈ Finset.univ.filter (fun k ↦ 1 < x k), x k)) := by
  -- Compare the nonnegative factors using the ordered-ring form of
  -- `Finset.prod_le_prod`, then
  -- combine exponential factors with `Real.exp_sum` and split the index set.
  classical
  let rate : Fin d → ℝ := fun k =>
    if x k ≤ 1 then a * x k ^ 2 else b * x k
  have hnonneg (k : Fin d) : 0 ≤ poissonCellLaplace (u k) (v k) := by
    unfold poissonCellLaplace
    exact integral_nonneg (fun _ => (Real.exp_pos _).le)
  have hcell (k : Fin d) :
      poissonCellLaplace (u k) (v k) ≤ Real.exp (-(rate k)) := by
    by_cases hk : x k ≤ 1
    · simpa [rate, hk] using hlight k hk
    · have hk' : 1 < x k := lt_of_not_ge hk
      simpa [rate, hk] using hheavy k hk'
  calc
    (∏ k, poissonCellLaplace (u k) (v k)) ≤
        ∏ k, Real.exp (-(rate k)) := by
      exact Finset.prod_le_prod (fun k _ => hnonneg k) (fun k _ => hcell k)
    _ = Real.exp (-(∑ k, rate k)) := by
      rw [← Real.exp_sum, Finset.sum_neg_distrib]
    _ = Real.exp (-(a * ∑ k ∈ Finset.univ.filter (fun k ↦ x k ≤ 1), x k ^ 2 +
        b * ∑ k ∈ Finset.univ.filter (fun k ↦ 1 < x k), x k)) := by
      congr 1
      simp [rate, Finset.sum_ite, Finset.mul_sum, not_le]

end Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk

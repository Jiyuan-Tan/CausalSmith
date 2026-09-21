/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.Probability.PoissonAddOnePoincare.NestedPairedProductMoments.PolynomialGrowth
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Coordinate-product integrals under nested paired Poisson laws

After flattening, products of single-coordinate functions factor into scalar Poisson integrals.
The square identity and integrability criterion are tailored to Poincare energy calculations.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace Causalean.Mathlib.Probability.PoissonAddOnePoincare.NestedPairedProductMoments

noncomputable section

open Causalean.Mathlib.Probability.PoissonAddOnePoincare

/-- A [scalar function at each flattened coordinate](hyp:g) and a
[nested count-pair array](hyp:x) determine [their flattened coordinate product](goal),
given by [multiplying the coordinate functions evaluated at the flattened counts](step:1). -/
def nestedPairedCoordinateProduct
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    (g : NestedPairedPoissonIndex iota kappa → Nat → Real)
    (x : iota → kappa → Nat × Nat) : Real :=
  ∏ p, g p (nestedPairedPoissonFlattening iota kappa x p)

/-- Two [arrays of nonnegative Poisson rates](hyp:lambda₁,lambda₂) and
[one scalar function for each flattened coordinate](hyp:g) have
[a nested paired-count product integral equal to the product of scalar Poisson
integrals](goal). -/
theorem integral_nestedPairedCoordinateProduct_eq_prod
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    (lambda₁ lambda₂ : iota → kappa → NNReal)
    (g : NestedPairedPoissonIndex iota kappa → Nat → Real) :
    (∫ x, nestedPairedCoordinateProduct g x
        ∂(nestedPairedPoissonMeasure lambda₁ lambda₂)) =
      ∏ p, ∫ n, g p n ∂(poissonMeasure (nestedPairedPoissonRates lambda₁ lambda₂ p)) := by
  let hmp := measurePreserving_nestedPairedPoissonFlattening lambda₁ lambda₂
  calc
    _ = ∫ z, ∏ p, g p (z p)
        ∂(poissonPi (nestedPairedPoissonRates lambda₁ lambda₂)) := by
      simpa [nestedPairedCoordinateProduct] using
        hmp.integral_comp' (fun z => ∏ p, g p (z p))
    _ = _ := by
      exact MeasureTheory.integral_fintype_prod_eq_prod g

/-- Two [arrays of nonnegative Poisson rates](hyp:lambda₁,lambda₂) and
[one scalar function for each flattened coordinate](hyp:g) have
[the squared nested coordinate-product integral equal to the product of scalar second
moments](goal). -/
theorem integral_sq_nestedPairedCoordinateProduct_eq_prod
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    (lambda₁ lambda₂ : iota → kappa → NNReal)
    (g : NestedPairedPoissonIndex iota kappa → Nat → Real) :
    (∫ x, (nestedPairedCoordinateProduct g x) ^ 2
        ∂(nestedPairedPoissonMeasure lambda₁ lambda₂)) =
      ∏ p, ∫ n, (g p n) ^ 2
        ∂(poissonMeasure (nestedPairedPoissonRates lambda₁ lambda₂ p)) := by
  let hmp := measurePreserving_nestedPairedPoissonFlattening lambda₁ lambda₂
  calc
    _ = ∫ z, (∏ p, g p (z p)) ^ 2
        ∂(poissonPi (nestedPairedPoissonRates lambda₁ lambda₂)) := by
      simpa [nestedPairedCoordinateProduct] using
        hmp.integral_comp' (fun z => (∏ p, g p (z p)) ^ 2)
    _ = ∫ z, ∏ p, (g p (z p)) ^ 2
        ∂(poissonPi (nestedPairedPoissonRates lambda₁ lambda₂)) := by
      congr with z
      simp [Finset.prod_pow]
    _ = _ := by
      exact MeasureTheory.integral_fintype_prod_eq_prod (fun p n => (g p n) ^ 2)

/-- Two [arrays of nonnegative Poisson rates](hyp:lambda₁,lambda₂),
[one scalar function for each flattened coordinate](hyp:g), and
[integrable scalar squared functions](hyp:hg) give
[a square-integrable nested flattened coordinate product](goal). -/
theorem memLp_two_nestedPairedCoordinateProduct
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    (lambda₁ lambda₂ : iota → kappa → NNReal)
    (g : NestedPairedPoissonIndex iota kappa → Nat → Real)
    (hg : ∀ p, Integrable (fun n => (g p n) ^ 2)
      (poissonMeasure (nestedPairedPoissonRates lambda₁ lambda₂ p))) :
    MemLp (nestedPairedCoordinateProduct g) 2
      (nestedPairedPoissonMeasure lambda₁ lambda₂) := by
  have hflat : Integrable (fun z => (∏ p, g p (z p)) ^ 2)
      (poissonPi (nestedPairedPoissonRates lambda₁ lambda₂)) := by
    have hprod := Integrable.fintype_prod (𝕜 := Real) hg
    simpa [poissonPi, Finset.prod_pow] using hprod
  have hnested :=
    (measurePreserving_nestedPairedPoissonFlattening lambda₁ lambda₂)
      |>.integrable_comp_of_integrable hflat
  refine (memLp_two_iff_integrable_sq
    (measurable_of_countable _).aestronglyMeasurable).2 ?_
  simpa [nestedPairedCoordinateProduct, Function.comp_def] using hnested

/-- Two [arrays of nonnegative Poisson rates](hyp:lambda₁,lambda₂) and
[first- and second-count scalar functions in every cell](hyp:g₁,g₂) have
[their cellwise nested product integral factored into scalar Poisson integrals](goal). -/
theorem integral_nestedPaired_cellwise_product_eq_prod
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    (lambda₁ lambda₂ : iota → kappa → NNReal)
    (g₁ g₂ : iota → kappa → Nat → Real) :
    (∫ x, ∏ i, ∏ j, g₁ i j (x i j).1 * g₂ i j (x i j).2
        ∂(nestedPairedPoissonMeasure lambda₁ lambda₂)) =
      ∏ i, ∏ j,
        ((∫ n, g₁ i j n ∂(poissonMeasure (lambda₁ i j))) *
          (∫ n, g₂ i j n ∂(poissonMeasure (lambda₂ i j)))) := by
  let g : NestedPairedPoissonIndex iota kappa → Nat → Real := fun p =>
    Fin.cases (g₁ p.1 p.2.1) (fun _ => g₂ p.1 p.2.1) p.2.2
  have h := integral_nestedPairedCoordinateProduct_eq_prod lambda₁ lambda₂ g
  simp only [nestedPairedCoordinateProduct, g, Fintype.prod_sigma,
    Fin.prod_univ_two, nestedPairedPoissonFlattening_apply_zero,
    nestedPairedPoissonFlattening_apply_one, nestedPairedPoissonRates] at h
  have hone : (1 : Fin 2) = Fin.succ 0 := rfl
  rw [hone] at h
  simpa only [Fin.cases_zero, Fin.cases_succ] using h

/-- Two [arrays of nonnegative Poisson rates](hyp:lambda₁,lambda₂) and
[first- and second-count scalar functions in every cell](hyp:g₁,g₂) have
[their squared cellwise nested product integral factored into scalar Poisson second
moments](goal). -/
theorem integral_sq_nestedPaired_cellwise_product_eq_prod
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    (lambda₁ lambda₂ : iota → kappa → NNReal)
    (g₁ g₂ : iota → kappa → Nat → Real) :
    (∫ x, (∏ i, ∏ j, g₁ i j (x i j).1 * g₂ i j (x i j).2) ^ 2
        ∂(nestedPairedPoissonMeasure lambda₁ lambda₂)) =
      ∏ i, ∏ j,
        ((∫ n, (g₁ i j n) ^ 2 ∂(poissonMeasure (lambda₁ i j))) *
          (∫ n, (g₂ i j n) ^ 2 ∂(poissonMeasure (lambda₂ i j)))) := by
  let g : NestedPairedPoissonIndex iota kappa → Nat → Real := fun p =>
    Fin.cases (g₁ p.1 p.2.1) (fun _ => g₂ p.1 p.2.1) p.2.2
  have h := integral_sq_nestedPairedCoordinateProduct_eq_prod lambda₁ lambda₂ g
  simp only [nestedPairedCoordinateProduct, g, Fintype.prod_sigma,
    Fin.prod_univ_two, nestedPairedPoissonFlattening_apply_zero,
    nestedPairedPoissonFlattening_apply_one, nestedPairedPoissonRates] at h
  have hone : (1 : Fin 2) = Fin.succ 0 := rfl
  rw [hone] at h
  simpa only [Fin.cases_zero, Fin.cases_succ] using h

end

end Causalean.Mathlib.Probability.PoissonAddOnePoincare.NestedPairedProductMoments

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import CausalSmith.Substrate.NestedPairedPoissonProductMoments.PolynomialGrowth
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Coordinate-product integrals under nested paired Poisson laws

After flattening, products of single-coordinate functions factor into scalar Poisson integrals.
The square identity and integrability criterion are tailored to Poincare energy calculations.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace CausalSmith.Substrate.NestedPairedPoissonProductMoments

noncomputable section

open Causalean.Mathlib.Probability.PoissonAddOnePoincare

/-- A product of scalar functions evaluated on all flattened coordinates of a nested sample. -/
def nestedPairedCoordinateProduct
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    (g : NestedPairedPoissonIndex iota kappa → Nat → Real)
    (x : iota → kappa → Nat × Nat) : Real :=
  ∏ p, g p (nestedPairedPoissonFlattening iota kappa x p)

/-- The integral of a product of flattened coordinate functions factors into scalar
Poisson integrals. -/
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

/-- The integral of the square of a coordinate product is the product of scalar second moments. -/
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

/-- Scalar second-moment integrability makes a flattened coordinate product square-integrable. -/
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

/-- A cellwise product integral factors into the first- and second-count scalar integrals. -/
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

/-- The squared cellwise product integral factors into scalar Poisson second moments. -/
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

end CausalSmith.Substrate.NestedPairedPoissonProductMoments

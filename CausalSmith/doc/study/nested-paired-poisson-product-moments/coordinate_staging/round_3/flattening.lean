/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.Probability.PoissonAddOnePoincare.Tensorization

/-!
# Flattening finite nested arrays of Poisson pairs

This module exposes the measurable equivalence and measure-preserving transport hidden in the
proof of the nested paired-Poisson Poincare inequality.  A nested array with two counts in each
cell is represented as one finite dependent product, with a `Fin 2` tag selecting the count.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Causalean.Mathlib.Probability.PoissonAddOnePoincare.NestedPairedProductMoments

noncomputable section

open Causalean.Mathlib.Probability.PoissonAddOnePoincare

/-- Two [finite index types](hyp:iota,kappa) determine
[the coordinate labels for a flattened nested paired-count array](goal), given by
[a cell label together with a tag for its first or second count](step:1). -/
abbrev NestedPairedPoissonIndex (iota kappa : Type*) :=
  Sigma fun _ : iota => Sigma fun _ : kappa => Fin 2

/-- Two [arrays of nonnegative Poisson rates](hyp:lambda₁,lambda₂) determine
[the rate assigned to each flattened coordinate](goal), given by
[selecting the first or second rate according to that coordinate's count tag](step:1). -/
def nestedPairedPoissonRates
    {iota kappa : Type*} (lambda₁ lambda₂ : iota → kappa → NNReal) :
    NestedPairedPoissonIndex iota kappa → NNReal :=
  fun p => Fin.cases (lambda₁ p.1 p.2.1) (fun _ => lambda₂ p.1 p.2.1) p.2.2

/-- A [finite family of probability laws](hyp:mu) has
[the same product law after regrouping a dependent pair of finite indices](goal). -/
theorem measurePreserving_piCurry_probability
    {alpha : Type*} {beta : alpha → Type*}
    [Fintype alpha] [∀ i, Fintype (beta i)]
    {X : (i : alpha) → beta i → Type*} [∀ i j, MeasurableSpace (X i j)]
    (mu : (i : alpha) → (j : beta i) → Measure (X i j))
    [∀ i j, IsProbabilityMeasure (mu i j)] :
    MeasurePreserving (MeasurableEquiv.piCurry X)
      (Measure.pi fun p : Sigma beta => mu p.1 p.2)
      (Measure.pi fun i => Measure.pi (mu i)) := by
  refine ⟨(MeasurableEquiv.piCurry X).measurable, ?_⟩
  simpa only [Measure.infinitePi_eq_pi] using Measure.infinitePi_map_piCurry mu

/-- Two [finite families of probability laws](hyp:mu,nu),
[coordinatewise measurable equivalences](hyp:e), and the fact that they
[preserve their corresponding laws](hyp:he) transport
[one finite product probability law to the other](goal). -/
theorem measurePreserving_piCongrRight_probability
    {alpha : Type*} [Fintype alpha]
    {X Y : alpha → Type*} [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (mu : (i : alpha) → Measure (X i)) (nu : (i : alpha) → Measure (Y i))
    [∀ i, IsProbabilityMeasure (mu i)] [∀ i, IsProbabilityMeasure (nu i)]
    (e : ∀ i, X i ≃ᵐ Y i) (he : ∀ i, MeasurePreserving (e i) (mu i) (nu i)) :
    MeasurePreserving (MeasurableEquiv.piCongrRight e) (Measure.pi mu) (Measure.pi nu) := by
  refine ⟨(MeasurableEquiv.piCongrRight e).measurable, ?_⟩
  change (Measure.pi mu).map (fun x i => e i (x i)) = Measure.pi nu
  rw [Measure.pi_map_pi fun i => (he i).measurable.aemeasurable]
  congr 1
  funext i
  exact (he i).map_eq

/-- Two [finite index types](hyp:iota,kappa) determine
[a measurable equivalence from a flat count vector to a nested array of count pairs](goal),
given by [currying the two index levels and grouping the two tagged counts in each cell](step:1). -/
def nestedPairedPoissonUnflattening
    (iota kappa : Type*) [Fintype iota] [Fintype kappa] :
    (NestedPairedPoissonIndex iota kappa → Nat) ≃ᵐ
      (iota → kappa → Nat × Nat) :=
  (MeasurableEquiv.piCurry
      (fun (_ : iota) (_ : Sigma fun _ : kappa => Fin 2) => Nat)).trans
    ((MeasurableEquiv.piCongrRight fun _ : iota =>
        MeasurableEquiv.piCurry (fun (_ : kappa) (_ : Fin 2) => Nat)).trans
      (MeasurableEquiv.piCongrRight fun _ : iota =>
        MeasurableEquiv.piCongrRight fun _ : kappa =>
          MeasurableEquiv.piFinTwo (fun _ : Fin 2 => Nat)))

/-- Two [finite index types](hyp:iota,kappa) determine
[a measurable equivalence from a nested array of count pairs to one flat count vector](goal),
given by [the inverse of the canonical unflattening equivalence](step:1). -/
def nestedPairedPoissonFlattening
    (iota kappa : Type*) [Fintype iota] [Fintype kappa] :
    (iota → kappa → Nat × Nat) ≃ᵐ
      (NestedPairedPoissonIndex iota kappa → Nat) :=
  (nestedPairedPoissonUnflattening iota kappa).symm

/-- A [flat count vector](hyp:z) and [selected nested-array cell](hyp:i,j) have
[an unflattened count pair equal to the two tagged flat counts](goal). -/
@[simp] theorem nestedPairedPoissonUnflattening_apply
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    (z : NestedPairedPoissonIndex iota kappa → Nat) (i : iota) (j : kappa) :
    nestedPairedPoissonUnflattening iota kappa z i j =
      (z ⟨i, ⟨j, 0⟩⟩, z ⟨i, ⟨j, 1⟩⟩) := by
  rfl

/-- A [nested count-pair array](hyp:x) and [selected cell](hyp:i,j) have
[a first-tag flattened coordinate equal to that cell's first count](goal). -/
@[simp] theorem nestedPairedPoissonFlattening_apply_zero
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    (x : iota → kappa → Nat × Nat) (i : iota) (j : kappa) :
    nestedPairedPoissonFlattening iota kappa x ⟨i, ⟨j, 0⟩⟩ = (x i j).1 := by
  rfl

/-- A [nested count-pair array](hyp:x) and [selected cell](hyp:i,j) have
[a second-tag flattened coordinate equal to that cell's second count](goal). -/
@[simp] theorem nestedPairedPoissonFlattening_apply_one
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    (x : iota → kappa → Nat × Nat) (i : iota) (j : kappa) :
    nestedPairedPoissonFlattening iota kappa x ⟨i, ⟨j, 1⟩⟩ = (x i j).2 := by
  rfl

/-- Two [arrays of nonnegative Poisson rates](hyp:lambda₁,lambda₂) have
[a flat independent-Poisson product law transported to their nested paired-count law](goal). -/
theorem measurePreserving_nestedPairedPoissonUnflattening
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    (lambda₁ lambda₂ : iota → kappa → NNReal) :
    MeasurePreserving (nestedPairedPoissonUnflattening iota kappa)
      (poissonPi (nestedPairedPoissonRates lambda₁ lambda₂))
      (nestedPairedPoissonMeasure lambda₁ lambda₂) := by
  -- Follow the three public transports above: curry the outer Sigma, curry each inner
  -- Sigma, and turn each `Fin 2 → Nat` into a pair.
  let flatIndex := Sigma fun _ : iota => Sigma fun _ : kappa => Fin 2
  let flatLambda : flatIndex → NNReal := fun p =>
    Fin.cases (lambda₁ p.1 p.2.1) (fun _ => lambda₂ p.1 p.2.1) p.2.2
  let e₁ := MeasurableEquiv.piCurry
    (fun (_ : iota) (_ : Sigma fun _ : kappa => Fin 2) => Nat)
  let e₂ := MeasurableEquiv.piCongrRight (fun _ : iota =>
    MeasurableEquiv.piCurry (fun (_ : kappa) (_ : Fin 2) => Nat))
  let e₃ := MeasurableEquiv.piCongrRight (fun _ : iota =>
    MeasurableEquiv.piCongrRight (fun _ : kappa =>
      MeasurableEquiv.piFinTwo (fun _ : Fin 2 => Nat)))
  let mu₀ : Measure (flatIndex → Nat) := poissonPi flatLambda
  let mu₁ : Measure (iota → (Sigma fun _ : kappa => Fin 2) → Nat) :=
    Measure.pi fun i => Measure.pi fun q => poissonMeasure (flatLambda ⟨i, q⟩)
  let mu₂ : Measure (iota → kappa → Fin 2 → Nat) :=
    Measure.pi fun i => Measure.pi fun j => Measure.pi fun b =>
      poissonMeasure (flatLambda ⟨i, ⟨j, b⟩⟩)
  let mu₃ : Measure (iota → kappa → Nat × Nat) :=
    nestedPairedPoissonMeasure lambda₁ lambda₂
  have hmp₁ : MeasurePreserving e₁ mu₀ mu₁ := by
    simpa [e₁, mu₀, mu₁, poissonPi, flatIndex] using
      (measurePreserving_piCurry_probability
        (fun (i : iota) (q : Sigma fun _ : kappa => Fin 2) =>
          poissonMeasure (flatLambda ⟨i, q⟩)))
  have hmp₂ : MeasurePreserving e₂ mu₁ mu₂ := by
    apply measurePreserving_piCongrRight_probability
    intro i
    simpa [mu₁, mu₂, e₂] using
      (measurePreserving_piCurry_probability
        (fun (j : kappa) (b : Fin 2) =>
          poissonMeasure (flatLambda ⟨i, ⟨j, b⟩⟩)))
  have hmp₃ : MeasurePreserving e₃ mu₂ mu₃ := by
    apply measurePreserving_piCongrRight_probability
    intro i
    apply measurePreserving_piCongrRight_probability
    intro j
    convert (measurePreserving_piFinTwo (fun b : Fin 2 =>
      poissonMeasure (Fin.cases (lambda₁ i j) (fun _ => lambda₂ i j) b))) using 1
    · simp
      congr 2
  have hmp := hmp₃.comp (hmp₂.comp hmp₁)
  change MeasurePreserving (e₃ ∘ e₂ ∘ e₁) mu₀ mu₃
  exact hmp

/-- Two [arrays of nonnegative Poisson rates](hyp:lambda₁,lambda₂) have
[their nested paired-count law transported to the corresponding flat independent-Poisson
product law](goal). -/
theorem measurePreserving_nestedPairedPoissonFlattening
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    (lambda₁ lambda₂ : iota → kappa → NNReal) :
    MeasurePreserving (nestedPairedPoissonFlattening iota kappa)
      (nestedPairedPoissonMeasure lambda₁ lambda₂)
      (poissonPi (nestedPairedPoissonRates lambda₁ lambda₂)) := by
  exact MeasurePreserving.symm (nestedPairedPoissonUnflattening iota kappa)
    (measurePreserving_nestedPairedPoissonUnflattening lambda₁ lambda₂)

/-- A [flat count vector](hyp:z) and [selected nested-array cell](hyp:i,j) have
[a first-tag increment that unflattens to adding one to that cell's first count](goal). -/
theorem nestedPairedPoissonUnflattening_update_fst
    {iota kappa : Type*}
    [Fintype iota] [DecidableEq iota] [Fintype kappa] [DecidableEq kappa]
    (z : NestedPairedPoissonIndex iota kappa → Nat) (i : iota) (j : kappa) :
    nestedPairedPoissonUnflattening iota kappa
        (Function.update z ⟨i, ⟨j, 0⟩⟩ (z ⟨i, ⟨j, 0⟩⟩ + 1)) =
      Function.update (nestedPairedPoissonUnflattening iota kappa z) i
        (Function.update (nestedPairedPoissonUnflattening iota kappa z i) j
          ((nestedPairedPoissonUnflattening iota kappa z i j).1 + 1,
            (nestedPairedPoissonUnflattening iota kappa z i j).2)) := by
  funext i' j'
  rw [nestedPairedPoissonUnflattening_apply]
  by_cases hi : i' = i <;> by_cases hj : j' = j
  · subst i'
    subst j'
    simp
  · subst i'
    simp [hj]
  · simp [hi]
  · simp [hi]

/-- A [flat count vector](hyp:z) and [selected nested-array cell](hyp:i,j) have
[a second-tag increment that unflattens to adding one to that cell's second count](goal). -/
theorem nestedPairedPoissonUnflattening_update_snd
    {iota kappa : Type*}
    [Fintype iota] [DecidableEq iota] [Fintype kappa] [DecidableEq kappa]
    (z : NestedPairedPoissonIndex iota kappa → Nat) (i : iota) (j : kappa) :
    nestedPairedPoissonUnflattening iota kappa
        (Function.update z ⟨i, ⟨j, 1⟩⟩ (z ⟨i, ⟨j, 1⟩⟩ + 1)) =
      Function.update (nestedPairedPoissonUnflattening iota kappa z) i
        (Function.update (nestedPairedPoissonUnflattening iota kappa z i) j
          ((nestedPairedPoissonUnflattening iota kappa z i j).1,
            (nestedPairedPoissonUnflattening iota kappa z i j).2 + 1)) := by
  funext i' j'
  rw [nestedPairedPoissonUnflattening_apply]
  by_cases hi : i' = i <;> by_cases hj : j' = j
  · subst i'
    subst j'
    simp
  · subst i'
    simp [hj]
  · simp [hi]
  · simp [hi]

end

end Causalean.Mathlib.Probability.PoissonAddOnePoincare.NestedPairedProductMoments

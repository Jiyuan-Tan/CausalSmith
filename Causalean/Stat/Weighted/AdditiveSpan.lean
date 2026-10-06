/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Additive two-axis spans

For a generic index `R` equipped with two projections `f₁ : R → A` and
`f₂ : R → B`, the **additive span** is the linear subspace of `R → ℝ`
consisting of arrays of the form

    h r = a (f₁ r) + b (f₂ r)

for some `a : A → ℝ` and `b : B → ℝ`.  Specialized to `R = I × T`,
`f₁ = Prod.fst`, `f₂ = Prod.snd`, this is the classical two-way
fixed-effect subspace `H_twfe` used in `Causalean/Panel/FixedEffect.lean`
and across panel estimand-characterization arguments that residualize against
unit and time nuisance components.

The generic feature-map formulation lets panel and non-panel applications use
the same additive-subspace interface.

## Main definitions

* `AdditiveSpan f₁ f₂` — the additive-span subspace of `R → ℝ`.
* `twoAxisAdditiveSpan I T` — specialization to `R = I × T` with
  `f₁ = Prod.fst`, `f₂ = Prod.snd`.
* `IsUnitTimeAdditive` — membership predicate for the two-axis unit/time case.

## Main lemmas

* `AdditiveSpan.const_mem` — constants live in the additive span.
* `AdditiveSpan.finiteDimensional` — under `[Fintype R]` the span is
  finite-dimensional.
-/

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Additive Two-Axis Spans

This file defines `AdditiveSpan`, the linear subspace of finite arrays that
decompose additively through two index maps. It provides the generic algebra
behind two-way fixed-effect nuisance spaces, the product-index specialization
`twoAxisAdditiveSpan`, and the unit/time membership predicate
`IsUnitTimeAdditive`. The main public facts expose membership, constants in the
span, and finite dimensionality over a finite support. -/

@[expose] public section

open scoped BigOperators

namespace Causalean
namespace Stat.Weighted

/-- Given [an index set](hyp:R), [two feature sets](hyp:A,B), and
[two maps into those feature sets](hyp:f₁,f₂), the [additive span](goal) is
the real linear subspace of arrays that split as a function of the first feature
plus a function of the second feature. -/
def AdditiveSpan {R A B : Type*} (f₁ : R → A) (f₂ : R → B) :
    Submodule ℝ (R → ℝ) where
  carrier := { h | ∃ a : A → ℝ, ∃ b : B → ℝ, ∀ r : R, h r = a (f₁ r) + b (f₂ r) }
  zero_mem' := ⟨fun _ => 0, fun _ => 0, by intro r; simp⟩
  add_mem' := by
    rintro h₁ h₂ ⟨a₁, b₁, hh₁⟩ ⟨a₂, b₂, hh₂⟩
    refine ⟨a₁ + a₂, b₁ + b₂, ?_⟩
    intro r
    simp [hh₁ r, hh₂ r, Pi.add_apply]; ring
  smul_mem' := by
    rintro s h ⟨a, b, hh⟩
    refine ⟨s • a, s • b, ?_⟩
    intro r
    simp [hh r, Pi.smul_apply, smul_eq_mul]; ring

namespace AdditiveSpan

variable {R A B : Type*} {f₁ : R → A} {f₂ : R → B}

/-- [A function lies in the additive span exactly when it splits by feature](goal):
there are component functions `a` and `b` with
`h r = a (f₁ r) + b (f₂ r)` at every point. -/
lemma mem_iff {h : R → ℝ} :
    h ∈ AdditiveSpan f₁ f₂ ↔
      ∃ a : A → ℝ, ∃ b : B → ℝ, ∀ r : R, h r = a (f₁ r) + b (f₂ r) :=
  Iff.rfl

/-- [The constant function belongs to the two-feature additive span](goal),
witnessed by taking the `f₁`-component function constantly `c₀` and the
`f₂`-component function constantly `0`. -/
lemma const_mem (f₁ : R → A) (f₂ : R → B) (c₀ : ℝ) :
    (fun _ : R => c₀) ∈ AdditiveSpan f₁ f₂ := by
  refine ⟨fun _ => c₀, fun _ => 0, ?_⟩
  intro r; simp

/-- Under `[Finite R]` the additive span sits inside the
finite-dimensional ambient space `R → ℝ`, hence is finite-dimensional. -/
instance finiteDimensional [Finite R] :
    Module.Finite ℝ (AdditiveSpan f₁ f₂) := by
  set_option linter.style.haveILetI false in
    letI : Fintype R := Fintype.ofFinite R
    letI : Module.Finite ℝ (R → ℝ) := by infer_instance
    exact Module.Finite.of_injective (AdditiveSpan f₁ f₂).subtype
      (Subtype.val_injective)

end AdditiveSpan

/-- Given [a set of units](hyp:I) and [a set of periods](hyp:T), the [two-axis additive span](goal)
is the real linear subspace of unit-period arrays that can be written as the sum of a
unit-specific real-valued function and a period-specific real-valued function. -/
def twoAxisAdditiveSpan (I T : Type*) : Submodule ℝ ((I × T) → ℝ) :=
  AdditiveSpan (Prod.fst : I × T → I) (Prod.snd : I × T → T)

/-- Given [a set of units](hyp:Unit), [a set of periods](hyp:Time), and
[a real-valued unit-period array](hyp:h), the [unit-time additive condition](goal)
holds precisely when
[unit and period functions sum to the array at every pair](step:1). -/
def IsUnitTimeAdditive {Unit Time : Type*} (h : Unit → Time → ℝ) : Prop :=
  ∃ a : Unit → ℝ, ∃ b : Time → ℝ, ∀ i t, h i t = a i + b t

end Stat.Weighted
end Causalean

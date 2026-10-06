/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Conditional-expectation lemmas under `CondIndepFun`

* `condExp_sup_comap_eq_of_condIndep` — drop-of-conditioning: if `g ⟂ f | m`,
  conditioning `h ∘ g` on `m ⊔ σ(f)` equals conditioning on `m` alone.
* `condExp_mul_of_condIndep` — product factorization: `μ[(u∘f)(v∘g)|m] =ᵐ μ[u∘f|m]·μ[v∘g|m]`.
* `condIndepFun_weak_union_of_prodMk` — weak union via `prodMk`: `W ⟂ (V,A)|m ⟹ W ⟂ V|(m⊔σA)`.
* `condIndepFun_prodMk_of_measurable_left` — extension by an `m`-measurable function.
* `condIndepFun_contraction_of_prodMk` — contraction via a product right side.
-/

module
public import Causalean.Mathlib.Probability.Independence.Conditional.CondExp_Part2
/-!
Conditional-independence consequences for conditional expectations, developed in two stages. Use these identities to simplify conditional means when the relevant variables are conditionally independent.
-/

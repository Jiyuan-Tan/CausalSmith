/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bridge: bounded loss + Rademacher complexity ⇒ `LocalEmpProcessModulus`

This bridge discharges the `LocalEmpProcessModulus` hypothesis used by
`OrthogonalLearning/OracleInequality.lean` from concrete data-generating
assumptions. No upstream code lives here; this file consumes the
`Causalean.Stat.Concentration.{Rademacher, BoundedDifference, McDiarmid,
Symmetrization, Separable}` headlines together with the orthogonal
statistical-learning oracle-inequality predicate.

## Output

Under
* a uniform bound `|ℓ z θ g| ≤ b` for `θ ∈ Θ_set`,
* a population Rademacher-complexity bound `R_n` for the centred loss
  class `{z ↦ ℓ z θ g − ℓ z θ₀ g : θ ∈ Θ_set}` measured on the estimation
  fold,
* countability / separability of `Θ_set` (handled via
  `Causalean.Stat.Concentration.Separable`),

we conclude `LocalEmpProcessModulus S S_iid split ρ δ g` with
`ρ n := √(2 R_n + 2b * Real.sqrt (2 * Real.log (1 / δ) / |B(n)|))`
when the estimation fold is nonempty, and the boundary value
`ρ n := √(2b)` when `|B(n)| = 0`.

Only the constant slot `(ρ n)^2` is filled — the `ρ n * ‖θ − θ₀‖` slot
of the modulus inequality is satisfied by the trivial monotonicity
`ρ n * ‖θ − θ₀‖ ≥ 0`.  This is a deliberate, non-localized realisation:
sharper localized rates (Foster–Syrgkanis Lemma 14) live in the sibling
file `OrthogonalLearning/LocalEmpProcess/Localized.lean`.

## Headline schema

```
theorem localEmpProcessModulus_of_bounded_rademacher
    (S : LearningSystem Ω μ Z P_Z Θ G) (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid) {b : ℝ} (hb : 0 ≤ b)
    (g : G) (hg_bdd : ∀ z, ∀ θ ∈ S.Θ_set, |S.ℓ z θ g| ≤ b)
    (R : ℕ → ℝ) (hR : RademacherBound S S_iid split g R)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    LocalEmpProcessModulus S S_iid split
      (fun n => Real.sqrt
        (if (split.foldB n).card = 0 then 2 * b
         else 2 * R n + 2 * b *
          Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) δ g
```
-/

module
public import Causalean.Estimation.OrthogonalLearning.LocalEmpProcess.Rademacher_Part3
/-!
# Global Rademacher bridges for orthogonal learning

This barrel exports the fixed-nuisance bridges from bounded global Rademacher
complexity to `LocalEmpProcessModulus`, including everywhere-bounded,
almost-everywhere-bounded, and singleton-class variants.
-/

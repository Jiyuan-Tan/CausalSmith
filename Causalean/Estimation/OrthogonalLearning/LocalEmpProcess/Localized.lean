/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bridge: localized regime ⇒ `LocalEmpProcessModulus`

This bridge discharges the `LocalEmpProcessModulus` hypothesis used by
`OrthogonalLearning/OracleInequality.lean` from a **localized regime**, i.e. from
data-generating assumptions that have a sub-root upper envelope on the local
Rademacher complexity of the centred loss class.

Sibling: `Causalean/Estimation/OrthogonalLearning/LocalEmpProcess/Rademacher.lean` realises the same predicate
under a global Rademacher bound. Downstream callers pick
whichever bridge fits the problem at hand; the localized version
includes a countable-class critical-radius bridge for settings where the
`‖θ−θ₀‖` slot of the modulus inequality matters.

References:
* Foster, Syrgkanis, *Orthogonal statistical learning*, Ann. Statist.
  51 (2023) 879–908, Lemma 14 (the localized rate `O(δ_n)`
  with critical radius `δ_n`).
* Bartlett, Bousquet, Mendelson, *Local Rademacher complexities*,
  Ann. Statist. 33 (2005) 1497–1537, Theorem 3.3.

## Output

The file provides three bridge families.

* `localEmpProcessModulus_of_localized_bounded` and its a.e. analogue give a
  low-hypothesis fallback with the conservative deterministic envelope
  `ρ n := √(2 · b)`.
* `localEmpProcessModulus_of_localized_sharp` gives the separable-class
  Foster-Syrgkanis critical-radius envelope
  `ρ n := (10 · L + 3) · criticalRadius (ψ |B(n)|)` on nonempty fold-B samples.
* `localEmpProcessModulus_of_localized_sharp_ae` obtains the same sharp envelope
  from an a.e. centred-loss bound by clamping the centred loss on a conull set
  and transferring the event back to the original system.

## Headline schema

```
theorem localEmpProcessModulus_of_localized
    (S : LearningSystem Ω μ Z P_Z Θ G) (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid) (g : G)
    {ψ : ℕ → ℝ → ℝ} {b : ℝ}
    (hreg : LocalizedRademacherRegime S S_iid split g idx norm ψ b)
    (hpop_center : ∀ θ ∈ S.Θ_set, |S.L θ g - S.L S.θ₀ g| ≤ b)
    {δ : ℝ} (_hδ : 0 < δ) (_hδ' : δ ≤ 1) :
    LocalEmpProcessModulus S S_iid split
      (fun _n => Real.sqrt (2 * b)) δ g
```
-/

module
public import Causalean.Estimation.OrthogonalLearning.LocalEmpProcess.Localized_Part3
/-!
# Localized Rademacher bridges for orthogonal learning

This barrel exports the localized-regime predicates, conservative bounded-loss
bridges, sharp critical-radius bridges, and singleton-class specialization from
the three `Localized_Part` modules.
-/

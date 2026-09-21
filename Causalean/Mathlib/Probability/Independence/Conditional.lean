/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Conditional-independence interface

Aggregates the conditional-expectation, almost-everywhere lifting, density, and
transport submodules.

Sub-modules:
* `Conditional.CondExp` — conditional-expectation identities and semigraphoid lemmas.
* `Conditional.AELift` — almost-everywhere equality lifts under overlap.
* `Conditional.Integrability` — positivity and integrability from indicator identities.
* `Conditional.ThreeBlockDensity` — conditional independence from factorized densities.
* `Conditional.Transport` — transport along measurable maps and a.e. retractions.
-/

module
public import Causalean.Mathlib.Probability.Independence.Conditional.AELift
public import Causalean.Mathlib.Probability.Independence.Conditional.CondExp
public import Causalean.Mathlib.Probability.Independence.Conditional.Integrability
public import Causalean.Mathlib.Probability.Independence.Conditional.ThreeBlockDensity
public import Causalean.Mathlib.Probability.Independence.Conditional.Transport



/-!
This file gathers conditional-independence tools, including conditional-expectation
identities, almost-everywhere equality transfer under overlap, factorized-density
criteria, and transport results.

It re-exports
`Causalean.Mathlib.Probability.Independence.Conditional.CondExp` for
drop-of-conditioning, product factorization, weak union, extension, and contraction;
`Causalean.Mathlib.Probability.Independence.Conditional.AELift` for restricted-set
equality transfer; `Integrability` for consequences of indicator conditional
expectation identities; `ThreeBlockDensity` for a density-factorization criterion;
and `Transport` for invariance under changes of representation.
-/

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Analysis.NormedSpace.Duality.L1Linf.Basic
public import Causalean.Mathlib.Analysis.NormedSpace.Duality.L1Linf.Duality
public import Causalean.Mathlib.Analysis.NormedSpace.Duality.L1Linf.HahnBanachSetup
public import Causalean.Mathlib.Analysis.NormedSpace.Duality.L1Linf.NonemptyDuality
public import Causalean.Mathlib.Analysis.NormedSpace.Duality.L1Linf.StrongDuality
public import Causalean.Mathlib.Analysis.NormedSpace.Duality.L1Linf.WeakDuality

/-!
Finite-dimensional ℓ¹/ℓ∞ duality for node-sampled polynomials, from the moment-system setup
and Hahn–Banach construction through weak and strong duality. The main identity equates the
least ℓ¹ norm of endpoint-contrast weights with a supremum over node-bounded polynomials.
-/

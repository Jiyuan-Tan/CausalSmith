/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Concentration.Rademacher.Contraction.Absolute
public import Causalean.Stat.Concentration.Rademacher.Contraction.Coordinatewise
public import Causalean.Stat.Concentration.Rademacher.Contraction.Signed

/-! # Ledoux–Talagrand contraction for Rademacher complexity

The contraction principle: composing every function of a class with an L-Lipschitz map φ
multiplies its empirical Rademacher complexity by at most L in the signed form (no absolute
value inside the supremum), and by at most 2L in the absolute-value form when φ(0) = 0. The
results hold for finite classes and, under a uniform bound on the class, for arbitrary index
sets; a coordinatewise version allows a different L-Lipschitz map at each sample point.

## Main results

* `rademacher_contraction` (`Contraction.Signed`) — signed form, finite class, constant L.
* `rademacher_contraction_abs` (`Contraction.Absolute`) — absolute-value form, finite class,
  constant 2L, for φ with φ(0) = 0.
* `empiricalRademacherComplexity_contraction_abs_of_bddAbove` — the absolute-value form for an
  arbitrary nonempty index set and a uniformly bounded class.
* `rademacher_contraction_coordinatewise`, `rademacher_contraction_abs_coordinatewise`
  (`Contraction.Coordinatewise`) — sample-point-dependent maps φₖ, constants L and 2L.
* `empiricalRademacherComplexity_smul_class`, `empiricalRademacherComplexity_sub_le` — scaling
  a class by c scales the complexity by |c|; the complexity of a class of differences is at most
  the sum of the two complexities.
-/

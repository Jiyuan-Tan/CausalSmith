/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.Mathlib.Probability.Independence.Conditional.AELift
public import Causalean.Mathlib.Probability.Independence.Conditional.CondExp
public import Causalean.Mathlib.Probability.Independence.Conditional.DensityIntersection
public import Causalean.Mathlib.Probability.Independence.Conditional.FiniteProductResidual
public import Causalean.Mathlib.Probability.Independence.Conditional.Integrability
public import Causalean.Mathlib.Probability.Independence.Conditional.JoinedBlockProduct
public import Causalean.Mathlib.Probability.Independence.Conditional.ShiftedBlockCrossMoment
public import Causalean.Mathlib.Probability.Independence.Conditional.ShiftedBlockMoments
public import Causalean.Mathlib.Probability.Independence.Conditional.ShiftedJoinedScore
public import Causalean.Mathlib.Probability.Independence.Conditional.ThreeBlockDensity
public import Causalean.Mathlib.Probability.Independence.Conditional.ThreeBlockProduct
public import Causalean.Mathlib.Probability.Independence.Conditional.ThreeBlockShiftedProduct
public import Causalean.Mathlib.Probability.Independence.Conditional.ThreeBlockShiftedProduct.FourCoordinate
public import Causalean.Mathlib.Probability.Independence.Conditional.Transport






/-!
# Conditional independence: conditional-expectation identities and graphoid rules

Tools for working with conditional independence of random variables and σ-algebras. If X and Y
are conditionally independent given Z, then conditioning an integrable function of X on (Z, Y)
is the same as conditioning on Z, and conditional expectations of products factorize. The
semigraphoid rules weak union and contraction are proved, and the intersection rule is proved
for laws with a strictly positive density with respect to a product measure. Conditional
independence is characterized by factorization of a joint density and is preserved under
pushforward along a measurable map.

## Contents

* `Conditional.CondExp` — dropping independent conditioning information
  (`condExp_sup_comap_eq_of_condIndep`), product factorization (`condExp_mul_of_condIndep`),
  weak union and contraction (`condIndepFun_weak_union_of_prodMk`,
  `condIndepFun_contraction_of_prodMk`).
* `Conditional.DensityIntersection` — conditional independence as density factorization
  (`condIndepFun_threeBlock_iff_factors`) and the intersection rule under a positive density
  (`condIndepFun_intersection_of_positiveDensity`).
* `Conditional.ThreeBlockDensity` — a density factorizing through the conditioning block gives
  conditional independence of the other two blocks.
* `Conditional.Transport` — `condIndepFun_of_map`, transfer to a pushforward measure.
* `Conditional.AELift` — an almost-everywhere equality on a set E extends to the whole space
  when the agreement set is measurable for a σ-algebra whose sets that are null within E are
  null (an overlap condition; `ae_eq_of_ae_eq_restrict_arm`).
* `Conditional.Integrability` — positivity and integrability on a stratum from conditional
  expectations of indicators.
* `Conditional.FiniteProductResidual` — in an i.i.d. sample, a residual with conditional mean
  zero given its own covariate keeps mean zero given all other records as well.
* `Conditional.ThreeBlockProduct`, `Conditional.JoinedBlockProduct`,
  `Conditional.ShiftedBlockMoments`, `Conditional.ShiftedBlockCrossMoment`,
  `Conditional.ShiftedJoinedScore`, `Conditional.ThreeBlockShiftedProduct` — conditional means,
  cross moments and covariances, given a training block, of products of scores evaluated on
  disjoint held-out blocks of a product sample.

This file only gathers the modules above.
-/

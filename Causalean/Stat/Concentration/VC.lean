/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Concentration.VC.Algebra
public import Causalean.Stat.Concentration.VC.Basic
public import Causalean.Stat.Concentration.VC.BasicVarianceAdaptiveVCExpectedMaximal
public import Causalean.Stat.Concentration.VC.Cover
public import Causalean.Stat.Concentration.VC.Empirical
public import Causalean.Stat.Concentration.VC.EmpiricalCover
public import Causalean.Stat.Concentration.VC.EntropyChaining
public import Causalean.Stat.Concentration.VC.ExpectedMaximal
public import Causalean.Stat.Concentration.VC.Geometry
public import Causalean.Stat.Concentration.VC.MaximalInequalities
public import Causalean.Stat.Concentration.VC.Parametric
public import Causalean.Stat.Concentration.VC.Rademacher
public import Causalean.Stat.Concentration.VC.RadialPolynomial
public import Causalean.Stat.Concentration.VC.Score
public import Causalean.Stat.Concentration.VC.Separability
public import Causalean.Stat.Concentration.VC.Trace

/-! # VC classes, pseudo-dimension and maximal inequalities

Uniform entropy and maximal inequalities for VC-type classes of real functions. A class has
pseudo-dimension at most d when its subgraphs form a class of sets of VC dimension at most d. For
a measurable class with pseudo-dimension at most d and envelope U, the L²(Q) covering number at
radius εU is at most (16/ε)^(8(d+1)), uniformly over all probability measures Q. For a countable
class bounded by U with L²(P) norms at most σ < U and polynomial covering numbers (A/ε)^v, the
expected supremum of the centred empirical process over n iid draws is at most a universal
constant times σ√(vL/n) + vUL/n with L = log max(e, AU/σ): the leading term scales with the
standard deviation, not the envelope.

## Main results

* `real_vcSubgraph_l2_covering` (`VC.Basic`) — the uniform polynomial covering bound.
* `varianceAdaptiveExpectedMaximal_le`, `varianceAdaptiveRademacherComplexity_le`
  (`VC.ExpectedMaximal`, `VC.Rademacher`) — the variance-adaptive maximal inequality and its
  Rademacher-complexity form, with explicit constants 16384 and 8192.
* `HasPolynomialL2Cover.add`, `.mul`, `.finSum`, `.finProd`, `.pullback`, `.mulIndicator`
  (`VC.Algebra`, `VC.Cover`, `VC.Parametric`) — polynomial covering is preserved by sums,
  products, reparametrization and multiplication by indicators of a VC class of sets.
* `linearSignClass_hasVCAtMost`, `booleanCombination_hasVCAtMost`,
  `euclideanClosedBall_hasVCAtMost` (`VC.Trace`, `VC.Geometry`) — VC bounds for linear
  threshold classifiers, Boolean combinations and Euclidean balls.
* `linearParameterClass_hasPolynomialL2Cover`, `radialResidualScore_hasPolynomialL2Cover`
  (`VC.Parametric`, `VC.Score`) — bounded linear classes and radial-polynomial score classes.
* `real_vcSubgraph_dudley_example`, `vcEntropy_chaining_bound` (`VC.Empirical`,
  `VC.EntropyChaining`) — the link to Dudley's entropy integral and the chaining bound.
-/

public section

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Goodman-Bacon pairwise algebra layer

**Role in the folder.** *Finite-algebra support (not a headline).* Reduction
machinery feeding the algebraic headline `AlgebraicDecomposition.lean`. See
`StaggeredTWFEDecomposition.lean` for the folder layer-map.

This file sits between the paper-agnostic finite weighted identities in
`Causalean/Stat/Weighted/NormalizedWeights.lean` and the headline
Goodman-Bacon decomposition in `AlgebraicDecomposition.lean`.

It exposes the pairwise centered-treatment contributions that the denominator
and numerator identities should first reduce to before the adoption-window
case split into TN / EL / LE comparisons.
-/

module
public import Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition.Pairwise.Algebra
public import Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition.Pairwise.GoodmanBacon

/-! # Goodman-Bacon Pairwise Algebra

This file reduces Goodman-Bacon denominator and numerator terms to ordered-pair
centered-treatment contributions. It is the algebraic bridge between generic
finite weighted covariance identities and the adoption-window case analysis that
produces the three comparison types in the decomposition. -/

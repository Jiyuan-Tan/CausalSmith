/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.LinearAlgebra.Tensor.SymmetricPencil.Basic
public import Causalean.Mathlib.LinearAlgebra.Tensor.SymmetricPencil.Conditioning
public import Causalean.Mathlib.LinearAlgebra.Tensor.SymmetricPencil.Main
public import Causalean.Mathlib.LinearAlgebra.Tensor.SymmetricPencil.Pencil
public import Causalean.Mathlib.LinearAlgebra.Tensor.SymmetricPencil.Projectors
public import Causalean.Mathlib.LinearAlgebra.Tensor.SymmetricPencil.Recovery
public import Causalean.Mathlib.LinearAlgebra.Tensor.SymmetricPencil.SpectralMatching

/-!
Recovery of the rank-one factors of a symmetric tensor from its pencil of contracted slices:
spectral projectors, quantitative conditioning of the eigendecomposition, matching of eigenvalues
across slices, and trace-coordinate recovery of scaled columns. Under the final theorem's unit-norm
and positive-orientation hypotheses, normalization removes the scaling ambiguity and leaves only a
column permutation.
-/

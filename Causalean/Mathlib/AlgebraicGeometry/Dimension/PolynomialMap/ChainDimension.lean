/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.AlgebraicGeometry.Dimension.PolynomialMap.Irreducibility

/-!
# Ambient closed-chain dimension in complex affine space

This file defines an ambient closed-chain rank using strict chains of nonempty
irreducible subsets that are closed in the surrounding affine space.  On an
affine-closed locus this is its usual Zariski dimension; on an arbitrary
nonclosed subset it is not the dimension of the induced Zariski topology.
-/

@[expose] public section

namespace Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension

noncomputable section

/-- For [a coordinate index set](hyp:ι), [a nonnegative integer $d$](hyp:d), and
[a subset $Z$ of the corresponding complex affine space](hyp:Z),
[the ambient affine-closed-chain rank of $Z$ is exactly $d$](goal) when
[a strict chain of $d+1$ ambient-closed irreducible subsets of $Z$ exists](step:1),
and
[no such chain of $d+2$ subsets exists](step:2).

When `Z` is affine-closed, this is its usual Zariski dimension.  For nonclosed
`Z`, it counts only subsets closed in the ambient affine space, not subsets
closed in the subspace topology on `Z`, so it is not ordinary Zariski
dimension of `Z`. -/
def HasAffineZariskiDimension {ι : Type*} (d : ℕ) (Z : Set (ι → ℂ)) : Prop :=
  (∃ chain : Fin (d + 1) → Set (ι → ℂ),
      StrictMono chain ∧
      (∀ i, IsIrreducibleAffineClosed (chain i)) ∧
      (∀ i, chain i ⊆ Z)) ∧
  ¬ ∃ chain : Fin (d + 2) → Set (ι → ℂ),
      StrictMono chain ∧
      (∀ i, IsIrreducibleAffineClosed (chain i)) ∧
      (∀ i, chain i ⊆ Z)

end

end Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension

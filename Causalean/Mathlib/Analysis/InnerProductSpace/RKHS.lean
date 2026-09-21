/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.Analysis.InnerProductSpace.Basic

/-! # Abstract reproducing representers

Mathlib's `RKHS` class describes Hilbert spaces continuously embedded in a
function space and constructs kernel functions under completeness assumptions.
The `HasReproducingRepresenters` proposition here records only the identity
`f x = ⟪f, kₓ⟫` for a supplied evaluation and representer map. It does not
assert that evaluation embeds `H` into a function space. This is the interface
consumed by the representer theorem and the representer-ball Rademacher bound.
-/

@[expose] public section

namespace Causalean.ML

/-- [A real inner-product space](hyp:H) has reproducing representers for [a domain](hyp:X),
[an evaluation map](hyp:feval), and [a representer map](hyp:representer) when
[evaluation equals inner product against the point's representer](hyp:reproducing). This does
not assert that evaluation embeds the space into a function space. -/
structure HasReproducingRepresenters (X H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    (feval : H → X → ℝ) (representer : X → H) : Prop where
  /-- The reproducing identity `f x = ⟪f, kₓ⟫`. -/
  reproducing : ∀ (f : H) (x : X), feval f x = inner ℝ f (representer x)

end Causalean.ML

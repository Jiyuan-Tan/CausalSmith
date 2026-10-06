/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.ML.Core
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.MetricSpace.Lipschitz

/-! # Neural-network layers

A dense (affine) layer `x ↦ W x + b` and an activation function carrying its
Lipschitz constant.  These are the building blocks composed in
`NeuralNet/FeedForward.lean`.
-/

@[expose] public section

namespace Causalean.ML

open Matrix

/-- A dense affine layer bundles [a weight matrix](hyp:W) and [a bias vector](hyp:b) determining
the map $x \mapsto Wx + b$ from `Fin m` inputs to `Fin n` outputs. -/
structure DenseLayer (m n : ℕ) where
  /-- The weight matrix. -/
  W : Matrix (Fin n) (Fin m) ℝ
  /-- The bias vector. -/
  b : Fin n → ℝ

/-- [Dense-layer evaluation](goal) sends [an input vector](hyp:x) through [an affine layer](hyp:L),
producing [one output coordinate as the weighted input sum plus its bias](step:1). The layer maps
[the stated input and output dimensions](hyp:m,n). -/
def DenseLayer.eval {m n : ℕ} (L : DenseLayer m n) (x : Fin m → ℝ) : Fin n → ℝ :=
  fun j => (L.W *ᵥ x) j + L.b j

/-- An activation function bundles [a scalar map](hyp:act) together with [a Lipschitz
constant](hyp:lip) and the certificate that [the map is Lipschitz with that
constant](hyp:isLipschitz) (e.g. ReLU, sigmoid, and tanh are all `1`-Lipschitz). -/
structure Activation where
  /-- The scalar activation. -/
  act : ℝ → ℝ
  /-- A Lipschitz constant for the activation. -/
  lip : NNReal
  /-- Proof that `act` is `lip`-Lipschitz. -/
  isLipschitz : LipschitzWith lip act

/-- [Coordinatewise activation](goal) transforms [an input vector](hyp:x) by
[applying the scalar activation coordinatewise](step:1), using [the activation bundle](hyp:σ) at
[the chosen finite dimension](hyp:n). -/
def Activation.applyVec {n : ℕ} (σ : Activation) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j => σ.act (x j)

end Causalean.ML

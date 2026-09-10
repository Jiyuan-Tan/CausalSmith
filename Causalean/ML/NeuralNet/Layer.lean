/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Core
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.MetricSpace.Lipschitz

/-! # Neural-network layers

A dense (affine) layer `x ↦ W x + b` and an activation function carrying its
Lipschitz constant.  These are the building blocks composed in
`NeuralNet/FeedForward.lean`.
-/

namespace Causalean.ML

open Matrix

/-- A dense affine layer bundles [a weight matrix](hyp:W) and [a bias vector](hyp:b) determining
the map $x \mapsto Wx + b$ from `Fin m` inputs to `Fin n` outputs. -/
structure DenseLayer (m n : ℕ) where
  /-- The weight matrix. -/
  W : Matrix (Fin n) (Fin m) ℝ
  /-- The bias vector. -/
  b : Fin n → ℝ

/-- For [an input dimension](hyp:m), [an output dimension](hyp:n), [a dense affine layer](hyp:L), and [an input vector](hyp:x), [the layer evaluation](goal) is the output vector whose $j$th coordinate is the weighted sum of the input coordinates plus the $j$th bias. -/
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

/-- For [a vector dimension](hyp:n), [an activation-function bundle](hyp:σ), and [an input vector](hyp:x), [the coordinatewise activation](goal) is the vector obtained by applying the bundle's scalar activation to each coordinate of the input. -/
def Activation.applyVec {n : ℕ} (σ : Activation) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j => σ.act (x j)

end Causalean.ML

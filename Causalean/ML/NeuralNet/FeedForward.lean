/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.NeuralNet.Layer

/-! # Feedforward networks (uniform width)

A uniform-width feedforward network is a list of dense layers evaluated
left-to-right with an activation after each affine map.  Structural facts: the
evaluation respects layer concatenation (composition), and the network is
Lipschitz with constant the product of the per-layer Lipschitz constants.
Universal approximation and training dynamics are out of scope.
-/

namespace Causalean.ML

open BigOperators

/-- For [a nonnegative network width](hyp:n), [an activation function](hyp:σ), [a dense layer
with that finite input and output width](hyp:L), and [an input vector of that width](hyp:x), the
[one-layer network map](goal)
applies the layer's affine transformation and then applies the activation function to each
coordinate. -/
def layerMap {n : ℕ} (σ : Activation) (L : DenseLayer n n) (x : Fin n → ℝ) : Fin n → ℝ :=
  σ.applyVec (L.eval x)

/-- For [a nonnegative network width](hyp:n) and [an activation function](hyp:σ), the
[evaluation of a uniform-width feedforward network](goal) maps a finite ordered list of
equal-width dense layers and an input vector to its output vector. [For an empty list, the output
is the input itself](step:1); [for a list whose
first layer is followed by further layers, the output applies the first layer and then evaluates
the remaining layers](step:2). -/
def evalLayers {n : ℕ} (σ : Activation) : List (DenseLayer n n) → (Fin n → ℝ) → (Fin n → ℝ)
  | [], x => x
  | L :: Ls, x => evalLayers σ Ls (layerMap σ L x)

/-- **Structure — composition.** Evaluating concatenated layer lists is the
composition of the two evaluations. -/
theorem evalLayers_append {n : ℕ} (σ : Activation) (Ls Ms : List (DenseLayer n n))
    (x : Fin n → ℝ) :
    evalLayers σ (Ls ++ Ms) x = evalLayers σ Ms (evalLayers σ Ls x) := by
  induction Ls generalizing x with
  | nil => rfl
  | cons L Ls ih => simp [evalLayers, ih]

/-- **Structure — Lipschitz.** For a uniform-width feedforward network with activation `σ` and
layer list `Ls`, if [each layer's affine-then-activation map is Lipschitz with the constant
assigned to it by `k`](hyp:hk), then [the whole network evaluation is Lipschitz with constant
equal to the product of the per-layer constants](goal). -/
theorem evalLayers_lipschitz {n : ℕ} (σ : Activation) (Ls : List (DenseLayer n n))
    (k : DenseLayer n n → NNReal)
    (hk : ∀ L ∈ Ls, LipschitzWith (k L) (layerMap σ L)) :
    LipschitzWith (Ls.map k).prod (evalLayers σ Ls) := by
  induction Ls with
  | nil =>
      -- `simp` no longer unfolds `id`, so state the identity bound in the
      -- lambda form the goal uses.
      have hid : LipschitzWith (1 : NNReal) (fun x : Fin n → ℝ => x) :=
        LipschitzWith.id
      simpa [evalLayers] using hid
  | cons L Ls ih =>
      have hL : LipschitzWith (k L) (layerMap σ L) := hk L (by simp)
      have hLs : ∀ L' ∈ Ls, LipschitzWith (k L') (layerMap σ L') := by
        intro L' hL'
        exact hk L' (by simp [hL'])
      simpa [evalLayers, List.map_cons, List.prod_cons, mul_comm,
        Function.comp_def] using (ih hLs).comp hL

end Causalean.ML

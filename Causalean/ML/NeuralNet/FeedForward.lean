/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.ML.NeuralNet.Layer
public import Mathlib.Analysis.Matrix.Normed

/-! # Feedforward networks (uniform width)

A uniform-width feedforward network is a list of dense layers evaluated
left-to-right with an activation after each affine map.  Structural facts: the
evaluation respects layer concatenation (composition), and the network is
Lipschitz with constant the product of the activation Lipschitz constant and
the induced `L∞` operator norm of each layer's weight matrix.
Universal approximation and training dynamics are out of scope.
-/

@[expose] public section

namespace Causalean.ML

open BigOperators

/-- [A one-layer network map](goal) [applies an affine layer then activates](step:1). It combines
[a square dense layer and activation function](hyp:L,σ) at
[the chosen finite width](hyp:n) and acts on [an input vector](hyp:x). -/
def layerMap {n : ℕ} (σ : Activation) (L : DenseLayer n n) (x : Fin n → ℝ) : Fin n → ℝ :=
  σ.applyVec (L.eval x)

/-- [The weight Lipschitz constant](goal) extracts [the induced L∞ weight norm](step:1) from
[a square dense layer](hyp:L). -/
noncomputable def DenseLayer.weightLip {n : ℕ} (L : DenseLayer n n) : NNReal := by
  letI := Matrix.linftyOpNormedAddCommGroup (m := Fin n) (n := Fin n) (α := ℝ)
  exact ‖L.W‖₊

/-- [A dense layer's weight Lipschitz constant is the largest absolute row sum](goal), giving
an explicit induced L∞ operator norm for [the square weight matrix](hyp:L). -/
theorem DenseLayer.weightLip_eq {n : ℕ} (L : DenseLayer n n) :
    L.weightLip =
      (Finset.univ : Finset (Fin n)).sup fun i => ∑ j : Fin n, ‖L.W i j‖₊ := by
  unfold DenseLayer.weightLip
  letI := Matrix.linftyOpNormedAddCommGroup (m := Fin n) (n := Fin n) (α := ℝ)
  exact Matrix.linfty_opNNNorm_def L.W

/-- [Affine evaluation is Lipschitz with the induced L∞ norm of the weight matrix](goal) for
[every square dense layer](hyp:L); the bias cancels when comparing two inputs. -/
theorem DenseLayer.eval_lipschitz {n : ℕ} (L : DenseLayer n n) :
    LipschitzWith L.weightLip L.eval := by
  letI := Matrix.linftyOpNormedAddCommGroup (m := Fin n) (n := Fin n) (α := ℝ)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  have heval : L.eval x - L.eval y = Matrix.mulVec L.W (x - y) := by
    funext i
    simp [DenseLayer.eval, Matrix.mulVec_sub]
  rw [heval]
  simpa [DenseLayer.weightLip] using Matrix.linfty_opNorm_mulVec L.W (x - y)

/-- [Coordinatewise activation preserves the bundled scalar Lipschitz constant](goal) on
finite vectors for [the chosen activation function](hyp:σ). -/
theorem Activation.applyVec_lipschitz {n : ℕ} (σ : Activation) :
    LipschitzWith σ.lip (σ.applyVec : (Fin n → ℝ) → (Fin n → ℝ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (dist_pi_le_iff (mul_nonneg σ.lip.2 dist_nonneg)).2 fun i => by
    change dist (σ.act (x i)) (σ.act (y i)) ≤ _
    calc
      dist (σ.act (x i)) (σ.act (y i)) ≤ σ.lip * dist (x i) (y i) :=
        σ.isLipschitz.dist_le_mul (x i) (y i)
      _ ≤ σ.lip * dist x y :=
        mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) σ.lip.2

/-- [An affine-then-activation layer has the product Lipschitz bound](goal), combining
[the activation function](hyp:σ) with [a square dense layer](hyp:L). -/
theorem layerMap_lipschitz {n : ℕ} (σ : Activation) (L : DenseLayer n n) :
    LipschitzWith (σ.lip * L.weightLip) (layerMap σ L) := by
  change LipschitzWith (σ.lip * L.weightLip) (fun x => σ.applyVec (L.eval x))
  exact σ.applyVec_lipschitz.comp L.eval_lipschitz

/-- [Uniform-width feedforward evaluation](goal) composes affine-then-activation maps using
[the chosen activation function](hyp:σ) at [a fixed finite width](hyp:n).
[An empty network returns its input](step:1), while
[a nonempty network applies its head before its tail](step:2). -/
def evalLayers {n : ℕ} (σ : Activation) : List (DenseLayer n n) → (Fin n → ℝ) → (Fin n → ℝ)
  | [], x => x
  | L :: Ls, x => evalLayers σ Ls (layerMap σ L x)

/-- **Network concatenation evaluates by function composition.**
[Joined lists apply the first network and then the second](goal), for
[the chosen activation function](hyp:σ), [the two layer lists](hyp:Ls,Ms), and
[the input vector](hyp:x). -/
theorem evalLayers_append {n : ℕ} (σ : Activation) (Ls Ms : List (DenseLayer n n))
    (x : Fin n → ℝ) :
    evalLayers σ (Ls ++ Ms) x = evalLayers σ Ms (evalLayers σ Ls x) := by
  induction Ls generalizing x with
  | nil => rfl
  | cons L Ls ih => simp [evalLayers, ih]

/-- **Per-layer Lipschitz bounds multiply through a feedforward network.**
[The whole network has the product bound](goal) for [the activation function](hyp:σ) and
[ordered layer list](hyp:Ls), provided [each layer has an assigned constant](hyp:K) and
[every layer map obeys its assignment](hyp:hK). -/
theorem evalLayers_lipschitz_of_forall {n : ℕ} (σ : Activation)
    (Ls : List (DenseLayer n n)) (K : DenseLayer n n → NNReal)
    (hK : ∀ L ∈ Ls, LipschitzWith (K L) (layerMap σ L)) :
    LipschitzWith (Ls.map K).prod (evalLayers σ Ls) := by
  induction Ls with
  | nil =>
      have hid : LipschitzWith (1 : NNReal) (fun x : Fin n → ℝ => x) :=
        LipschitzWith.id
      simpa [evalLayers] using hid
  | cons L Ls ih =>
      have hhead : LipschitzWith (K L) (layerMap σ L) := hK L (by simp)
      have htail : ∀ M ∈ Ls, LipschitzWith (K M) (layerMap σ M) := by
        intro M hM
        exact hK M (by simp [hM])
      simpa [evalLayers, Function.comp_def, mul_comm] using (ih htail).comp hhead

/-- **A feedforward network is Lipschitz with its product activation--weight bound.**
[The full network evaluation has the product bound](goal) for
[the bundled activation function](hyp:σ) and [the ordered square layers](hyp:Ls). -/
theorem evalLayers_lipschitz {n : ℕ} (σ : Activation) (Ls : List (DenseLayer n n))
    : LipschitzWith (Ls.map (fun L => σ.lip * L.weightLip)).prod (evalLayers σ Ls) := by
  apply evalLayers_lipschitz_of_forall
  intro L hL
  exact layerMap_lipschitz σ L

end Causalean.ML

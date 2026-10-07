/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Square-completion bound on the `(0,0)` inverse entry under a Loewner sandwich

Linear-algebra bounds for the top-left inverse entry under positive-definite quadratic-form
sandwiches.

The interior local-polynomial leverage `(T⁻¹)₀₀` of the bandwidth-free kernel shape matrix `T`
must be controlled by the *density constants* `cDesign ≤ p ≤ CDesign` together with the pure
kernel-moment Gram matrix `G`. The clean route avoids Loewner inverse-monotonicity (absent from
Mathlib): it uses only the elementary **completing-the-square** identity

`(w − A⁻¹e)ᵀ A (w − A⁻¹e) ≥ 0  ⟺  2 eᵀw − wᵀ A w ≤ eᵀ A⁻¹ e`

valid for any positive definite `A` and vectors `e, w`. Evaluating it at the optimum `w = A⁻¹e`
turns the inequality into the variational identity `eᵀ A⁻¹ e = max_w (2 eᵀw − wᵀ A w)`, and a
Loewner sandwich `c·B ⪯ A` (as quadratic forms) then transports the maximum:

`(A⁻¹)₀₀ ≤ (B⁻¹)₀₀ / c`.

This file proves that bound (and the trivial companion `A₀₀ ≤ C·B₀₀` under `A ⪯ C·B`). It is the
pure-linear-algebra heart of the density-constant discharge of the local-polynomial leverage rate.
-/

public section

namespace Causalean.Stat.Nonparametric

open scoped BigOperators
open Matrix

variable {p : ℕ}

/-- **Completing-the-square inequality for a positive definite quadratic form.** For [a positive
definite matrix `A`](hyp:hA) and any vectors `e, w`, [the affine functional `2 eᵀw − wᵀ A w` is
bounded above by the inverse quadratic form `eᵀ A⁻¹ e`, with equality at `w = A⁻¹ e`](goal). This
is the elementary identity `eᵀ A⁻¹ e − (2 eᵀw − wᵀ A w) = (w − A⁻¹ e)ᵀ A (w − A⁻¹ e) ≥ 0`. -/
theorem two_dotProduct_sub_quadForm_le_inv {A : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ}
    (hA : A.PosDef) (e w : Fin (p + 1) → ℝ) :
    2 * (e ⬝ᵥ w) - w ⬝ᵥ (A *ᵥ w) ≤ e ⬝ᵥ (A⁻¹ *ᵥ e) := by
  let u : Fin (p + 1) → ℝ := (A⁻¹ *ᵥ e)
  have hdet : IsUnit A.det := Matrix.isUnit_iff_isUnit_det A |>.mp hA.isUnit
  have hAu : A *ᵥ u = e := by
    simpa [u] using congr_arg (fun M => M *ᵥ e) (Matrix.mul_nonsing_inv A hdet)
  have hsym : ∀ x y : Fin (p + 1), A x y = A y x := by
    intro x y
    have h := congr_fun₂ hA.isHermitian.eq y x
    simpa [conjTranspose] using h
  have hcross : u ⬝ᵥ (A *ᵥ w) = e ⬝ᵥ w := by
    rw [Matrix.dotProduct_mulVec]
    have hvec : u ᵥ* A = A *ᵥ u := by
      ext i
      rw [Matrix.vecMul, Matrix.mulVec]
      simp only [hsym]
      exact dotProduct_comm _ _
    rw [hvec, hAu]
  have hlast : u ⬝ᵥ e = e ⬝ᵥ (A⁻¹ *ᵥ e) := by
    dsimp [u]
    rw [dotProduct_comm]
  have h0 : 0 ≤ (w - u) ⬝ᵥ (A *ᵥ (w - u)) := by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg (w - u)
  have hexpand :
      (w - u) ⬝ᵥ (A *ᵥ (w - u))
        = w ⬝ᵥ (A *ᵥ w) - 2 * (e ⬝ᵥ w) + e ⬝ᵥ (A⁻¹ *ᵥ e) := by
    rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct]
    rw [hAu, hcross, hlast]
    rw [dotProduct_comm w e]
    ring
  rw [hexpand] at h0
  linarith

/-- The `(0,0)` entry of an inverse as an inverse quadratic form at the first basis vector:
`(A⁻¹)₀₀ = e₀ᵀ A⁻¹ e₀` with `e₀ = Pi.single 0 1`. -/
theorem inv00_eq_quadForm (A : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ) :
    A⁻¹ 0 0 = (Pi.single (0 : Fin (p + 1)) (1 : ℝ)) ⬝ᵥ (A⁻¹ *ᵥ Pi.single 0 1) := by
  simp [dotProduct, mulVec, Pi.single_apply]

/-- The `(0,0)` entry of a matrix as a quadratic form at the first basis vector:
`A₀₀ = e₀ᵀ A e₀` with `e₀ = Pi.single 0 1`. -/
theorem entry00_eq_quadForm (A : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ) :
    A 0 0 = (Pi.single (0 : Fin (p + 1)) (1 : ℝ)) ⬝ᵥ (A *ᵥ Pi.single 0 1) := by
  simp [dotProduct, mulVec, Pi.single_apply]

/-- **Loewner sandwich bound on a diagonal entry of the inverse.** If [`A`](hyp:hA) and
[`B`](hyp:hB) are positive definite real matrices and, for [a constant `c > 0`](hyp:hc), [`c
· wᵀ B w ≤ wᵀ A w` for every vector `w`](hyp:hsand), then for [every index `j`](hyp:j),
[`(A⁻¹)_{jj} ≤ (B⁻¹)_{jj} / c`](goal).

The proof evaluates the completing-the-square identity for `A` at `w⋆ = A⁻¹ e_j`, bounds
`w⋆ᵀ A w⋆ ≥ c · w⋆ᵀ B w⋆` by the sandwich, and applies completing-the-square for `B` at `c ·
w⋆`. -/
theorem inv_diag_le_of_quadForm_sandwich {A B : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ}
    (hA : A.PosDef) (hB : B.PosDef) {c : ℝ} (hc : 0 < c)
    (hsand : ∀ w : Fin (p + 1) → ℝ, c * (w ⬝ᵥ (B *ᵥ w)) ≤ w ⬝ᵥ (A *ᵥ w))
    (j : Fin (p + 1)) : A⁻¹ j j ≤ B⁻¹ j j / c := by
  let e : Fin (p + 1) → ℝ := Pi.single j 1
  let w : Fin (p + 1) → ℝ := A⁻¹ *ᵥ e
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hAw : A *ᵥ w = e := by
    simpa [w] using congr_arg (fun M => M *ᵥ e) (Matrix.mul_nonsing_inv A hdet)
  have hew : e ⬝ᵥ w = A⁻¹ j j := by
    simp [e, w]
  have hquadA : w ⬝ᵥ (A *ᵥ w) = e ⬝ᵥ w := by
    rw [hAw, dotProduct_comm]
  have hoptA : A⁻¹ j j = 2 * (e ⬝ᵥ w) - w ⬝ᵥ (A *ᵥ w) := by
    rw [hquadA, hew]
    ring
  have hAB : 2 * (e ⬝ᵥ w) - w ⬝ᵥ (A *ᵥ w)
      ≤ 2 * (e ⬝ᵥ w) - c * (w ⬝ᵥ (B *ᵥ w)) := by
    linarith [hsand w]
  have hBvar := two_dotProduct_sub_quadForm_le_inv hB e (c • w)
  have hscale :
      2 * (e ⬝ᵥ (c • w)) - (c • w) ⬝ᵥ (B *ᵥ (c • w))
        = c * (2 * (e ⬝ᵥ w) - c * (w ⬝ᵥ (B *ᵥ w))) := by
    simp [Matrix.mulVec_smul]
    ring
  have hBscaled : c * (2 * (e ⬝ᵥ w) - c * (w ⬝ᵥ (B *ᵥ w))) ≤ B⁻¹ j j := by
    rw [hscale] at hBvar
    simpa [e] using hBvar
  have hBdiv : 2 * (e ⬝ᵥ w) - c * (w ⬝ᵥ (B *ᵥ w)) ≤ B⁻¹ j j / c := by
    rw [le_div_iff₀ hc]
    linarith
  rw [hoptA]
  exact hAB.trans hBdiv

/-- **Loewner sandwich bound on the `(0,0)` inverse entry.** If `A` and `B` are positive definite
and `A` dominates `c·B` in the Loewner order on quadratic forms (`c·(wᵀ B w) ≤ wᵀ A w` for all `w`)
with `c > 0`, then the intercept leverage entries satisfy

`(A⁻¹)₀₀ ≤ (B⁻¹)₀₀ / c`.

This is the intercept case of the bound for an arbitrary diagonal entry of the inverse. -/
theorem inv00_le_of_quadForm_sandwich {A B : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ}
    (hA : A.PosDef) (hB : B.PosDef) {c : ℝ} (hc : 0 < c)
    (hsand : ∀ w : Fin (p + 1) → ℝ, c * (w ⬝ᵥ (B *ᵥ w)) ≤ w ⬝ᵥ (A *ᵥ w)) :
    A⁻¹ 0 0 ≤ B⁻¹ 0 0 / c :=
  inv_diag_le_of_quadForm_sandwich hA hB hc hsand 0

/-- **Loewner sandwich bound on the `(0,0)` entry.** If `A ⪯ C·B` in the Loewner order on
quadratic forms (`wᵀ A w ≤ C·wᵀ B w` for all `w`), then the top weight entries satisfy
`A₀₀ ≤ C·B₀₀`. (Just evaluate the quadratic forms at the first basis vector.) -/
theorem entry00_le_of_quadForm_sandwich {A B : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ} {C : ℝ}
    (hsand : ∀ w : Fin (p + 1) → ℝ, w ⬝ᵥ (A *ᵥ w) ≤ C * (w ⬝ᵥ (B *ᵥ w))) :
    A 0 0 ≤ C * B 0 0 := by
  rw [entry00_eq_quadForm A, entry00_eq_quadForm B]
  exact hsand (Pi.single (0 : Fin (p + 1)) (1 : ℝ))

end Causalean.Stat.Nonparametric

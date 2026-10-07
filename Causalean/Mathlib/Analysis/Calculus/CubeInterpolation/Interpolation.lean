module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Boundary
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Grid
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.GridResponse
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.JetPolynomial
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.PolynomialControl
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Taylor

/-!
# Fixed-cube Hölder interpolation

The main estimate bounds all lower coordinate partials from a response supremum and
the seminorm of the highest coordinate partials, uniformly over the response.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- [A finite dimension, derivative order, and positive Hölder exponent](hyp:d,m,s,hs) guarantee [a positive uniform constant controlling every coordinate partial in the open normalized cube from the response supremum and top-order Hölder seminorm](goal). -/
theorem interior_fixed_cube_interpolation (d m : ℕ) (s : ℝ)
    (hs : 0 < s) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (M L : ℝ),
        0 ≤ M → 0 ≤ L → ContDiffOn ℝ m u (cube d) →
        (∀ x ∈ cube d, |u x| ≤ M) → TopHolder d m s L u →
        ∀ j ≤ m, ∀ f : Fin j → Fin d,
          ∀ x ∈ openCube d, |coordPartial j u f x| ≤ K * (M + L) := by
  obtain ⟨C₁, hC₁, hgrid⟩ := taylor_polynomial_grid_bound d m s hs
  obtain ⟨C₂, hC₂, hpoly⟩ := tensor_polynomial_deriv_bound d m
  refine ⟨C₂ * C₁, mul_pos hC₂ hC₁, ?_⟩
  intro u M L hM hL hu hbound hholder j hj f x hx
  obtain ⟨p, hdegree, hp⟩ := taylor_expression_polynomial d m u x
  have ho : IsOpen (openCube d) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hsub : openCube d ⊆ cube d := by
    intro z hz i
    exact ⟨le_of_lt (hz i (Set.mem_univ i)).1,
      le_of_lt (hz i (Set.mem_univ i)).2⟩
  have hux : ContDiffAt ℝ m u x :=
    (hu.mono hsub).contDiffAt (ho.mem_nhds hx)
  have hB : 0 ≤ C₁ * (M + L) :=
    mul_nonneg (le_of_lt hC₁) (add_nonneg hM hL)
  have hpbound := hpoly p (C₁ * (M + L)) hB hdegree
    (hgrid u M L hM hL hu hbound hholder x hx p hp) j hj f x (hsub hx)
  rw [← taylor_polynomial_jet_match hux hp j hj f]
  calc
    |coordPartial j (fun z => MvPolynomial.eval z p) f x| ≤
        C₂ * (C₁ * (M + L)) := hpbound
    _ = (C₂ * C₁) * (M + L) := by ring

/-- [A finite dimension, derivative order, and positive Hölder exponent](hyp:d,m,s,hs) guarantee [a positive uniform constant controlling every coordinate partial on the closed normalized cube from the response supremum and top-order Hölder seminorm](goal). -/
theorem fixed_cube_interpolation (d m : ℕ) (s : ℝ)
    (hs : 0 < s) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (M L : ℝ),
        0 ≤ M → 0 ≤ L → ContDiffOn ℝ m u (cube d) →
        (∀ x ∈ cube d, |u x| ≤ M) → TopHolder d m s L u →
        DerivBound d m (K * (M + L)) u := by
  obtain ⟨K, hK, hinterior⟩ := interior_fixed_cube_interpolation d m s hs
  refine ⟨K, hK, ?_⟩
  intro u M L hM hL hu hbound hholder
  apply interior_coordPartial_bound_extends
    (mul_nonneg (le_of_lt hK) (add_nonneg hM hL)) hu
  exact hinterior u M L hM hL hu hbound hholder

/-- In [dimension d](hyp:d), for [a smoothness index β](hyp:β) [greater
than one](hyp:hβ), write m for the largest integer strictly below β and s = β − m. Then [there is a
positive constant K, depending only on d and β, such that for all nonnegative M and L: every
function that is m times continuously differentiable on the closed normalized cube, is bounded
there by M in absolute value, and satisfies the top-order Hölder condition of order m with exponent
s and constant L, lies in the fixed-cube Hölder ball of order m, exponent s, and radius K times
(M + L); in particular all its coordinate partials of order at most m are bounded by K times
(M + L) on the cube](goal).

Coordinate partials in both the hypothesis and the conclusion are taken in the whole space. -/
theorem fixed_cube_holder_completion (d : ℕ)
    (β : ℝ) (hβ : 1 < β) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (M L : ℝ),
        0 ≤ M → 0 ≤ L →
        ContDiffOn ℝ (⌈β⌉₊ - 1) u (cube d) →
        (∀ x ∈ cube d, |u x| ≤ M) →
        TopHolder d (⌈β⌉₊ - 1) (β - ((⌈β⌉₊ - 1 : ℕ) : ℝ)) L u →
        HolderBall d (⌈β⌉₊ - 1)
          (β - ((⌈β⌉₊ - 1 : ℕ) : ℝ)) (K * (M + L)) u := by
  have hceil_one : 1 ≤ ⌈β⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
  have hcast : ((⌈β⌉₊ - 1 : ℕ) : ℝ) = (⌈β⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub hceil_one, Nat.cast_one]
  have hs : 0 < β - ((⌈β⌉₊ - 1 : ℕ) : ℝ) := by
    rw [hcast]
    linarith [Nat.ceil_lt_add_one (by linarith : 0 ≤ β)]
  have hs1 : β - ((⌈β⌉₊ - 1 : ℕ) : ℝ) ≤ 1 := by
    rw [hcast]
    linarith [Nat.le_ceil β]
  obtain ⟨K, hK, hinterp⟩ :=
    fixed_cube_interpolation d (⌈β⌉₊ - 1)
      (β - ((⌈β⌉₊ - 1 : ℕ) : ℝ)) hs
  refine ⟨K + 1, by linarith, ?_⟩
  intro u M L hM hL hu hbound hholder
  have hsum : 0 ≤ M + L := add_nonneg hM hL
  have hKle : K ≤ K + 1 := by linarith
  have hLradius : L ≤ (K + 1) * (M + L) := by
    calc
      L ≤ M + L := by linarith
      _ = 1 * (M + L) := by ring
      _ ≤ (K + 1) * (M + L) :=
        mul_le_mul_of_nonneg_right (by linarith : 1 ≤ K + 1) hsum
  refine ⟨hu, ?_, ?_⟩
  · intro j hj f x hx
    exact (hinterp u M L hM hL hu hbound hholder j hj f x hx).trans
      (mul_le_mul_of_nonneg_right hKle hsum)
  · intro f x hx y hy
    exact (hholder f x hx y hy).trans
      (mul_le_mul_of_nonneg_right hLradius (by positivity))

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.AffineGeometry
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Interpolation
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
# Affine transport between fixed cubes

The map `x ↦ 2x-1` sends `[0,1]^d` to `[-1,1]^d`. Coordinate derivatives of order
`j` gain `2^j`, and the top Hölder seminorm gains `2^(m+s)`.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- [A finite dimension, derivative order, response, coordinate-direction sequence, and evaluation point](hyp:d,j,u,f,x) imply [that affine transport from the unit cube multiplies the coordinate partial by two to that order](goal). -/
theorem affine_coordPartial {d j : ℕ} (u : (Fin d → ℝ) → ℝ)
    (f : Fin j → Fin d) (x : Fin d → ℝ) :
    coordPartial j (fun z => u (cubeAffine z)) f x =
      (2 : ℝ) ^ j * coordPartial j u f (cubeAffine x) := by
  let a : Fin d → ℝ := fun _ => 1
  let v : (Fin d → ℝ) → ℝ := fun y => u (y - a)
  let e : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
    ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Fin d → ℝ)
      (Units.mk0 (2 : ℝ) (by norm_num))
  have he (z : Fin d → ℝ) : e z = (2 : ℝ) • z := by
    ext i
    simp [e]
  have he_map : (e : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) =
      (2 : ℝ) • ContinuousLinearMap.id ℝ (Fin d → ℝ) := by
    apply ContinuousLinearMap.ext
    intro z
    simpa using he z
  have hscale := e.iteratedFDerivWithin_comp_right v uniqueDiffOn_univ
    (Set.mem_univ (e x)) j
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at hscale
  have hscale' : iteratedFDeriv ℝ j (fun z => v ((2 : ℝ) • z)) x =
      (iteratedFDeriv ℝ j v ((2 : ℝ) • x)).compContinuousLinearMap
        (fun _ => (2 : ℝ) • ContinuousLinearMap.id ℝ (Fin d → ℝ)) := by
    simpa only [he_map, he, Function.comp_def] using hscale
  have hc (z : Fin d → ℝ) : cubeAffine z = (2 : ℝ) • z - a := by
    ext i
    simp [cubeAffine, a, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have htrans : iteratedFDeriv ℝ j v ((2 : ℝ) • x) =
      iteratedFDeriv ℝ j u ((2 : ℝ) • x - a) := by
    exact iteratedFDeriv_comp_sub j a ((2 : ℝ) • x)
  unfold coordPartial
  rw [show (fun z => u (cubeAffine z)) = (fun z => v ((2 : ℝ) • z)) by
    funext z; simp [v, hc]]
  rw [hscale', htrans]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    smul_apply, ContinuousLinearMap.id_apply]
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp [hc, a]

/-- [A finite dimension, derivative order, Hölder exponent, seminorm bound, response, and top-order modulus](hyp:d,m,s,L,u,hL) imply [the affine-scaled top-order Hölder modulus on the unit cube](goal). -/
theorem affine_topHolder {d m : ℕ} {s L : ℝ} (u : (Fin d → ℝ) → ℝ)
    (hL : TopHolder d m s L u) :
    ∀ f : Fin m → Fin d, ∀ x ∈ unitCube d, ∀ y ∈ unitCube d,
      |coordPartial m (fun z => u (cubeAffine z)) f x -
        coordPartial m (fun z => u (cubeAffine z)) f y| ≤
        ((2 : ℝ) ^ ((m : ℝ) + s) * L) * ‖x - y‖ ^ s := by
  intro f x hx y hy
  rw [affine_coordPartial, affine_coordPartial]
  have h := hL f (cubeAffine x) (cubeAffine_mem_cube hx)
    (cubeAffine y) (cubeAffine_mem_cube hy)
  have hpow : (2 : ℝ) ^ m * (2 * ‖x - y‖) ^ s =
      (2 : ℝ) ^ ((m : ℝ) + s) * ‖x - y‖ ^ s := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg _),
      ← Real.rpow_natCast, ← mul_assoc,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  calc
    |(2 : ℝ) ^ m * coordPartial m u f (cubeAffine x) -
        (2 : ℝ) ^ m * coordPartial m u f (cubeAffine y)| =
        (2 : ℝ) ^ m * |coordPartial m u f (cubeAffine x) -
          coordPartial m u f (cubeAffine y)| := by
          rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ (2 : ℝ) ^ m * (L * ‖cubeAffine x - cubeAffine y‖ ^ s) := by
      exact mul_le_mul_of_nonneg_left h (by positivity)
    _ = ((2 : ℝ) ^ ((m : ℝ) + s) * L) * ‖x - y‖ ^ s := by
      rw [cubeAffine_norm_sub]
      calc
        (2 : ℝ) ^ m * (L * (2 * ‖x - y‖) ^ s) =
            ((2 : ℝ) ^ m * (2 * ‖x - y‖) ^ s) * L := by ring
        _ = _ := by rw [hpow]; ring

/-- If [a function u of d variables](hyp:d,u) lies in [the fixed-cube Hölder ball of derivative
order m, exponent s, and radius R on the normalized cube](hyp:m,s,R,hu), then [its pullback
z ↦ u(2z − 1) to the unit cube satisfies three things: it is m times continuously
differentiable on the unit cube; each of
its coordinate partial derivatives of order j at most m is at most 2^j times R in absolute value
on the unit cube; and each of its order-m coordinate partials changes between any two points of
the unit cube by at most 2^(m + s) times R times their distance to the power s](goal).

Coordinate partials are taken in the whole space, as in the fixed-cube Hölder ball. -/
theorem affine_holderBall {d m : ℕ} {s R : ℝ} (u : (Fin d → ℝ) → ℝ)
    (hu : HolderBall d m s R u) :
    ContDiffOn ℝ m (fun z => u (cubeAffine z)) (unitCube d) ∧
    (∀ j ≤ m, ∀ f : Fin j → Fin d, ∀ x ∈ unitCube d,
      |coordPartial j (fun z => u (cubeAffine z)) f x| ≤ (2 : ℝ) ^ j * R) ∧
    (∀ f : Fin m → Fin d, ∀ x ∈ unitCube d, ∀ y ∈ unitCube d,
      |coordPartial m (fun z => u (cubeAffine z)) f x -
        coordPartial m (fun z => u (cubeAffine z)) f y| ≤
          ((2 : ℝ) ^ ((m : ℝ) + s) * R) * ‖x - y‖ ^ s) := by
  refine ⟨?_, ?_, affine_topHolder u hu.modulus⟩
  · have hmap : Set.MapsTo (cubeAffine : (Fin d → ℝ) → (Fin d → ℝ))
        (unitCube d) (cube d) := fun _ hx => cubeAffine_mem_cube hx
    simpa only [Function.comp_def] using
      hu.regularity.comp cubeAffine_contDiff.contDiffOn hmap
  · intro j hj f x hx
    rw [affine_coordPartial, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ j)]
    exact mul_le_mul_of_nonneg_left
      (hu.derivBound j hj f (cubeAffine x) (cubeAffine_mem_cube hx))
      (by positivity)

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

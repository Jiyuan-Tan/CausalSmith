module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Basic

/-!
# Affine transport of Hölder balls between the cubes [0,1]^d and [−1,1]^d

Composing with the coordinatewise affine map x ↦ 2x − 1 or its inverse x ↦ (x + 1)/2 carries the
intrinsic Hölder ball of derivative order m and exponent s ∈ (0, 1] on one cube into the Hölder
ball on the other, with the radius multiplied by a constant depending only on the dimension d,
on m and on s. Results proved on the normalized cube [−1,1]^d therefore transfer to the unit cube
[0,1]^d and back.

## Main definitions

* `cubeAffineInv` — the map x ↦ (x + 1)/2, coordinate by coordinate, from [−1,1]^d onto [0,1]^d.

## Main results

* `cube_holder_affine_transport` — u in the radius-R Hölder ball on [−1,1]^d implies
  x ↦ u(2x − 1) in the radius-C·R Hölder ball on [0,1]^d.
* `unit_holder_affine_transport` — the converse direction, for x ↦ u((x + 1)/2).
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation
open scoped Pointwise

/-- [The inverse coordinatewise affine map](goal) sends [a point x](hyp:x) to
the point whose i-th coordinate is (x_i + 1)/2; it carries the normalized cube
`[-1,1]^d` onto the unit cube `[0,1]^d`. -/
noncomputable def cubeAffineInv {d : ℕ} (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => (x i + 1) / 2

private theorem coordJetOn_comp_affine {d j : ℕ}
    {S T : Set (Fin d → ℝ)} (u : (Fin d → ℝ) → ℝ)
    (f : Fin j → Fin d) (x : Fin d → ℝ)
    (e : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) (a : Fin d → ℝ) (q : ℝ)
    (he : ∀ z, e z = q • z) (hT : a +ᵥ T = e ⁻¹' S)
    (hS : UniqueDiffOn ℝ S) (hx : e (x + a) ∈ S) :
    coordJetOn T j (fun z => u (e (z + a))) f x =
      q ^ j * coordJetOn S j u f (e (x + a)) := by
  unfold coordJetOn
  have htrans := iteratedFDerivWithin_comp_add_right
    (𝕜 := ℝ) (s := T) (f := fun z => u (e z)) j a x
  have hscale := e.iteratedFDerivWithin_comp_right u hS hx j
  rw [hT] at htrans
  rw [htrans]
  change iteratedFDerivWithin ℝ j (u ∘ (e : (Fin d → ℝ) → (Fin d → ℝ)))
    (e ⁻¹' S) (x + a) (fun k => Pi.single (f k) 1) = _
  rw [hscale]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe]
  have hb (k : Fin j) : e (Pi.single (f k) (1 : ℝ)) =
      q • Pi.single (f k) (1 : ℝ) := he _
  simp only [hb]
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp [Finset.prod_const, smul_eq_mul]

private theorem uniqueDiffOn_unitCube (d : ℕ) :
    UniqueDiffOn ℝ (unitCube d) := by
  unfold unitCube
  exact UniqueDiffOn.pi (fun _ _ => uniqueDiffOn_Icc (by norm_num))

private theorem cubeAffineInv_mem_unitCube {d : ℕ} {x : Fin d → ℝ}
    (hx : x ∈ cube d) : cubeAffineInv x ∈ unitCube d := by
  apply Set.mem_univ_pi.mpr
  intro i
  have hi := hx i
  constructor <;> dsimp [cubeAffineInv] <;> linarith [hi.1, hi.2]

private theorem cubeAffineInv_preimage_unitCube (d : ℕ) :
    cubeAffineInv ⁻¹' unitCube d = cube d := by
  ext x
  constructor
  · intro hx i
    have hi := (Set.mem_univ_pi.mp hx) i
    change 0 ≤ (x i + 1) / 2 ∧ (x i + 1) / 2 ≤ 1 at hi
    constructor <;> linarith [hi.1, hi.2]
  · exact cubeAffineInv_mem_unitCube

private theorem coordJetOn_cubeAffine {d j : ℕ} (u : (Fin d → ℝ) → ℝ)
    (f : Fin j → Fin d) (x : Fin d → ℝ) (hx : x ∈ unitCube d) :
    coordJetOn (unitCube d) j (fun z => u (cubeAffine z)) f x =
      (2 : ℝ) ^ j * coordJetOn (cube d) j u f (cubeAffine x) := by
  let e : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
    ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Fin d → ℝ)
      (Units.mk0 (2 : ℝ) (by norm_num))
  let a : Fin d → ℝ := fun _ => -(1 / 2 : ℝ)
  have he (z : Fin d → ℝ) : e z = (2 : ℝ) • z := by
    ext i
    simp [e]
  have hT : a +ᵥ unitCube d = e ⁻¹' cube d := by
    ext z
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, ← cubeAffine_preimage_cube d]
    change cubeAffine (-a + z) ∈ cube d ↔ e z ∈ cube d
    rw [show cubeAffine (-a + z) = e z by
      ext i
      simp [cubeAffine, a, he, Pi.add_apply, Pi.neg_apply, smul_eq_mul]
      ring]
  have hfa (z : Fin d → ℝ) : e (z + a) = cubeAffine z := by
    ext i
    simp [cubeAffine, a, he, Pi.add_apply, smul_eq_mul]
    ring
  simpa only [hfa] using
    coordJetOn_comp_affine u f x e a 2 he hT
      (by
        have hcube : cube d = Set.univ.pi (fun _ : Fin d => Set.Icc (-1 : ℝ) 1) := by
          ext z
          simp [cube, Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube,
            Pi.le_def, forall_and]
        rw [hcube]
        exact UniqueDiffOn.pi (fun _ _ => uniqueDiffOn_Icc (by norm_num)))
      (by rw [hfa]; exact cubeAffine_mem_cube hx)

private theorem coordJetOn_cubeAffineInv {d j : ℕ} (u : (Fin d → ℝ) → ℝ)
    (f : Fin j → Fin d) (x : Fin d → ℝ) (hx : x ∈ cube d) :
    coordJetOn (cube d) j (fun z => u (cubeAffineInv z)) f x =
      (1 / 2 : ℝ) ^ j * coordJetOn (unitCube d) j u f (cubeAffineInv x) := by
  let e : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
    ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Fin d → ℝ)
      (Units.mk0 (1 / 2 : ℝ) (by norm_num))
  let a : Fin d → ℝ := fun _ => 1
  have he (z : Fin d → ℝ) : e z = (1 / 2 : ℝ) • z := by
    ext i
    simp [e]
  have hT : a +ᵥ cube d = e ⁻¹' unitCube d := by
    ext z
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, ← cubeAffineInv_preimage_unitCube d]
    change cubeAffineInv (-a + z) ∈ unitCube d ↔ e z ∈ unitCube d
    rw [show cubeAffineInv (-a + z) = e z by
      ext i
      simp [cubeAffineInv, a, he, Pi.add_apply, Pi.neg_apply, smul_eq_mul]
      ring]
  have hfa (z : Fin d → ℝ) : e (z + a) = cubeAffineInv z := by
    ext i
    simp [cubeAffineInv, a, he, Pi.add_apply, smul_eq_mul]
    ring
  simpa only [hfa] using
    coordJetOn_comp_affine u f x e a (1 / 2) he hT
      (uniqueDiffOn_unitCube d)
      (by rw [hfa]; exact cubeAffineInv_mem_unitCube hx)

private theorem cubeAffineInv_norm_sub {d : ℕ} (x y : Fin d → ℝ) :
    ‖cubeAffineInv x - cubeAffineInv y‖ = (1 / 2 : ℝ) * ‖x - y‖ := by
  have h : cubeAffineInv x - cubeAffineInv y = (1 / 2 : ℝ) • (x - y) := by
    ext i
    simp [cubeAffineInv, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h, norm_smul]
  norm_num

/-- In [dimension d](hyp:d), for [derivative order m](hyp:m) and
[a Hölder exponent s](hyp:s) with [s ≤ 1](hyp:hs1),
[there is a positive constant C such that whenever a response u lies in the
intrinsic Hölder ball of order m, exponent s and radius R ≥ 0 on the
normalized cube `[-1,1]^d`, its pullback x ↦ u(2x − 1) along the coordinatewise
affine map lies in the intrinsic Hölder ball of radius C·R on the unit cube
`[0,1]^d`](goal). The constant depends only on d, m and s. -/
theorem cube_holder_affine_transport (d m : ℕ) (s : ℝ)
    (hs1 : s ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (R : ℝ), 0 ≤ R →
        CubeHolderBall d m s R u →
        HolderBallOn (unitCube d) m s (C * R)
          (fun x => u (cubeAffine x)) := by
  refine ⟨(2 : ℝ) ^ (m + 1), by positivity, ?_⟩
  intro u R hR hu
  have hreg : ContDiffOn ℝ m (fun x => u (cubeAffine x)) (unitCube d) := by
    exact hu.regularity.comp cubeAffine_contDiff.contDiffOn
      (fun _ hx => cubeAffine_mem_cube hx)
  refine ⟨hreg, ?_, ?_⟩
  · intro j hj f x hx
    rw [coordJetOn_cubeAffine u f x hx, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ j)]
    calc
      (2 : ℝ) ^ j * |coordJetOn (cube d) j u f (cubeAffine x)| ≤
          (2 : ℝ) ^ j * R :=
        mul_le_mul_of_nonneg_left
          (hu.derivBound j hj f (cubeAffine x) (cubeAffine_mem_cube hx))
          (by positivity)
      _ ≤ (2 : ℝ) ^ (m + 1) * R :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_succ_of_le hj)) hR
  · intro f x hx y hy
    rw [coordJetOn_cubeAffine u f x hx, coordJetOn_cubeAffine u f y hy]
    have hmod := hu.modulus f (cubeAffine x) (cubeAffine_mem_cube hx)
      (cubeAffine y) (cubeAffine_mem_cube hy)
    have hpow : (2 : ℝ) ^ s ≤ 2 :=
      Real.rpow_le_self_of_one_le (by norm_num) hs1
    have hn : 0 ≤ ‖x - y‖ ^ s := Real.rpow_nonneg (norm_nonneg _) _
    calc
      |(2 : ℝ) ^ m * coordJetOn (cube d) m u f (cubeAffine x) -
          (2 : ℝ) ^ m * coordJetOn (cube d) m u f (cubeAffine y)| =
          (2 : ℝ) ^ m *
            |coordJetOn (cube d) m u f (cubeAffine x) -
              coordJetOn (cube d) m u f (cubeAffine y)| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ (2 : ℝ) ^ m * (R * ‖cubeAffine x - cubeAffine y‖ ^ s) :=
        mul_le_mul_of_nonneg_left hmod (by positivity)
      _ = ((2 : ℝ) ^ m * (2 : ℝ) ^ s * R) * ‖x - y‖ ^ s := by
        rw [cubeAffine_norm_sub,
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg _)]
        ring
      _ ≤ ((2 : ℝ) ^ m * 2 * R) * ‖x - y‖ ^ s := by
        gcongr
      _ = (2 : ℝ) ^ (m + 1) * R * ‖x - y‖ ^ s := by
        rw [pow_succ]

/-- In [dimension d](hyp:d), for [derivative order m](hyp:m) and
[a Hölder exponent s](hyp:s) with [0 < s](hyp:hs),
[there is a positive constant C such that whenever a response u lies in the
intrinsic Hölder ball of order m, exponent s and radius R ≥ 0 on the unit cube
`[0,1]^d`, its pullback x ↦ u((x + 1)/2) along the inverse coordinatewise affine
map lies in the intrinsic Hölder ball of radius C·R on the normalized cube
`[-1,1]^d`](goal). The constant depends only on d, m and s. -/
theorem unit_holder_affine_transport (d m : ℕ) (s : ℝ)
    (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (R : ℝ), 0 ≤ R →
        HolderBallOn (unitCube d) m s R u →
        CubeHolderBall d m s (C * R)
          (fun x => u (cubeAffineInv x)) := by
  refine ⟨1, by norm_num, ?_⟩
  intro u R hR hu
  have hinv : ContDiff ℝ m (cubeAffineInv : (Fin d → ℝ) → (Fin d → ℝ)) := by
    unfold cubeAffineInv
    fun_prop
  have hreg : ContDiffOn ℝ m (fun x => u (cubeAffineInv x)) (cube d) := by
    exact hu.regularity.comp hinv.contDiffOn
      (fun _ hx => cubeAffineInv_mem_unitCube hx)
  refine ⟨hreg, ?_, ?_⟩
  · intro j hj f x hx
    rw [coordJetOn_cubeAffineInv u f x hx, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ (1 / 2 : ℝ) ^ j)]
    calc
      (1 / 2 : ℝ) ^ j * |coordJetOn (unitCube d) j u f (cubeAffineInv x)| ≤
          (1 / 2 : ℝ) ^ j * R :=
        mul_le_mul_of_nonneg_left
          (hu.derivBound j hj f (cubeAffineInv x) (cubeAffineInv_mem_unitCube hx))
          (by positivity)
      _ ≤ 1 * R :=
        mul_le_mul_of_nonneg_right
          (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)) hR
  · intro f x hx y hy
    rw [coordJetOn_cubeAffineInv u f x hx, coordJetOn_cubeAffineInv u f y hy]
    have hmod := hu.modulus f (cubeAffineInv x) (cubeAffineInv_mem_unitCube hx)
      (cubeAffineInv y) (cubeAffineInv_mem_unitCube hy)
    have hnorm : ‖cubeAffineInv x - cubeAffineInv y‖ ≤ ‖x - y‖ := by
      rw [cubeAffineInv_norm_sub]
      nlinarith [norm_nonneg (x - y)]
    have hpow : ‖cubeAffineInv x - cubeAffineInv y‖ ^ s ≤ ‖x - y‖ ^ s :=
      Real.rpow_le_rpow (norm_nonneg _) hnorm hs.le
    calc
      |(1 / 2 : ℝ) ^ m * coordJetOn (unitCube d) m u f (cubeAffineInv x) -
          (1 / 2 : ℝ) ^ m * coordJetOn (unitCube d) m u f (cubeAffineInv y)| =
          (1 / 2 : ℝ) ^ m *
            |coordJetOn (unitCube d) m u f (cubeAffineInv x) -
              coordJetOn (unitCube d) m u f (cubeAffineInv y)| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ (1 / 2 : ℝ) ^ m * (R * ‖cubeAffineInv x - cubeAffineInv y‖ ^ s) :=
        mul_le_mul_of_nonneg_left hmod (by positivity)
      _ ≤ (1 / 2 : ℝ) ^ m * (R * ‖x - y‖ ^ s) := by
        gcongr
      _ ≤ 1 * (R * ‖x - y‖ ^ s) := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
          (mul_nonneg hR (Real.rpow_nonneg (norm_nonneg _) _))
      _ = 1 * R * ‖x - y‖ ^ s := by ring

end Causalean.Mathlib.Analysis.Calculus.CubeExtension

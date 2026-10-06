module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.RectangularFaceGeometry
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionCoefficients
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionCollarControl

/-!
# Controlled reflection across a face of a rectangular box

Affine transport carries the normalized one-face reflection to any
nondegenerate coordinate box. The first step extends across a lower face;
upper faces and repeated reflection can be built from this result.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- If [0 < s](hyp:hs) and [s ≤ 1](hyp:hs1) and [the box with corners lo, hi has
positive side lengths](hyp:hbox), then for [derivative order m](hyp:m) and
[coordinate i](hyp:i) [there is a positive constant C such that every response u
in the intrinsic Hölder ball of order m, exponent s and radius L ≥ 0 on the box
agrees on the box with a response in the intrinsic Hölder ball of radius C·L on
the box's left collar in coordinate i](goal). The constant depends only on the
box, m, s and i. -/
theorem exists_rectLeftFaceReflection_holder_constant {d : ℕ}
    (lo hi : Fin d → ℝ) (m : ℕ) (s : ℝ)
    (hs : 0 < s) (hs1 : s ≤ 1)
    (hbox : ∀ j, lo j < hi j) (i : Fin d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (L : ℝ), 0 ≤ L →
        HolderBallOn (rectBox lo hi) m s L u →
        ∃ v : (Fin d → ℝ) → ℝ,
          Set.EqOn v u (rectBox lo hi) ∧
          HolderBallOn (rectLeftCollar lo hi m i) m s (C * L) v := by
  /- Normalize the source box to `cube d` by `rectAffine`. Use
  `exists_rectAffine_holder_constant` to control the normalized response,
  `exists_reflection_coefficients` and
  `exists_leftFaceReflection_collar_holder_constant` for the reflected
  response, then transport back. Identify the affine preimage of
  `leftCubeCollar` with `rectLeftCollar`; this uses the factor 1/2 in the
  collar width. Agreement follows from `leftFaceReflection_eqOn_cube`.
  The constants depend on the fixed box and remain uniform in `u,L`. -/
  let lower : Fin d → ℝ := fun j =>
    if j = i then -1 - (1 : ℝ) / ((m : ℝ) + 1) else -1
  have hcube : rectBox (fun _ : Fin d => -1) (fun _ => 1) = cube d := by
    rfl
  have hcollar : rectBox lower (fun _ => 1) = leftCubeCollar d m i := by
    ext x
    simp only [rectBox, leftCubeCollar, Set.mem_ofPred_eq]
    constructor <;> intro hx j
    · specialize hx j
      by_cases hj : j = i <;> simp only [lower, hj, ↓reduceIte] at * <;> exact hx
    · specialize hx j
      by_cases hj : j = i <;> simp only [lower, hj, ↓reduceIte] at * <;> exact hx
  have hsource : ∀ j, rectLeftLower lo hi m i j < hi j := by
    intro j
    by_cases hj : j = i
    · subst j
      have hp : 0 < hi i - lo i := sub_pos.mpr (hbox i)
      have hw : 0 < (hi i - lo i) / (2 * ((m : ℝ) + 1)) := by positivity
      simp only [rectLeftLower, ↓reduceIte]
      linarith
    · simpa [rectLeftLower, hj] using hbox j
  have htarget : ∀ j, lower j < (1 : ℝ) := by
    intro j
    by_cases hj : j = i
    · simp only [lower, hj, ↓reduceIte]
      have hp : 0 < (1 : ℝ) / ((m : ℝ) + 1) := by positivity
      linarith
    · simp [lower, hj]
  obtain ⟨Cn, hCn, hn⟩ :=
    exists_rectAffine_holder_constant
      (fun _ : Fin d => -1) (fun _ => 1) lo hi m s
      (by intro j; norm_num) hbox
  obtain ⟨a, ha⟩ := exists_reflection_coefficients m
  obtain ⟨Cr, hCr, hr⟩ :=
    exists_leftFaceReflection_collar_holder_constant d m s hs hs1 i a ha
  obtain ⟨Cb, hCb, hb⟩ :=
    exists_rectAffine_holder_constant
      (rectLeftLower lo hi m i) hi lower (fun _ => 1) m s hsource htarget
  refine ⟨Cb * (Cr * Cn), mul_pos hCb (mul_pos hCr hCn), ?_⟩
  intro u L hL hu
  let un : (Fin d → ℝ) → ℝ :=
    fun x => u (rectAffine (fun _ => -1) (fun _ => 1) lo hi x)
  let reflected := leftFaceReflection d m i a un
  let v : (Fin d → ℝ) → ℝ :=
    fun x => reflected (rectAffine (rectLeftLower lo hi m i) hi lower (fun _ => 1) x)
  have hnormalized : CubeHolderBall d m s (Cn * L) un := by
    change HolderBallOn (cube d) m s (Cn * L) un
    rw [← hcube]
    exact hn u L hL hu
  have hreflected : HolderBallOn (leftCubeCollar d m i) m s
      (Cr * (Cn * L)) reflected := hr un (Cn * L)
        (mul_nonneg hCn.le hL) hnormalized
  refine ⟨v, ?_, ?_⟩
  · intro x hx
    have hxcube : rectAffine lo hi (fun _ => -1) (fun _ => 1) x ∈ cube d := by
      rw [← hcube]
      exact (Set.ext_iff.mp
        (rectAffine_preimage_rectBox lo hi (fun _ => -1) (fun _ => 1)
          hbox (by intro j; norm_num)) x).2 hx
    have heq := leftFaceReflection_eqOn_cube d m i a un hxcube
    change reflected (rectAffine (rectLeftLower lo hi m i) hi lower
      (fun _ => 1) x) = u x
    rw [show rectAffine (rectLeftLower lo hi m i) hi lower
        (fun _ => 1) x = rectAffine lo hi (fun _ => -1) (fun _ => 1) x from
      rectAffine_leftCollar_eq_normalize lo hi m i hbox x]
    change leftFaceReflection d m i a un
      (rectAffine lo hi (fun _ => -1) (fun _ => 1) x) = u x
    rw [heq]
    change u (rectAffine (fun _ => -1) (fun _ => 1) lo hi
      (rectAffine lo hi (fun _ => -1) (fun _ => 1) x)) = u x
    congr 1
    funext j
    have hw : hi j - lo j ≠ 0 := ne_of_gt (sub_pos.mpr (hbox j))
    simp only [rectAffine]
    field_simp [hw]
    ring
  · change HolderBallOn (rectBox (rectLeftLower lo hi m i) hi) m s
      (Cb * (Cr * Cn) * L) v
    have htransport := hb reflected (Cr * (Cn * L))
      (mul_nonneg hCr.le (mul_nonneg hCn.le hL)) (by
        rw [hcollar]
        exact hreflected)
    simpa only [v, mul_assoc] using htransport

end Causalean.Mathlib.Analysis.Calculus.CubeExtension

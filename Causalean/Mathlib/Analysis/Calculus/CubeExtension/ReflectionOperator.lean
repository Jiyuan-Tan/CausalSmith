module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionCoefficients
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionGeometry
public import Mathlib.Topology.Piecewise

/-!
# One-face reflection on a cube collar

Reflection weights combine inward samples to define a response on a thin
collar outside one face. This module records the operator, its exact agreement
on the original cube, and the first gluing obligation at the face.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- [The left collar](goal) of the normalized cube in [dimension d](hyp:d), for
[derivative order m](hyp:m) and [coordinate i](hyp:i), is the closed box whose
i-th coordinate ranges over `[-1 - 1/(m+1), 1]` and whose other coordinates
range over `[-1,1]`; it extends the cube outward by 1/(m + 1) past its left face
in coordinate i. -/
def leftCubeCollar (d m : ℕ) (i : Fin d) : Set (Fin d → ℝ) :=
  {x | ∀ j : Fin d,
    if j = i then x j ∈ Set.Icc (-1 - (1 : ℝ) / ((m : ℝ) + 1)) 1
    else x j ∈ Set.Icc (-1 : ℝ) 1}

/-- [The one-face reflection](goal) of [a response u](hyp:u) across the left face
in [coordinate i](hyp:i) of the normalized cube in [dimension d](hyp:d), with
[reflection weights a_0, …, a_m](hyp:a) for [derivative order m](hyp:m), equals u
at points whose i-th coordinate is at least −1, and at points with i-th
coordinate below −1 equals the weighted sum over q of a_q times u at the inward
reflection sample with dilation index q. -/
noncomputable def leftFaceReflection (d m : ℕ) (i : Fin d)
    (a : Fin (m + 1) → ℝ) (u : (Fin d → ℝ) → ℝ) :
    (Fin d → ℝ) → ℝ :=
  fun x => if x i < -1 then
    ∑ q : Fin (m + 1), a q * u (leftFaceSample d i q x)
  else u x

/-- [The one-face reflection of a response u agrees with u at every point of the
normalized cube](goal), whatever the reflection weights and whatever the values
of u outside the cube. -/
theorem leftFaceReflection_eqOn_cube (d m : ℕ) (i : Fin d)
    (a : Fin (m + 1) → ℝ) (u : (Fin d → ℝ) → ℝ) :
    Set.EqOn (leftFaceReflection d m i a u) u (cube d) := by
  intro x hx
  have hxi : -1 ≤ x i := (hx i).1
  simp [leftFaceReflection, not_lt.mpr hxi]

/-- If [the reflection weights a sum to one](hyp:ha), so that the reflection
reproduces constants, and [a response u is continuous on the closed
cube](hyp:hu), then [the one-face reflection of u is continuous on the closed
left collar](goal). -/
theorem leftFaceReflection_continuousOn (d m : ℕ) (i : Fin d)
    (a : Fin (m + 1) → ℝ)
    (ha : (∑ q : Fin (m + 1), a q) = 1)
    (u : (Fin d → ℝ) → ℝ)
    (hu : ContinuousOn u (cube d)) :
    ContinuousOn (leftFaceReflection d m i a u) (leftCubeCollar d m i) := by
  let f : (Fin d → ℝ) → ℝ := fun x =>
    ∑ q : Fin (m + 1), a q * u (leftFaceSample d i q x)
  let p : (Fin d → ℝ) → Prop := fun x => x i < -1
  have hleft : closure {x : Fin d → ℝ | p x} ⊆ {x | x i ≤ -1} := by
    apply closure_minimal
    · intro x hx
      change x i < -1 at hx
      exact le_of_lt hx
    · exact isClosed_le (continuous_apply i) continuous_const
  have hright : closure {x : Fin d → ℝ | ¬p x} ⊆ {x | -1 ≤ x i} := by
    apply closure_minimal
    · intro x hx
      change ¬ x i < -1 at hx
      exact le_of_not_gt hx
    · exact isClosed_le continuous_const (continuous_apply i)
  have hsample (q : Fin (m + 1)) :
      Continuous (leftFaceSample d i q) := by
    unfold leftFaceSample
    fun_prop
  have hf : ContinuousOn f
      (leftCubeCollar d m i ∩ closure {x : Fin d → ℝ | p x}) := by
    unfold f
    apply continuousOn_finsetSum
    intro q hq
    apply ContinuousOn.mul continuousOn_const
    apply hu.comp (hsample q).continuousOn
    intro x hx
    have hxi := (hx.1 i)
    simp only [↓reduceIte] at hxi
    apply leftFaceSample_mem_cube i q x
    · exact ⟨hxi.1, hleft hx.2⟩
    · intro j hji
      have hj := hx.1 j
      simp only [if_neg hji] at hj
      exact hj
  have hg : ContinuousOn u
      (leftCubeCollar d m i ∩ closure {x : Fin d → ℝ | ¬p x}) := by
    apply hu.mono
    intro x hx j
    have hj := hx.1 j
    by_cases hji : j = i
    · subst j
      simp only [Set.mem_Icc] at hj
      exact ⟨hright hx.2, hj.2⟩
    · simpa [leftCubeCollar, hji] using hj
  have hface : ∀ x ∈ leftCubeCollar d m i ∩ frontier {x : Fin d → ℝ | p x},
      f x = u x := by
    intro x hx
    have hle : x i ≤ -1 := hleft hx.2.1
    have hge : -1 ≤ x i := hright (by
      change x ∈ closure ({x : Fin d → ℝ | p x}ᶜ)
      rw [closure_compl]
      exact hx.2.2)
    have heq : x i = -1 := le_antisymm hle hge
    simp [f, leftFaceSample_fixed i _ x heq, ← Finset.sum_mul, ha]
  change ContinuousOn (fun x => if p x then f x else u x) (leftCubeCollar d m i)
  exact ContinuousOn.if hface hf hg

end Causalean.Mathlib.Analysis.Calculus.CubeExtension

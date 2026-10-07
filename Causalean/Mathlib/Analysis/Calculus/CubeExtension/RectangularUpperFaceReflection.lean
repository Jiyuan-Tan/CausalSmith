module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.RectangularFaceReflection
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.RectangularNegation

/-!
# Controlled reflection across an upper face of a rectangular box

This is the upper-face counterpart of rectangular lower-face reflection.
The collar width is a fixed fraction of the side length, so successive
reflections can be applied to nondegenerate boxes with quantitative control.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

/-- [The upper corner of the right collar](goal) of [the box with corners lo and
hi](hyp:lo,hi), for [derivative order m](hyp:m) and [coordinate i](hyp:i), agrees
with hi except in coordinate i, where it is raised by the fraction 1/(2(m + 1))
of the side length hi_i − lo_i. -/
noncomputable def rectRightUpper {d : ℕ} (lo hi : Fin d → ℝ) (m : ℕ)
    (i : Fin d) : Fin d → ℝ :=
  fun j => if j = i then
    hi j + (hi j - lo j) / (2 * ((m : ℝ) + 1)) else hi j

/-- [The right collar](goal) of [the box with corners lo and hi](hyp:lo,hi), for
[derivative order m](hyp:m) and [coordinate i](hyp:i), is the closed box that
extends the original box past its upper face in coordinate i only, by the
fraction 1/(2(m + 1)) of that coordinate's side length. -/
def rectRightCollar {d : ℕ} (lo hi : Fin d → ℝ) (m : ℕ)
    (i : Fin d) : Set (Fin d → ℝ) :=
  rectBox lo (rectRightUpper lo hi m i)

/-- If [0 < s](hyp:hs) and [the box with corners lo, hi has
positive side lengths](hyp:hbox), then for [derivative order m](hyp:m) and
[coordinate i](hyp:i) [there is a positive constant C such that every response u
in the intrinsic Hölder ball of order m, exponent s and radius L ≥ 0 on the box
agrees on the box with a response in the intrinsic Hölder ball of radius C·L on
the box's right collar in coordinate i](goal). The constant depends only on the
box, m, s and i.

Reflect coordinate `i` through the box midpoint, apply the lower-face
reflection theorem to the reversed box, and transport the result back. -/
theorem exists_rectRightFaceReflection_holder_constant {d : ℕ}
    (lo hi : Fin d → ℝ) (m : ℕ) (s : ℝ)
    (hs : 0 < s)
    (hbox : ∀ j, lo j < hi j) (i : Fin d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (L : ℝ), 0 ≤ L →
        HolderBallOn (rectBox lo hi) m s L u →
        ∃ v : (Fin d → ℝ) → ℝ,
          Set.EqOn v u (rectBox lo hi) ∧
          HolderBallOn (rectRightCollar lo hi m i) m s (C * L) v := by
  let nlo : Fin d → ℝ := fun j => -hi j
  let nhi : Fin d → ℝ := fun j => -lo j
  have hnbox : ∀ j, nlo j < nhi j := by
    intro j
    dsimp [nlo, nhi]
    linarith [hbox j]
  have hupper : rectLeftLower nlo nhi m i =
      fun j => -rectRightUpper lo hi m i j := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [rectLeftLower, rectRightUpper, nlo, nhi]
      ring
    · simp [rectLeftLower, rectRightUpper, nlo, hji]
  have hncollar : rectBox (fun j => -nhi j)
      (fun j => -rectLeftLower nlo nhi m i j) =
      rectRightCollar lo hi m i := by
    simp [rectRightCollar, hupper, nhi]
  have hextbox : ∀ j, rectLeftLower nlo nhi m i j < nhi j := by
    intro j
    by_cases hji : j = i
    · subst j
      have hw : 0 < nhi i - nlo i := sub_pos.mpr (hnbox i)
      have hd : 0 < (2 : ℝ) * ((m : ℝ) + 1) := by positivity
      have hf : 0 < (nhi i - nlo i) / (2 * ((m : ℝ) + 1)) := div_pos hw hd
      simp only [rectLeftLower, ↓reduceIte]
      linarith
    · simpa [rectLeftLower, hji] using hnbox j
  obtain ⟨C, hC, hreflect⟩ :=
    exists_rectLeftFaceReflection_holder_constant nlo nhi m s hs hnbox i
  refine ⟨C, hC, ?_⟩
  intro u L hL hu
  have hnu : HolderBallOn (rectBox nlo nhi) m s L (fun x => u (-x)) :=
    holderBallOn_rectBox_neg lo hi hbox s L u hu
  obtain ⟨w, hwagree, hwball⟩ := hreflect (fun x => u (-x)) L hL hnu
  refine ⟨fun x => w (-x), ?_, ?_⟩
  · intro x hx
    have hnx : -x ∈ rectBox nlo nhi :=
      (mem_rectBox_neg_iff lo hi (-x)).mpr (by simpa using hx)
    simpa using hwagree hnx
  · have htransport := holderBallOn_rectBox_neg
      (rectLeftLower nlo nhi m i) nhi hextbox s (C * L) w hwball
    simpa only [rectLeftCollar, hncollar] using htransport

end Causalean.Mathlib.Analysis.Calculus.CubeExtension

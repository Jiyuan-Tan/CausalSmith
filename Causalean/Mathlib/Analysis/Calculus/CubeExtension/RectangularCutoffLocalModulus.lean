module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.RectangularCutoffBoundaryTransfer
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.RectangularCutoffInteriorModulus

/-!
# Top jet modulus on the cutoff box

Inside a closed rectangular box, bounded jets of a smooth cutoff and the
intrinsic Hölder jets of a response give a uniform top-order modulus for
the localized response, including boundary traces.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open scoped ContDiff

/-- If [0 < s](hyp:hs) and [s ≤ 1](hyp:hs1), [the box with corners lo, hi
strictly contains the normalized cube](hyp:hmargin), [χ is smooth](hyp:hχ)
[with closed support inside the open box](hyp:hsupp), and [its ambient
derivatives of every order up to m + 1 are bounded in operator norm by
B ≥ 0](hyp:hB,hχbound), then [there is a positive constant C such that for every
response v in the intrinsic Hölder ball of order m, exponent s and radius R ≥ 0
on the closed box, the order-m ambient derivatives of the zero extension of χ·v
at any two points x, y of the closed box differ in norm by at most
C·R·‖x − y‖^s](goal).

Use the interior cutoff estimate and transfer its bound to the faces through
global `C^m` regularity of the zero extension. -/
theorem exists_rectCutoffExtension_box_modulus_constant (d m : ℕ) (s : ℝ)
    (hs : 0 < s) (hs1 : s ≤ 1)
    (lo hi : Fin d → ℝ) (hmargin : ∀ i, lo i < -1 ∧ 1 < hi i)
    (χ : (Fin d → ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hsupp : tsupport χ ⊆ rectOpenBox lo hi)
    (B : ℝ) (hB : 0 ≤ B)
    (hχbound : ∀ j ≤ m + 1, ∀ x,
      ‖iteratedFDeriv ℝ j χ x‖ ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (v : (Fin d → ℝ) → ℝ) (R : ℝ), 0 ≤ R →
        HolderBallOn (rectBox lo hi) m s R v →
        ∀ x ∈ rectBox lo hi, ∀ y ∈ rectBox lo hi,
          ‖iteratedFDeriv ℝ m (rectCutoffExtension lo hi χ v) x -
            iteratedFDeriv ℝ m (rectCutoffExtension lo hi χ v) y‖
              ≤ C * R * ‖x - y‖ ^ s := by
  obtain ⟨C, hC, hmod⟩ :=
    exists_rectCutoffExtension_interior_modulus_constant d m s hs hs1
      lo hi hmargin χ hχ hsupp B hB hχbound
  refine ⟨C, hC, ?_⟩
  intro v R hR hv
  have hwidth : ∀ i, lo i < hi i := by
    intro i
    have h := hmargin i
    linarith
  have hcont : Continuous
      (fun x => iteratedFDeriv ℝ m (rectCutoffExtension lo hi χ v) x) :=
    (rectCutoffExtension_contDiff m lo hi χ v hχ hsupp
      hv.regularity).continuous_iteratedFDeriv'
  exact holder_modulus_on_rectBox_of_openBox lo hi hwidth
    _ hcont s (C * R) hs (by
      intro x hx y hy
      simpa only [mul_assoc] using hmod v R hR hv x hx y hy)

end Causalean.Mathlib.Analysis.Calculus.CubeExtension

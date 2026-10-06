module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.RectangularCutoffBoundaryPoint
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.RectangularCutoffLocalModulus

/-!
# Top-order modulus for a localized rectangular response

The zero extension of a fixed smooth cutoff times an intrinsic box response
retains the top-order Hölder modulus with a uniform multiplicative factor.
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
at any two points x, y of the whole space differ in norm by at most
C·R·‖x − y‖^s](goal). -/
theorem exists_rectCutoffExtension_modulus_constant (d m : ℕ) (s : ℝ)
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
        ∀ x y,
          ‖iteratedFDeriv ℝ m (rectCutoffExtension lo hi χ v) x -
            iteratedFDeriv ℝ m (rectCutoffExtension lo hi χ v) y‖
              ≤ C * R * ‖x - y‖ ^ s := by
  obtain ⟨C, hC, hboxMod⟩ :=
    exists_rectCutoffExtension_box_modulus_constant d m s hs hs1
      lo hi hmargin χ hχ hsupp B hB hχbound
  refine ⟨C, hC, ?_⟩
  intro v R hR hv x y
  let J := iteratedFDeriv ℝ m (rectCutoffExtension lo hi χ v)
  have hopenSub : rectOpenBox lo hi ⊆ rectBox lo hi := by
    intro z hz i
    exact ⟨(hz i).1.le, (hz i).2.le⟩
  have hzero (z : Fin d → ℝ) (hz : z ∉ rectBox lo hi) : J z = 0 :=
    rectCutoffExtension_iteratedFDeriv_eq_zero_of_not_mem
      hsupp (fun h => hz (hopenSub h)) m
  have hcross (a b : Fin d → ℝ)
      (ha : a ∈ rectBox lo hi) (hb : b ∉ rectBox lo hi) :
      ‖J a - J b‖ ≤ C * R * ‖a - b‖ ^ s := by
    obtain ⟨z, hzbox, hzopen, hza⟩ :=
      exists_rectBox_boundary_point_le lo hi a b ha hb
    have hz : J z = 0 :=
      rectCutoffExtension_iteratedFDeriv_eq_zero_of_not_mem hsupp hzopen m
    have hp : ‖a - z‖ ^ s ≤ ‖a - b‖ ^ s :=
      Real.rpow_le_rpow (norm_nonneg _) hza hs.le
    calc
      ‖J a - J b‖ = ‖J a - J z‖ := by rw [hzero b hb, hz]
      _ ≤ C * R * ‖a - z‖ ^ s := hboxMod v R hR hv a ha z hzbox
      _ ≤ C * R * ‖a - b‖ ^ s := by gcongr
  change ‖J x - J y‖ ≤ C * R * ‖x - y‖ ^ s
  by_cases hx : x ∈ rectBox lo hi
  · by_cases hy : y ∈ rectBox lo hi
    · exact hboxMod v R hR hv x hx y hy
    · exact hcross x y hx hy
  · by_cases hy : y ∈ rectBox lo hi
    · simpa only [norm_sub_rev] using hcross y x hy hx
    · rw [hzero x hx, hzero y hy]
      simp only [sub_self, norm_zero]
      positivity

end Causalean.Mathlib.Analysis.Calculus.CubeExtension

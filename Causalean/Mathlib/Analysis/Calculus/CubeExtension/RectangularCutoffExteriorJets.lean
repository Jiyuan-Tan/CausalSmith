module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.RectangularCutoffZero

/-!
# Cutoff jets outside a rectangular box

When the cutoff support lies strictly inside the open box, the zero extension
vanishes near every point outside that open box. All ambient jets vanish there.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

/-- If [the closed support of a cutoff χ lies inside the open box](hyp:hsupp)
and [a point x lies outside the open box](hyp:hx), then for [every order
j](hyp:j) [the ambient order-j derivative at x of the zero extension of χ·v from
the closed box vanishes](goal). -/
theorem rectCutoffExtension_iteratedFDeriv_eq_zero_of_not_mem
    {d : ℕ} {lo hi : Fin d → ℝ} {χ v : (Fin d → ℝ) → ℝ}
    (hsupp : tsupport χ ⊆ rectOpenBox lo hi)
    {x : Fin d → ℝ} (hx : x ∉ rectOpenBox lo hi) (j : ℕ) :
    iteratedFDeriv ℝ j (rectCutoffExtension lo hi χ v) x = 0 := by
  have hnot : x ∉ tsupport χ := fun h => hx (hsupp h)
  have hnhds : (tsupport χ)ᶜ ∈ nhds x :=
    (isClosed_tsupport χ).isOpen_compl.mem_nhds hnot
  have hzero : rectCutoffExtension lo hi χ v =ᶠ[nhds x]
      (fun _ : Fin d → ℝ => (0 : ℝ)) := by
    filter_upwards [hnhds] with y hy
    have hχy : χ y = 0 := image_eq_zero_of_notMem_tsupport hy
    by_cases hbox : y ∈ rectBox lo hi <;>
      simp [rectCutoffExtension, hbox, hχy]
  rw [(hzero.iteratedFDeriv ℝ j).eq_of_nhds]
  simp

end Causalean.Mathlib.Analysis.Calculus.CubeExtension

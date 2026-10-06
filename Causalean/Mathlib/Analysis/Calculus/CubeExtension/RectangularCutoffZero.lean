module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.RectangularCutoffFunction

/-!
# Zero extension of a localized rectangular response

Multiplying a response by a smooth cutoff supported strictly inside the
box makes its zero extension smooth across the boundary of that box.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open scoped ContDiff
open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- [The cutoff extension](goal) of [a response v](hyp:v) by [a cutoff
χ](hyp:χ) from [the closed box with corners lo and hi](hyp:lo,hi) takes, at [a
point x](hyp:x), the value χ(x)·v(x) when x lies in the box and zero
otherwise. -/
noncomputable def rectCutoffExtension {d : ℕ} (lo hi : Fin d → ℝ)
    (χ v : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  by
    classical
    exact if x ∈ rectBox lo hi then χ x * v x else 0

/-- If [a cutoff χ is smooth](hyp:hχ) and [its closed support lies inside the
open box](hyp:hsupp), and [a response v is m times continuously differentiable
within the closed box](hyp:hv), then [the zero extension of χ·v from the closed
box is m times continuously differentiable on the whole space](goal). No
normalization of the cutoff on the cube is needed. -/
theorem rectCutoffExtension_contDiff {d : ℕ} (m : ℕ)
    (lo hi : Fin d → ℝ) (χ v : (Fin d → ℝ) → ℝ)
    (hχ : ContDiff ℝ ∞ χ)
    (hsupp : tsupport χ ⊆ rectOpenBox lo hi)
    (hv : ContDiffOn ℝ m v (rectBox lo hi)) :
    ContDiff ℝ m (rectCutoffExtension lo hi χ v) := by
  have hopen : IsOpen (rectOpenBox lo hi) := by
    have h := isOpen_set_pi (Set.finite_univ : (Set.univ : Set (Fin d)).Finite)
      (s := fun i => Set.Ioo (lo i) (hi i)) (fun i _ => isOpen_Ioo)
    simpa [rectOpenBox, Set.pi, Set.mem_Ioo] using h
  have hsub : rectOpenBox lo hi ⊆ rectBox lo hi := by
    intro x hx i
    exact ⟨(hx i).1.le, (hx i).2.le⟩
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ rectOpenBox lo hi
  · have hvx : ContDiffAt ℝ m v x :=
      hv.contDiffAt (Filter.mem_of_superset (hopen.mem_nhds hx) hsub)
    have hprod : ContDiffAt ℝ m (fun y => χ y * v y) x :=
      hχ.contDiffAt.of_le (by exact_mod_cast le_top) |>.mul hvx
    apply hprod.congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hx] with y hy
    simp [rectCutoffExtension, hsub hy]
  · have hnot : x ∉ tsupport χ := fun h => hx (hsupp h)
    have hnhds : (tsupport χ)ᶜ ∈ nhds x :=
      (isClosed_tsupport χ).isOpen_compl.mem_nhds hnot
    have hzero : ContDiffAt ℝ m (fun _ : Fin d → ℝ => (0 : ℝ)) x :=
      contDiffAt_const
    apply hzero.congr_of_eventuallyEq
    filter_upwards [hnhds] with y hy
    have hχy : χ y = 0 := image_eq_zero_of_notMem_tsupport hy
    by_cases hbox : y ∈ rectBox lo hi <;>
      simp [rectCutoffExtension, hbox, hχy]

/-- If [the box with corners lo, hi strictly contains the normalized
cube](hyp:hmargin), [a cutoff χ is smooth](hyp:hχ) [with closed support inside
the open box](hyp:hsupp) and [equal to one on the cube](hyp:hone), and [a
response v is m times continuously differentiable within the closed
box](hyp:hv), then [the zero extension of χ·v from the closed box is m times
continuously differentiable on the whole space and agrees with v on the
cube](goal). -/
theorem rectCutoffExtension_contDiff_eqOn_cube (d m : ℕ)
    (lo hi : Fin d → ℝ) (hmargin : ∀ i, lo i < -1 ∧ 1 < hi i)
    (χ v : (Fin d → ℝ) → ℝ)
    (hχ : ContDiff ℝ ∞ χ)
    (hsupp : tsupport χ ⊆ rectOpenBox lo hi)
    (hone : ∀ x ∈ cube d, χ x = 1)
    (hv : ContDiffOn ℝ m v (rectBox lo hi)) :
    ContDiff ℝ m (rectCutoffExtension lo hi χ v) ∧
      Set.EqOn (rectCutoffExtension lo hi χ v) v (cube d) := by
  have hopen : IsOpen (rectOpenBox lo hi) := by
    have h := isOpen_set_pi (Set.finite_univ : (Set.univ : Set (Fin d)).Finite)
      (s := fun i => Set.Ioo (lo i) (hi i)) (fun i _ => isOpen_Ioo)
    simpa [rectOpenBox, Set.pi, Set.mem_Ioo] using h
  have hsub : rectOpenBox lo hi ⊆ rectBox lo hi := by
    intro x hx i
    exact ⟨(hx i).1.le, (hx i).2.le⟩
  constructor
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ rectOpenBox lo hi
    · have hvx : ContDiffAt ℝ m v x :=
        hv.contDiffAt (Filter.mem_of_superset (hopen.mem_nhds hx) hsub)
      have hprod : ContDiffAt ℝ m (fun y => χ y * v y) x :=
        hχ.contDiffAt.of_le (by exact_mod_cast le_top) |>.mul hvx
      apply hprod.congr_of_eventuallyEq
      filter_upwards [hopen.mem_nhds hx] with y hy
      simp [rectCutoffExtension, hsub hy]
    · have hnot : x ∉ tsupport χ := fun h => hx (hsupp h)
      have hnhds : (tsupport χ)ᶜ ∈ nhds x :=
        (isClosed_tsupport χ).isOpen_compl.mem_nhds hnot
      have hzero : ContDiffAt ℝ m (fun _ : Fin d → ℝ => (0 : ℝ)) x :=
        contDiffAt_const
      apply hzero.congr_of_eventuallyEq
      filter_upwards [hnhds] with y hy
      have hχy : χ y = 0 := image_eq_zero_of_notMem_tsupport hy
      by_cases hbox : y ∈ rectBox lo hi <;>
        simp [rectCutoffExtension, hbox, hχy]
  · intro x hx
    have hbox : x ∈ rectBox lo hi := by
      intro i
      have hi := hx i
      exact ⟨by linarith [(hmargin i).1, hi.1],
        by linarith [(hmargin i).2, hi.2]⟩
    simp [rectCutoffExtension, hbox, hone x hx]

end Causalean.Mathlib.Analysis.Calculus.CubeExtension

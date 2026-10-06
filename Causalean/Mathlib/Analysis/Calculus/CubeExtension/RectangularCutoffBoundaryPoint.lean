module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.RectangularCutoffFunction

/-!
# A nearby rectangular boundary point

For a point in a closed box and a point outside it, moving one coordinate
of the first point to the intervening face reaches the boundary without
traveling farther than the original pair's distance.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

/-- If [x lies in a closed coordinate box](hyp:hx) and [y lies outside
it](hyp:hy), then [there is a boundary point z of the box (in the closed box but
not in the open box) whose distance to x is at most the distance from x to
y](goal).

Choose a coordinate where the outside point violates an endpoint. Replace
only that coordinate of the inside point by the violated endpoint. The `pi`
norm reduces the distance estimate to the corresponding scalar inequality. -/
theorem exists_rectBox_boundary_point_le {d : ℕ}
    (lo hi : Fin d → ℝ) (x y : Fin d → ℝ)
    (hx : x ∈ rectBox lo hi) (hy : y ∉ rectBox lo hi) :
    ∃ z : Fin d → ℝ,
      z ∈ rectBox lo hi ∧ z ∉ rectOpenBox lo hi ∧ ‖x - z‖ ≤ ‖x - y‖ := by
  classical
  have hy' : ∃ i : Fin d, y i < lo i ∨ hi i < y i := by
    simpa only [rectBox, Set.mem_setOf_eq, Set.mem_Icc, not_forall,
      not_and_or, not_le] using hy
  obtain ⟨i, hlow | hhigh⟩ := hy'
  · let z := Function.update x i (lo i)
    refine ⟨z, ?_, ?_, ?_⟩
    · intro j
      by_cases hji : j = i
      · subst j
        simpa [z, Set.mem_Icc] using (hx i).1.trans (hx i).2
      · simpa [z, Function.update_of_ne hji] using hx j
    · intro hz
      have := (hz i).1
      simp [z] at this
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (x - y))).2
      intro j
      by_cases hji : j = i
      · subst j
        have hle : |x i - lo i| ≤ |x i - y i| := by
          rw [abs_of_nonneg (by linarith [(hx i).1]),
            abs_of_nonneg (by linarith [(hx i).1])]
          linarith
        have hnorm : |x i - y i| ≤ ‖x - y‖ := by
          simpa [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (x - y) i
        simpa [z, Pi.sub_apply, Real.norm_eq_abs] using hle.trans hnorm
      · simp [z, Pi.sub_apply, Function.update_of_ne hji]
  · let z := Function.update x i (hi i)
    refine ⟨z, ?_, ?_, ?_⟩
    · intro j
      by_cases hji : j = i
      · subst j
        simpa [z, Set.mem_Icc] using (hx i).1.trans (hx i).2
      · simpa [z, Function.update_of_ne hji] using hx j
    · intro hz
      have := (hz i).2
      simp [z] at this
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (x - y))).2
      intro j
      by_cases hji : j = i
      · subst j
        have hle : |x i - hi i| ≤ |x i - y i| := by
          rw [abs_of_nonpos (by linarith [(hx i).2]),
            abs_of_nonpos (by linarith [(hx i).2])]
          linarith
        have hnorm : |x i - y i| ≤ ‖x - y‖ := by
          simpa [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (x - y) i
        simpa [z, Pi.sub_apply, Real.norm_eq_abs] using hle.trans hnorm
      · simp [z, Pi.sub_apply, Function.update_of_ne hji]

end Causalean.Mathlib.Analysis.Calculus.CubeExtension

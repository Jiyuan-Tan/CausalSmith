module
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Transfer of interior derivative bounds to endpoint within derivatives

Continuity of the within jet on a compact interval carries any common
interior bound to both endpoints. The statement makes no global smoothness
assumption outside the interval.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.HolderTaylor

/-- If all ambient derivatives through order `k` are bounded by the same
constant in the interior of a nondegenerate compact interval, then all
corresponding within derivatives have that bound throughout the closed
interval, including both endpoints.
[The derivative order, interval, bound, function, and regularity assumptions](hyp:k,a,b,B,hab,hB,f,hf,hinterior) yield [the stated closed-interval within-jet bound](goal). -/
theorem within_jet_bound_of_interior_ambient_bound
    (k : ℕ) (a b B : ℝ) (hab : a < b) (hB : 0 ≤ B)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ k f (Set.Icc a b))
    (hinterior : ∀ j ≤ k, ∀ x ∈ Set.Ioo a b,
      |iteratedDeriv j f x| ≤ B) :
    ∀ j ≤ k, ∀ x ∈ Set.Icc a b,
      |iteratedDerivWithin j f (Set.Icc a b) x| ≤ B := by
  /- On Ioo, the within derivative equals the ambient derivative because
  Icc is a neighborhood of each interior point. `ContDiffOn` and
  `uniqueDiffOn_Icc` make every within jet continuous on Icc. Since Ioo is
  dense in Icc, extend the interior bound with `le_on_closure`. -/
  intro j hj x hx
  have hu : UniqueDiffOn ℝ (Set.Icc a b) := uniqueDiffOn_Icc hab
  have hcont : ContinuousOn
      (fun y => |iteratedDerivWithin j f (Set.Icc a b) y|) (Set.Icc a b) :=
    (hf.continuousOn_iteratedDerivWithin (by exact_mod_cast hj) hu).abs
  have hbound : ∀ y ∈ Set.Ioo a b,
      |iteratedDerivWithin j f (Set.Icc a b) y| ≤ B := by
    intro y hy
    have hreg : ContDiffAt ℝ j f y :=
      ((hf.mono Set.Ioo_subset_Icc_self).contDiffAt
        (isOpen_Ioo.mem_nhds hy)).of_le (by exact_mod_cast hj)
    rw [iteratedDerivWithin_eq_iteratedDeriv hu hreg
      (Set.Ioo_subset_Icc_self hy)]
    exact hinterior j hj y hy
  exact le_on_closure hbound
    (by simpa [closure_Ioo hab.ne] using hcont)
    continuousOn_const (by simpa [closure_Ioo hab.ne] using hx)

end Causalean.Mathlib.Analysis.Calculus.HolderTaylor

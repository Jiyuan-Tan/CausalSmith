module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.RectangularCutoffFunction
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Hölder bounds up to rectangular faces

A continuous map satisfying a Hölder estimate on the open rectangular box
satisfies the same estimate on its closed box.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

set_option maxHeartbeats 800000 in
-- Elaboration of the product-space closure inequality needs extra heartbeats.
/-- If [a box has positive side lengths](hyp:hwidth), [a map J into a normed
group is continuous](hyp:hJ), [s > 0](hyp:hs), and [‖J(x) − J(y)‖ ≤ C·‖x − y‖^s
for all points x, y of the open box](hyp:hopen), then [the same bound holds for
all points x, y of the closed box](goal).

Use `Set.mem_closure_pi` and `closure_Ioo` to put every closed-box point in
the closure of the open box. Then pass the pairwise inequality to the limit
using continuity of the map, subtraction, norm, and the positive real power. -/
theorem holder_modulus_on_rectBox_of_openBox
    {d : ℕ} {F : Type*} [NormedAddCommGroup F]
    (lo hi : Fin d → ℝ) (hwidth : ∀ i, lo i < hi i)
    (J : (Fin d → ℝ) → F) (hJ : Continuous J)
    (s C : ℝ) (hs : 0 < s)
    (hopen : ∀ x ∈ rectOpenBox lo hi, ∀ y ∈ rectOpenBox lo hi,
      ‖J x - J y‖ ≤ C * ‖x - y‖ ^ s) :
    ∀ x ∈ rectBox lo hi, ∀ y ∈ rectBox lo hi,
      ‖J x - J y‖ ≤ C * ‖x - y‖ ^ s := by
  have hopen_eq : rectOpenBox lo hi =
      Set.univ.pi (fun i : Fin d => Set.Ioo (lo i) (hi i)) := by
    ext z
    simp [rectOpenBox, Set.pi, Set.mem_Ioo]
  have hclosure (z : Fin d → ℝ) (hz : z ∈ rectBox lo hi) :
      z ∈ closure (rectOpenBox lo hi) := by
    rw [hopen_eq]
    rw [mem_closure_pi]
    intro i _
    rw [closure_Ioo (hwidth i).ne]
    exact hz i
  have hleft : Continuous (fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
      ‖J p.1 - J p.2‖) :=
    ((hJ.comp continuous_fst).sub (hJ.comp continuous_snd)).norm
  have hright : Continuous (fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
      C * ‖p.1 - p.2‖ ^ s) :=
    continuous_const.mul ((Real.continuous_rpow_const hs.le).comp
      ((continuous_fst.sub continuous_snd).norm))
  intro x hx y hy
  refine le_on_closure (s := rectOpenBox lo hi ×ˢ rectOpenBox lo hi)
    (f := fun p => ‖J p.1 - J p.2‖)
    (g := fun p => C * ‖p.1 - p.2‖ ^ s) (x := (x, y))
    ?_ hleft.continuousOn hright.continuousOn ?_
  · intro p hp
    exact hopen p.1 hp.1 p.2 hp.2
  · rw [closure_prod_eq]
    exact ⟨hclosure x hx, hclosure y hy⟩

end Causalean.Mathlib.Analysis.Calculus.CubeExtension

module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.JetSymmetry
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Symmetry of finite-order within-set jets

At points approached by the interior of a uniquely differentiable set,
iterated within-set derivatives of a `C^m` function are symmetric in their
direction slots. This recovers the product-jet formula from its diagonal form.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open scoped Topology

/-- At a point in the closure of the interior of a uniquely differentiable
set, the order-`m` within-set jet of a `C^m` scalar function is invariant
under every permutation of its
direction slots. At interior points, use the finite-order ambient permutation theorem from
`CubeInterpolation.JetSymmetry` and agreement of ambient and within-set jets.
The within-set jet is continuous on `S`, so equality extends to points in the
closure of its interior. The closure condition holds for rectangular boxes. Together, [the listed inputs and assumptions](hyp:d,m,S,huniq,f,hf,x,hx,hxcl,σ,v) establish [the stated conclusion](goal). -/
theorem iteratedFDerivWithin_comp_perm_of_contDiffOn
    {d m : ℕ} {S : Set (Fin d → ℝ)}
    (huniq : UniqueDiffOn ℝ S)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiffOn ℝ m f S)
    {x : Fin d → ℝ} (hx : x ∈ S)
    (hxcl : x ∈ closure (interior S))
    (σ : Equiv.Perm (Fin m)) (v : Fin m → Fin d → ℝ) :
    iteratedFDerivWithin ℝ m f S x (v ∘ σ) =
      iteratedFDerivWithin ℝ m f S x v := by
  have hint : Set.EqOn
      (fun z => iteratedFDerivWithin ℝ m f S z (v ∘ σ))
      (fun z => iteratedFDerivWithin ℝ m f S z v) (interior S) := by
    intro z hz
    dsimp only
    have hzS : z ∈ S := interior_subset hz
    have hzn : S ∈ 𝓝 z :=
      Filter.mem_of_superset (isOpen_interior.mem_nhds hz) interior_subset
    have hdz : ContDiffAt ℝ m f z := hf.contDiffAt hzn
    rw [iteratedFDerivWithin_eq_iteratedFDeriv huniq hdz hzS]
    exact Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.finite_order_iteratedFDeriv_perm
      hdz v σ
  have hcont : ContinuousOn (iteratedFDerivWithin ℝ m f S) S :=
    hf.continuousOn_iteratedFDerivWithin le_rfl huniq
  have hleft : ContinuousOn
      (fun z => iteratedFDerivWithin ℝ m f S z (v ∘ σ)) S :=
    (continuous_eval_const (v ∘ σ)).comp_continuousOn hcont
  have hright : ContinuousOn
      (fun z => iteratedFDerivWithin ℝ m f S z v) S :=
    (continuous_eval_const v).comp_continuousOn hcont
  have hsub : interior S ⊆ S ∩ closure (interior S) :=
    fun z hz => ⟨interior_subset hz, subset_closure hz⟩
  exact (hint.of_subset_closure
    (hleft.mono Set.inter_subset_left) (hright.mono Set.inter_subset_left)
    hsub Set.inter_subset_right) ⟨hx, hxcl⟩

end Causalean.Mathlib.Analysis.Calculus.CubeExtension

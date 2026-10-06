module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.JetNorm

/-!
# Coordinate criterion for convergence of multilinear maps

For multilinear maps on a finite product of finite-dimensional coordinate
spaces, convergence on all tuples of coordinate vectors implies convergence
in the operator norm. This isolates the topological step in face trace proofs.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

/-- Let [F be a family, indexed along a filter, of continuous j-linear maps on
d-dimensional coordinate space](hyp:F) and [T a continuous j-linear map on the
same space](hyp:T). If [for every tuple of coordinate directions the values of F
on the corresponding standard basis vectors converge to the value of T on those
vectors](hyp:h), then [F converges to T along the filter](goal). -/
theorem tendsto_multilinearMap_of_coordinate_tendsto
    (d j : ℕ) {α : Type*} [TopologicalSpace α] {l : Filter α}
    (F : α → ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → ℝ) ℝ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → ℝ) ℝ)
    (h : ∀ f : Fin j → Fin d,
      Filter.Tendsto (fun x => F x (fun k => Pi.single (f k) (1 : ℝ))) l
        (nhds (T (fun k => Pi.single (f k) (1 : ℝ))))) :
    Filter.Tendsto F l (nhds T) := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_coord_multilinear_norm_constant d j
  let E : α → ℝ := fun x =>
    ∑ f : Fin j → Fin d,
      |(F x - T) (fun k => Pi.single (f k) (1 : ℝ))|
  have hE : Filter.Tendsto E l (nhds 0) := by
    have hf (f : Fin j → Fin d) :
        Filter.Tendsto
          (fun x => |(F x - T) (fun k => Pi.single (f k) (1 : ℝ))|)
          l (nhds 0) := by
      have hs := (h f).sub_const (T (fun k => Pi.single (f k) (1 : ℝ)))
      have hs' : Filter.Tendsto
          (fun x => F x (fun k => Pi.single (f k) (1 : ℝ)) -
            T (fun k => Pi.single (f k) (1 : ℝ))) l (nhds 0) := by
        simpa using hs
      simpa [sub_apply, Real.norm_eq_abs] using hs'.norm
    simpa [E] using tendsto_finsetSum Finset.univ (fun f _ => hf f)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun x => norm_nonneg _) (fun x => ?_)
    (by simpa using Filter.Tendsto.const_mul C hE)
  apply hbound j le_rfl (F x - T) (E x)
  · dsimp [E]
    positivity
  · intro f
    dsimp [E]
    exact Finset.single_le_sum
      (fun g _ => abs_nonneg ((F x - T) (fun k => Pi.single (g k) (1 : ℝ))))
      (Finset.mem_univ f)

end Causalean.Mathlib.Analysis.Calculus.CubeExtension

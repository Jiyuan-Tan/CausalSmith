module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.RoleOverlapMoments

/-!
Exact shared-role variance decomposition for rectangular cross averages of a square-integrable
kernel. Pair-law transport identifies each covariance with a partial-kernel variance, and exact
configuration counts give the nonempty-pattern weights, including the one-sample case.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull

-- @node: lem:exact-role-overlap
/-- Every nonempty shared-role pattern contributes its exact configuration count times
the variance of the corresponding partial integral. Applying this to a fixed trained kernel
is the conditional version, with no new conditioning regularity assumption. -/
lemma exact_role_overlap_variance {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (d m : ℕ) (hd : 1 ≤ d) (hm : 1 ≤ m)
    (h : (Fin d → E) → ℝ) (hMeas : Measurable h)
    (hL2 : MemLp h 2 (Measure.pi (fun _ : Fin d => P))) :
    variance (roleAverage d m h)
      (Measure.pi (fun _ : Fin d => Measure.pi (fun _ : Fin m => P))) =
    ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset.erase ∅,
      ((m - 1 : ℕ) : ℝ) ^ (d - S.card) / (m : ℝ) ^ d * 
        variance (partialRoleKernel P d S h) (Measure.pi (fun _ : Fin d => P)) := by
  classical
  rw [role_average_variance_expansion P d m h hL2]
  have overlap_covariance := partial_overlap_role_covariance P d m h hMeas hL2
  simp_rw [overlap_covariance]
  exact normalized_shared_role_sum d m hm
    (fun S => variance (partialRoleKernel P d S h) (Measure.pi (fun _ : Fin d => P)))
    (partial_role_kernel_empty_variance P d h)

end CausalSmith.Stat.DensityEffectRoughNull

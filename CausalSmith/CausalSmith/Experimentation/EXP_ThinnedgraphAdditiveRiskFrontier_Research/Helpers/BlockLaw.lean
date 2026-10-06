module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.PosteriorTreatedDensity

/-!
# Complete original-record block likelihood assembly

The fixed-partition density and compatible-completion count recover the full
record with every retained edge and assignment coordinate.
-/

public section

open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Support, target, independent source reveals, and the complete-record likelihood
reconstruction.  [For the stated data and conditions](hyp:n,B,d,σ,h,q,D,hn,hB,hd,hfit,hh,hq,ha,hw,hi), [the stated conclusion holds](goal). -/
-- @node: lem:block-law
lemma block_law (n B d : ℕ) (σ : Bool) (h q : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n)))
    (hn : 4 ≤ n) (hB : 1 ≤ B) (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (hh : h ∈ Set.Icc 0 (1 / 4)) (hq : q ∈ Set.Icc 0 1)
    (ha : AssignmentLaw D) (hw : AuditLaw D q) (hi : DesignIndependent D) :
    (∀ᵐ ξ ∂(blockParamLaw B d), ScheduleClass (blockSchedule n B d σ h ξ) d ∧
      tte (blockSchedule n B d σ h ξ) = signOf σ * (B * d : ℕ) * h / n) ∧
    (retainedGraphMarginal n B d D).map (sourceReveals n B d) =
      Measure.pi (fun _ : Fin (B * d) => bernoulliLaw (retentionP d q)) ∧
    blockMixtureLawOf n B d D σ h = reconstructedLaw n B d D σ h ∧
    (blockMixtureLawOf n B d D σ h).map (fun o => (o.1, o.2.1)) =
      graphAssignMarginal n B d D ∧
    (∀ᵐ hz ∂(graphAssignMarginal n B d D),
      undiscovered n B d hz.1 = 0 → hiddenTreated n B d hz.1 hz.2 = 0 ∧
        (undiscovered n B d hz.1).choose (hiddenTreated n B d hz.1 hz.2) = 1) := by
  let : NeZero n := ⟨by omega⟩
  let := design_isProbabilityMeasure D q ha hw hi
  refine ⟨block_support n B d σ h hB hd hfit hh,
    block_reveal_law n B d q D hB hd hfit hq ha hw hi, ?_,
    block_mixture_graphAssignMarginal n B d σ h D,
    block_hidden_zero_endpoint n B d D hfit⟩
  rw [design_eq_thinnedDesign D q ha hw hi,
    blockMixtureLawOf_hidden_completion_bind n B d hd hfit σ h q hq,
    reconstructedLaw]
  apply Measure.bind_congr_right
  have hv : ∀ᵐ hz ∂(graphAssignMarginal n B d (thinnedDesign (Fin n) q)),
      ValidRetainedGraph n B d hz.1 :=
    (ae_map_iff (by fun_prop) (by measurability)).mp
      (retainedGraphMarginal_valid n B d (thinnedDesign (Fin n) q) hfit)
  filter_upwards [hv] with hz hH
  exact hiddenCompletionKernel_eq_blockDensity n B d hd hfit σ h hz hH

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier

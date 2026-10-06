module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.CollisionEnvelope

/-! # Finite estimates used by the birthday occupancy asymptotic. -/

@[expose] public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

/-- The birthday pair scale is asymptotic to half the square of the expected
audit count, even when the audit probability varies with the horizon. -/
-- @node: collisionScale_over_mean_sq_tendsto_half
lemma collisionScale_over_mean_sq_tendsto_half
    (Tseq : Nat → Nat) (etaseq : Nat → ℝ)
    (heta : ∀ j, etaseq j ∈ Set.Icc (0 : ℝ) 1)
    (hmean : Filter.Tendsto (fun j => (Tseq j : ℝ) * etaseq j)
      Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun j => collisionScale (Tseq j) (etaseq j) /
        (((Tseq j : ℝ) * etaseq j) ^ 2))
      Filter.atTop (nhds (1 / 2 : ℝ)) := by
  have hT : Filter.Tendsto (fun j => (Tseq j : ℝ)) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono' Filter.atTop _ hmean
    filter_upwards [] with j
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) (heta j).2
  have hmu_pos : Filter.Eventually (fun j => 0 < (Tseq j : ℝ) * etaseq j)
      Filter.atTop := hmean.eventually_gt_atTop 0
  have heq : Filter.Eventually
      (fun j => collisionScale (Tseq j) (etaseq j) /
        (((Tseq j : ℝ) * etaseq j) ^ 2) =
        (1 - (Tseq j : ℝ)⁻¹) / 2) Filter.atTop := by
    filter_upwards [hmu_pos] with j hj
    have hTj : (Tseq j : ℝ) ≠ 0 := by
      intro h
      simp [h] at hj
    have hetaj : etaseq j ≠ 0 := by
      intro h
      simp [h] at hj
    unfold collisionScale
    field_simp
  have hinv : Filter.Tendsto (fun j => (Tseq j : ℝ)⁻¹)
      Filter.atTop (nhds 0) := hT.inv_tendsto_atTop
  have hlim : Filter.Tendsto (fun j => (1 - (Tseq j : ℝ)⁻¹) / 2)
      Filter.atTop (nhds (1 / 2 : ℝ)) := by
    convert (tendsto_const_nhds.sub hinv).div_const (2 : ℝ) using 1; norm_num
  exact hlim.congr' (heq.mono (fun j hj => hj.symm))

end CausalSmith.Stat.PomdpStateauditMinimax

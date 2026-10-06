module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.PairedTent

/-! Public paired-tent ranks and cell-width bounds. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- The public paired rank lies between twice and four times its unrounded target. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: tentRank_bounds
lemma tentRank_bounds (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n) :
    2 ≤ tentRank n v ∧
    2*(n:ℝ)^(2*qExp v/(2*v.γ+qExp v)) ≤ (tentRank n v:ℝ) ∧
    (tentRank n v:ℝ) ≤ 4*(n:ℝ)^(2*qExp v/(2*v.γ+qExp v)) := by
  have hp : 0 < v.p := by linarith [hv.1.1]
  have hq : 0 < qExp v := div_pos (by linarith [hv.1.1]) hp
  have hg : 0 < v.γ := by linarith [hv.2.2.2.1]
  have he : 0 ≤ 2*qExp v/(2*v.γ+qExp v) := by positivity
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have ht : 1 ≤ (n:ℝ)^(2*qExp v/(2*v.γ+qExp v)) := Real.one_le_rpow hnR he
  have hlo := Nat.le_ceil ((n:ℝ)^(2*qExp v/(2*v.γ+qExp v)))
  have hhi := Nat.ceil_lt_add_one (by positivity : 0 ≤ (n:ℝ)^(2*qExp v/(2*v.γ+qExp v)))
  have hc : 1 ≤ Nat.ceil ((n:ℝ)^(2*qExp v/(2*v.γ+qExp v))) := by
    exact_mod_cast (show (1:ℝ) ≤ Nat.ceil ((n:ℝ)^(2*qExp v/(2*v.γ+qExp v))) from ht.trans hlo)
  refine ⟨by unfold tentRank; omega, ?_, ?_⟩ <;>
    simp only [tentRank, Nat.cast_mul, Nat.cast_ofNat] <;> linarith

/-- A positive paired rank gives a cell width strictly between zero and one. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: tentH_bounds
lemma tentH_bounds (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n) :
    0 < tentH n v ∧ tentH n v < 1 := by
  have hr : (2:ℝ) ≤ tentRank n v := by exact_mod_cast (tentRank_bounds v hv n hn).1
  unfold tentH
  constructor
  · positivity
  · exact inv_lt_one_of_one_lt₀ (by linarith)

end CausalSmith.Stat.FinitepHomogeneityDensegamma

module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.RateFailure

/-! Assembly of the deterministic tuning restrictions and public expected-length
budget, including the pilot failure contribution in (57)--(58). -/

public section
noncomputable section
open Filter
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- The frozen ranks eventually satisfy every corrected-mean restriction and
all reporting guards, and the full public length budget has no logarithmic loss. -/
-- @node: tuned_rate_arithmetic
lemma tuned_rate_arithmetic :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, ∀ n, n0 ≤ n →
      let m := roleSize n
      reportingBranch n ∧ tunedMx m ≤ m ∧ tunedQ m ≤ m ∧
      MeanRanks (tunedMx m) (tunedMy m) (tunedK m) (tunedL m) (tunedT m)
        (tunedJ m) (tunedQ m) (tunedKt m) ∧
      4 * ((aci (tunedB n) (tunedW n)) ^ 2 + 
        dci (tunedB n) (tunedW n) (tunedV n) (tunedJ m)) + 
        16 * zetaAllow m (tunedMx m) (tunedMy m) ≤ C * frontierRate n := by
  obtain ⟨CI, hCI, hi⟩ := tuned_inversion_budget_eventually_frontier_rate_bound
  let CZ : ℝ := (2 * (Nat.factorial 10 : ℝ) * 32 ^ 10 + 6) *
    (26 : ℝ) ^ (16 / 29 : ℝ)
  refine ⟨CI + 16 * CZ, by positivity, ?_⟩
  have hall : ∀ᶠ n : ℕ in atTop,
      reportingBranch n ∧ tunedMx (roleSize n) ≤ roleSize n ∧
      tunedQ (roleSize n) ≤ roleSize n ∧
      MeanRanks (tunedMx (roleSize n)) (tunedMy (roleSize n))
        (tunedK (roleSize n)) (tunedL (roleSize n)) (tunedT (roleSize n))
        (tunedJ (roleSize n)) (tunedQ (roleSize n)) (tunedKt (roleSize n)) ∧
      4 * ((aci (tunedB n) (tunedW n)) ^ 2 +
        dci (tunedB n) (tunedW n) (tunedV n) (tunedJ (roleSize n))) +
        16 * zetaAllow (roleSize n) (tunedMx (roleSize n)) (tunedMy (roleSize n)) ≤
          (CI + 16 * CZ) * frontierRate n := by
    filter_upwards [hi, reportingBranch_eventually] with n hbudget hbranch
    have hm : 3 ≤ roleSize n := hbranch.1
    obtain ⟨hx, hq, hr⟩ := tuned_rank_compatibility (roleSize n) hm
    have hz := tuned_zeta_frontier_rate_bound n hm
    change _ ≤ CZ * frontierRate n at hz
    exact ⟨hbranch, hx, hq, hr, by nlinarith⟩
  exact eventually_atTop.mp hall

end CausalSmith.Stat.DensityEffectRoughNull


module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.LowerBanditTransport
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.LowerBanditCode
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.LowerBanditInformation
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.LowerRegimeCombination
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.LowerSparseTesting
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SparseFilterInformation
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.FanoGate
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.TestingRegret
public import Causalean.Stat.Minimax.MinimaxValue

/-! # Conditional common-kernel minimax lower bound -/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

-- @node: thm:common-kernel-lower
/-- For [the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the mixing scale assumption](hyp:ht0), and
[the policy-overlap scale assumption](hyp:hzeta), this establishes
[the common kernel lower result](goal). -/
theorem common_kernel_lower (t0 zeta : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) :
    ∃ (cl : ℝ) (Tl : Nat), 0 < cl ∧
      ∀ (T M : Nat) (C : ℝ), (hT : max 1 Tl ≤ T) → (hM : 2 ≤ M) → (hC : 1 ≤ C) →
        cl * (regretFrontier T M t0 zeta C ht0 hzeta hC (by omega) hM) ≤
          minimaxRegret T M t0 zeta C := by
  obtain ⟨c1, hc1, hparam⟩ := lower_bandit_parametric_component t0 zeta ht0 hzeta
  obtain ⟨c2, eta0, hc2, heta0, hhidden⟩ :=
    lower_sparse_hidden_component t0 zeta ht0 hzeta
  let beta := CausalSmith.Stat.PomdpLatentOverlapMinimax.rateExponent t0 zeta
  let K := eta0 ^ (-((1 - beta) / 2))
  let cl := min c1 (min (c1 / (1 + K)) (min c1 c2 / 2))
  have hK : 0 ≤ K := Real.rpow_nonneg heta0.le _
  refine ⟨cl, 1, lower_combined_constant_pos c1 c2 K hc1 hc2 hK, ?_⟩
  intro T M C hT hM hC
  have hCR : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hq : 0 ≤ CausalSmith.Stat.PomdpLatentOverlapMinimax.overlapRadius C := by
    exact div_nonneg (sub_nonneg.mpr hC) hCR.le
  have hu : 0 < (listInformationRatio T M (by omega) hM) := by
    unfold listInformationRatio
    exact div_pos (Real.log_pos (by exact_mod_cast (show 1 < M by omega)))
      (by exact_mod_cast (show 0 < T by omega))
  have hbeta : beta < 1 := by
    dsimp [beta, CausalSmith.Stat.PomdpLatentOverlapMinimax.rateExponent]
    apply (div_lt_one (by positivity)).mpr
    nlinarith [mul_pos ht0 hzeta]
  apply lower_frontier_of_component_bounds _ _ beta eta0 c1 c2 _ hq hu hbeta heta0
    hc1 hc2 (hparam T M C hT hM hC)
  intro hqpos hsmall
  have hCpos : 1 < C := by
    by_contra h
    have hCe : C = 1 := le_antisymm (le_of_not_gt h) hC
    simp [hCe, CausalSmith.Stat.PomdpLatentOverlapMinimax.overlapRadius] at hqpos
  exact hhidden T M C hT hM hCpos hsmall

end CausalSmith.Stat.PomdpPolicyclassRegret

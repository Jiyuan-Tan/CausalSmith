import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Basic
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.T_coarse_two_arm_minimax_lower
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.EmbeddedTwoArm
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.FirstOrderUpper

/-! Sign-group embedding of the unrestricted two-arm decision problem. -/

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

-- @node: thm:embedded-two-arm-converse
/-- [there are at least two treatment arms](hyp:hK), [the population size is positive](hyp:hn), [every multi-arm problem contains a scaled two-arm sign-group subproblem, yielding the stated two-arm minimax lower bound](goal). -/
theorem embedded_two_arm_converse (K n : ℕ) (c : Contrast ℝ K)
    (hK : AdmissibleArmCount K) (hn : 0 < n) :
    C0 c * rho2 n ≤ rhoN K n c ∧
    rhoN K n c ≤ C0 c / n ∧
    (8 ≤ n →
      0 ≤ dN K c n ∧
      dN K c n ≤ C0 c * ((n : ℝ)⁻¹ - rho2 n) ∧
      dN K c n ≤ 43 * C0 c * (n : ℝ) ^ (-(4 / 3 : ℝ))) ∧
    ((Sc c).card = 2 →
      rhoN K n c = C0 c * rho2 n ∧
      dN K c n = C0 c * ((n : ℝ)⁻¹ - rho2 n)) := by
  have hlow : C0 c * rho2 n ≤ rhoN K n c := embeddedTwoArmLowerBound K n c
  have hC0 : 0 ≤ C0 c := by unfold C0; positivity
  have hu : rhoN K n c ≤ C0 c / n := by
    unfold rhoN
    exact (Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
      (fun p z => p.1.mse_nonneg _ _) (contrastWeightedProcedure K n c)).trans
        (contrastWeightedProcedure_upperRisk K n c hn)
  have hsupp : (Sc c).card = 2 → rhoN K n c = C0 c * rho2 n := by
    intro hc
    exact le_antisymm (supportTwoUpperBound K n c hc) hlow
  refine ⟨hlow, hu, ?_, ?_⟩
  · intro hn8
    have hcoarse := (coarse_two_arm_minimax_lower n hn8).2
    have hd0 : 0 ≤ dN K c n := by
      unfold dN
      linarith
    have hdmid : dN K c n ≤ C0 c * ((n : ℝ)⁻¹ - rho2 n) := by
      unfold dN
      rw [div_eq_mul_inv]
      linarith
    have hdlast : dN K c n ≤ 43 * C0 c * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
      calc
        dN K c n ≤ C0 c * ((n : ℝ)⁻¹ - rho2 n) := hdmid
        _ ≤ C0 c * (43 * (n : ℝ) ^ (-(4 / 3 : ℝ))) := by
          gcongr
          linarith
        _ = 43 * C0 c * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by ring
    exact ⟨hd0, hdmid, hdlast⟩
  · intro hc
    have hrho := hsupp hc
    refine ⟨hrho, ?_⟩
    unfold dN
    rw [hrho, div_eq_mul_inv]
    ring

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.TMatchedRegretFrontier
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Contextual-bandit boundary and hidden-memory dominance -/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open CausalSmith.Stat.PomdpLatentOverlapMinimax

-- @node: prop:phase-boundary
/-- For [the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the mixing scale assumption](hyp:ht0), and
[the policy-overlap scale assumption](hyp:hzeta), this establishes
[the phase boundary result](goal). -/
theorem phase_boundary (t0 zeta : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) :
    (∀ (T M : Nat), (hT : 1 ≤ T) → (hM : 2 ≤ M) →
      (regretFrontier T M t0 zeta 1 ht0 hzeta (le_refl 1) (by omega) hM) =
        min 1 (Real.sqrt (Real.log (M : ℝ) / T))) ∧
    (∀ (q u c : ℝ), 0 < q → 0 < u → 0 < c →
      q ^ (1 - rateExponent t0 zeta) *
          u ^ (rateExponent t0 zeta / 2) / Real.sqrt u =
            (q ^ 2 / u) ^ ((1 - rateExponent t0 zeta) / 2) ∧
      (c * u ≤ q ^ 2 →
        c ^ ((1 - rateExponent t0 zeta) / 2) ≤
          q ^ (1 - rateExponent t0 zeta) *
            u ^ (rateExponent t0 zeta / 2) / Real.sqrt u) ∧
      (q ^ 2 ≤ c * u →
        q ^ (1 - rateExponent t0 zeta) *
          u ^ (rateExponent t0 zeta / 2) / Real.sqrt u ≤
            c ^ ((1 - rateExponent t0 zeta) / 2))) ∧
    (∃ (c K : ℝ) (T0 : Nat), 0 < c ∧ c ≤ K ∧
      ∀ (T M : Nat) (C : ℝ), (hT : max 1 T0 ≤ T) → (hM : 2 ≤ M) → (hC : 1 ≤ C) →
        c * (regretFrontier T M t0 zeta C ht0 hzeta hC (by omega) hM) ≤
          minimaxRegret T M t0 zeta C ∧
        minimaxRegret T M t0 zeta C ≤
          K * (regretFrontier T M t0 zeta C ht0 hzeta hC (by omega) hM)) := by
  have hbeta : 0 < 1 - rateExponent t0 zeta := by
    unfold rateExponent
    have hprod : 0 < t0 * zeta := mul_pos ht0 hzeta
    have hden : 0 < 2 + t0 * zeta := by linarith
    have hlt : 2 / (2 + t0 * zeta) < 1 := by
      apply (div_lt_iff₀ hden).2
      linarith
    linarith
  refine ⟨?_, ?_, matched_regret_frontier t0 zeta ht0 hzeta⟩
  · intro T M hT hM
    simp only [regretFrontier, listInformationRatio, overlapRadius, sub_self, zero_div,
      Real.zero_rpow (ne_of_gt hbeta), zero_mul, add_zero]
  · intro q u c hq hu hc
    have he : 0 ≤ (1 - rateExponent t0 zeta) / 2 := by linarith
    have hratio :
        q ^ (1 - rateExponent t0 zeta) *
            u ^ (rateExponent t0 zeta / 2) / Real.sqrt u =
          (q ^ 2 / u) ^ ((1 - rateExponent t0 zeta) / 2) := by
      calc
        q ^ (1 - rateExponent t0 zeta) *
            u ^ (rateExponent t0 zeta / 2) / Real.sqrt u =
          q ^ (1 - rateExponent t0 zeta) *
            (u ^ (rateExponent t0 zeta / 2) / u ^ (1 / 2 : ℝ)) := by
              rw [Real.sqrt_eq_rpow, mul_div_assoc]
        _ = q ^ (1 - rateExponent t0 zeta) *
            u ^ (rateExponent t0 zeta / 2 - 1 / 2) := by
              rw [Real.rpow_sub hu]
        _ = (q ^ 2 / u) ^ ((1 - rateExponent t0 zeta) / 2) := by
              rw [Real.div_rpow (by positivity) (by positivity)]
              have hqpow : (q ^ 2) ^ ((1 - rateExponent t0 zeta) / 2) =
                  q ^ (1 - rateExponent t0 zeta) := by
                rw [← Real.rpow_natCast q 2, ← Real.rpow_mul (le_of_lt hq)]
                congr 1
                ring
              rw [hqpow, show rateExponent t0 zeta / 2 - 1 / 2 =
                -((1 - rateExponent t0 zeta) / 2) by ring]
              rw [Real.rpow_neg (le_of_lt hu)]
              rfl
    refine ⟨hratio, ?_, ?_⟩
    · intro hcu
      rw [hratio]
      apply Real.rpow_le_rpow (le_of_lt hc) _ he
      exact (le_div_iff₀ hu).2 hcu
    · intro hqu
      rw [hratio]
      apply Real.rpow_le_rpow (div_nonneg (sq_nonneg q) (le_of_lt hu)) _ he
      exact (div_le_iff₀ hu).2 hqu

end CausalSmith.Stat.PomdpPolicyclassRegret

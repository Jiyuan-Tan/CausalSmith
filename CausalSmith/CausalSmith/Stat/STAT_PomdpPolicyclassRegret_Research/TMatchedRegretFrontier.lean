module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.TObservableSelectorUpper
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.TCommonKernelLower

/-! # Matched finite-list regret frontier -/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open CausalSmith.Stat.PomdpLatentOverlapMinimax

-- @node: thm:matched-regret-frontier
/-- For [the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the mixing scale assumption](hyp:ht0), and
[the policy-overlap scale assumption](hyp:hzeta), this establishes
[the matched regret frontier result](goal). -/
theorem matched_regret_frontier (t0 zeta : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) :
    ∃ (c K : ℝ) (T0 : Nat), 0 < c ∧ c ≤ K ∧
      ∀ (T M : Nat) (C : ℝ), (hT : max 1 T0 ≤ T) → (hM : 2 ≤ M) → (hC : 1 ≤ C) →
        c * (regretFrontier T M t0 zeta C ht0 hzeta hC (by omega) hM) ≤
          minimaxRegret T M t0 zeta C ∧
        minimaxRegret T M t0 zeta C ≤
          K * (regretFrontier T M t0 zeta C ht0 hzeta hC (by omega) hM) := by
  obtain ⟨Ku, Tu, hKu, hu⟩ := observable_selector_upper t0 zeta ht0 hzeta
  obtain ⟨cl, Tl, hcl, hl⟩ := common_kernel_lower t0 zeta ht0 hzeta
  refine ⟨cl, max Ku cl, max Tu Tl, hcl, le_max_right _ _, ?_⟩
  intro T M C hT hM hC
  have hrate : 0 ≤ (regretFrontier T M t0 zeta C ht0 hzeta hC (by omega) hM) := by
    unfold regretFrontier
    have hq : 0 ≤ overlapRadius C := by
      unfold overlapRadius
      apply div_nonneg
      · linarith
      · linarith
    have hu : 0 ≤ Real.log (M : ℝ) / T := by
      apply div_nonneg
      · apply Real.log_nonneg
        exact_mod_cast (show 1 ≤ M by omega)
      · positivity
    exact le_min (by norm_num)
      (add_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (Real.rpow_nonneg hq _)
          (Real.rpow_nonneg hu _)))
  have hnonneg : ∀ (sel : ObservableSelector T M)
      (m : {m : ModelIndex T M // PolicyListClass t0 zeta C m}),
      0 ≤ expectedRegret sel m.1 := by
    intro sel m
    unfold expectedRegret
    apply MeasureTheory.integral_nonneg
    intro w
    unfold simpleRegret
    exact sub_nonneg.mpr (le_ciSup (Finite.bddAbove_range _) _)
  constructor
  · exact hl T M C (by omega) hM hC
  · calc
      minimaxRegret T M t0 zeta C ≤
          Causalean.Stat.worstCaseRiskReal
            (fun (sel : ObservableSelector T M)
              (m : {m : ModelIndex T M // PolicyListClass t0 zeta C m}) ↦
              expectedRegret sel m.1)
            (blockSelector T M (by omega) t0 zeta C) := by
              exact Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg hnonneg _
      _ ≤ Ku * (regretFrontier T M t0 zeta C ht0 hzeta hC (by omega) hM) :=
        hu T M C (by omega) hM hC
      _ ≤ max Ku cl * (regretFrontier T M t0 zeta C ht0 hzeta hC (by omega) hM) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hrate

end CausalSmith.Stat.PomdpPolicyclassRegret

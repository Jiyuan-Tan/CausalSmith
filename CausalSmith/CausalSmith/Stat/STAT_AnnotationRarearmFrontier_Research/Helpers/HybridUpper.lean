module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.FinitePrefixTransfer
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.HybridArmRisk
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.HybridFiniteEncoding
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.HybridFiniteRate
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.HybridFiniteTransfer
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.HybridPoolLaw
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.HybridPrefixContrast
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.HybridPrefixRisk
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.HybridTunedRisk
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.LabelFloorPair

/-!
Gate-free original-record upper bound and range for the finite hybrid rule.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory

/--
[The finite hybrid rule is measurable, clipped, and uniformly attains the frontier upper
order](goal).
-/
-- @node: hybrid_upper
lemma hybrid_upper :
    ∃ C : Real, 0 < C ∧ ∀ (n m d : Nat) (eps : Real),
      1 ≤ n → 2 ≤ d → 0 < eps → eps ≤ 1 / 4 →
      Measurable (hybridEstimator n m d eps) ∧
      (∀ s, hybridEstimator n m d eps s ∈ Set.Icc (-1) 1) ∧
      worstRisk (liftRule (hybridEstimator n m d eps)) eps ≤ C * frontierRate n m d eps := by
  obtain ⟨C, hC, hlarge⟩ := hybrid_large_information_risk
  let D := max (max C 4) (Real.exp 4096)
  refine ⟨D, lt_of_lt_of_le hC
    ((le_max_left C 4).trans (le_max_left _ _)), ?_⟩
  intro n m d eps hn hd heps heps4
  refine ⟨hybridEstimator_measurable n m d eps,
    hybridEstimator_mem_Icc n m d eps, ?_⟩
  have hrate := (frontierRate_pos n m d eps hn heps).le
  let P0 : ClassLaw d eps :=
    ⟨labelFloorLaw d eps (1 / 8) false hd labelFloorAmplitude_eighth,
      labelFloor_model d eps (1 / 8) false hd labelFloorAmplitude_eighth heps heps4⟩
  letI : Nonempty (ClassLaw d eps) := ⟨P0⟩
  unfold worstRisk
  apply ciSup_le
  intro P
  by_cases hsmall : (n : Real) * eps < Real.exp 4096
  · calc
      ruleRisk (liftRule (hybridEstimator n m d eps)) P.1 ≤ 1 :=
        hybrid_small_information_risk n m d eps P.1 hsmall
      _ ≤ Real.exp 4096 * frontierRate n m d eps :=
        hybrid_small_information_rate n m d eps hn heps hsmall
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hrate
  · have hS := le_of_not_gt hsmall
    by_cases hcap : 1 ≤ 1 / ((n : Real) * eps) +
        ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2
    · rw [frontierRate, labelScale, min_eq_left hcap, mul_one]
      exact (hybrid_risk_le_four n m d eps P.1).trans
        ((le_max_right C 4).trans (le_max_left _ _))
    · rw [frontierRate, labelScale, min_eq_right (le_of_not_ge hcap)]
      exact (hlarge n m d eps P.1 hn hd heps heps4 hS P.2).trans
        (mul_le_mul_of_nonneg_right
          ((le_max_left C 4).trans (le_max_left _ _)) (by positivity))

end CausalSmith.Stat.AnnotationRarearmFrontier

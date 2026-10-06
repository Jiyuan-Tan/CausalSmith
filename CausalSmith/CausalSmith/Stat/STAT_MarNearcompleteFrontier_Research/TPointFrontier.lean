module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.TUpperRisk
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.TPriorReduction

/-!
# Exact all-procedure point-risk frontier
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory

-- @node: thm:point-frontier
/-- Universal constants sandwich the finite-sample minimax MSE at the stated rate. [the stated mathematical conclusion holds](goal). -/
theorem point_frontier :
    ∃ c C : ℝ, 0 < c ∧ c < C ∧
      ∀ (n d : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ d →
        -- @realizes n(sample size in Nat≥1)
        -- @realizes d(baseline alphabet bound in Nat≥1)
        q ∈ Set.Icc ((1 : ℝ) / 2) 1 →
        -- @realizes q(known arrival floor in [1/2,1])
        c * rate n d q ≤ pointMinimaxRisk n d q ∧
        pointMinimaxRisk n d q ≤ C * rate n d q := by
  obtain ⟨cPoint, c0, hcPoint, hc0, hprior⟩ := prior_reduction
  obtain ⟨CU, hCU⟩ := upper_risk
  let c := min cPoint (CU / 2)
  refine ⟨c, CU, ?_, ?_, ?_⟩
  · exact lt_min hcPoint (by linarith [hCU.1])
  · exact lt_of_le_of_lt (min_le_right _ _) (by linarith [hCU.1])
  intro n d q hn hd hq
  constructor
  · obtain ⟨cInterval, c0α, hcInterval, hc0α, hbounds⟩ :=
      hprior (1 / 4) (by constructor <;> norm_num)
    exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by
      unfold rate
      positivity)) (hbounds n d q hn hd hq).2.2.2.1
  · let T : Estimator n d :=
      ⟨tauhatMM n d q, measurable_tauhatMM n d q, tauhatMM_range n d q⟩
    letI : Nonempty (ClassLaw d q) :=
      ⟨pairedClassLaw n d q 0 hn hd hq (by norm_num : (0 : ℝ) ∈ Set.Icc (-1) 1)
        ⟨fun _ => Sum.inr (), fun _ => false⟩⟩
    calc
      pointMinimaxRisk n d q ≤ ⨆ P : ClassLaw d q,
          ∫ o, (T o - tau P.val) ^ 2 ∂ samplePi P.val n := by
        unfold pointMinimaxRisk
        exact ciInf_le (by
          refine ⟨0, ?_⟩
          rintro y ⟨T', rfl⟩
          by_cases hb : BddAbove (Set.range fun P : ClassLaw d q =>
              ∫ o, (T' o - tau P.val) ^ 2 ∂ samplePi P.val n)
          · let P0 : ClassLaw d q := pairedClassLaw n d q 0 hn hd hq (by norm_num : (0 : ℝ) ∈ Set.Icc (-1) 1)
                ⟨fun _ => Sum.inr (), fun _ => false⟩
            exact le_ciSup_of_le hb P0 (integral_nonneg (fun _ => sq_nonneg _))
          · change 0 ≤ ⨆ P : ClassLaw d q,
                ∫ o, (T' o - tau P.val) ^ 2 ∂ samplePi P.val n
            rw [ciSup_of_not_bddAbove hb]
            simp) T
      _ ≤ CU * rate n d q := by
        apply ciSup_le
        intro P
        exact hCU.2 n d q hn hd hq P _ rfl

end CausalSmith.Stat.MarNearcompleteFrontier

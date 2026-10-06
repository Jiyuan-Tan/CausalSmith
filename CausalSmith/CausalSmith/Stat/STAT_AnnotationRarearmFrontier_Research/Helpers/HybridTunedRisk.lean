module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.HybridFiniteRate
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.HybridPrefixContrast

/-!
Risk bounds for the exact public hybrid tuning, including the logarithmic conversion and
the three finite-pool overflow costs.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Under the stated inputs and conditions, The prescribed intensities and bandwidth realize the ordered-prefix contrast bound.  This gives [the stated result](goal). -/
-- @node: hybrid_tuned_prefix_risk
lemma hybrid_tuned_prefix_risk :
    ∃ C : Real, 0 < C ∧ ∀ (n m d : Nat) (eps : Real) (P : DiscreteLaw d),
      1 ≤ n → 2 ≤ d → 0 < eps → eps ≤ 1 / 4 →
      Real.exp 4096 ≤ (n : Real) * eps → ModelClass d eps P →
      Causalean.Stat.sqRisk
        (hybridPoissonPrefixLaw P
          ((hybridTuning n m eps).h0 / 8 : NNReal)
          ((hybridTuning n m eps).Mp / 8 : NNReal)
          ((hybridTuning n m eps).Mf / 8 : NNReal))
        (hybridOrderedPrefixStatistic (hybridTuning n m eps)) (ateFunctional P) ≤
        C * (1 / ((n : Real) * eps) +
          ((d : Real) / (((n : Real) + m) * eps * (hybridTuning n m eps).L)) ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := hybrid_ordered_prefix_contrast_risk
  refine ⟨C, hC, ?_⟩
  intro n m d eps P hn hd heps heps4 hS hP
  obtain ⟨hu, hp, ht, _, hlo, hhi⟩ := hybrid_finite_pool_intensities n m eps
    (hybrid_large_sample_size n eps heps4 hS)
  have hb := hbound n m d eps P
    ((hybridTuning n m eps).h0 / 8 : NNReal)
    ((hybridTuning n m eps).Mp / 8 : NNReal)
    ((hybridTuning n m eps).Mf / 8 : NNReal) hn hd heps heps4 hS hP
  simp only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_ofNat] at hb
  have hb' := hb hu hp ht hlo hhi
  change Causalean.Stat.sqRisk _
    (fun s => hybridOrderedPrefixStatistic (hybridTuning n m eps) s) _ ≤ _
  simp_rw [hybrid_ordered_statistic_eq_contrast]
  simpa only [hybridTuning,
    NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_ofNat] using hb'

/-- Under the stated inputs and conditions, The ideal contrast risk and all three overflow costs have the uncapped frontier order.  This gives [the stated result](goal). -/
-- @node: hybrid_tuned_prefix_and_overflow_rate
lemma hybrid_tuned_prefix_and_overflow_rate :
    ∃ C : Real, 0 < C ∧ ∀ (n m d : Nat) (eps : Real) (P : DiscreteLaw d),
      1 ≤ n → 2 ≤ d → 0 < eps → eps ≤ 1 / 4 →
      Real.exp 4096 ≤ (n : Real) * eps → ModelClass d eps P →
      Causalean.Stat.sqRisk
        (hybridPoissonPrefixLaw P
          ((hybridTuning n m eps).h0 / 8 : NNReal)
          ((hybridTuning n m eps).Mp / 8 : NNReal)
          ((hybridTuning n m eps).Mf / 8 : NNReal))
        (hybridOrderedPrefixStatistic (hybridTuning n m eps)) (ateFunctional P) +
        (Real.exp (-((hybridTuning n m eps).h0 : Real)) +
          Real.exp (-((hybridTuning n m eps).Mp : Real)) +
          Real.exp (-((hybridTuning n m eps).Mf : Real))) ≤
        C * (1 / ((n : Real) * eps) +
          ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := hybrid_tuned_prefix_risk
  refine ⟨C * (1281 : Real) ^ 2 + 5, by positivity, ?_⟩
  intro n m d eps P hn hd heps heps4 hS hP
  have hrisk := hbound n m d eps P hn hd heps heps4 hS hP
  have hdegree := mul_le_mul_of_nonneg_left
    (hybrid_finite_degree_rate n m d eps heps hS) hC.le
  have hoverflow := hybrid_finite_overflow_rate n m eps
    (hybrid_large_sample_size n eps heps4 hS) heps heps4
  have hsquare := sq_nonneg
    ((d : Real) / (((n : Real) + m) * eps * logScale n eps))
  calc
    _ ≤ C * (1281 ^ 2 * (1 / ((n : Real) * eps) +
        ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2)) +
        5 / ((n : Real) * eps) := add_le_add (hrisk.trans hdegree) hoverflow
    _ = (C * 1281 ^ 2 + 5) * (1 / ((n : Real) * eps) +
        ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2) -
        5 * ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2 := by ring
    _ ≤ _ := sub_le_self _ (mul_nonneg (by norm_num) hsquare)

/-- [Under the stated inputs and conditions](hyp:eps,P,n,m,d), The clipped finite hybrid estimator has squared risk at most four for every law.  This gives [the stated result](goal).-/
-- @node: hybrid_risk_le_four
lemma hybrid_risk_le_four (n m d : Nat) (eps : Real) (P : DiscreteLaw d) :
    ruleRisk (liftRule (hybridEstimator n m d eps)) P ≤ 4 := by
  let : IsProbabilityMeasure (annotationLaw P n m) := by
    unfold annotationLaw labeledProductLaw auxProductLaw
    infer_instance
  have ht := ateFunctional_mem_Icc P
  rw [hybrid_ruleRisk_eq_sqRisk]
  unfold Causalean.Stat.sqRisk
  calc
    _ ≤ ∫ _s : Sample n m d, (4 : Real) ∂annotationLaw P n m := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) (integrable_const 4)
      apply Filter.Eventually.of_forall
      intro s
      have hs := hybridEstimator_mem_Icc n m d eps s
      nlinarith [hs.1, hs.2, ht.1, ht.2]
    _ = 4 := by simp

end CausalSmith.Stat.AnnotationRarearmFrontier

module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Baseline
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.BaselinePoissonRisk
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.BaselinePoolEncoding
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.BaselinePoolLaw
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.BaselinePoolStatistic
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.BaselinePrefixCounts
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.FinitePrefixTransfer
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.InverseCountArmRisk

/-!
Uniform original-record inverse-count baseline theorem.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


/-- [Under the stated inputs and conditions](hyp:P,hsmall,n,m,d), The prescribed zero branch has squared risk at most one.  This gives [the stated result](goal).-/
-- @node: baseline_small_sample_risk
lemma baseline_small_sample_risk (n m d : Nat) (P : DiscreteLaw d)
    (hsmall : n < 6) :
    ruleRisk (liftRule (baselineEstimator n m d)) P ≤ 1 := by
  let : IsProbabilityMeasure (obsLaw P) := by
    unfold obsLaw
    infer_instance
  let : IsProbabilityMeasure seedLaw := ⟨by
    norm_num [seedLaw, Real.volume_Icc]⟩
  let : IsProbabilityMeasure (annotationLaw P n m) := by
    unfold annotationLaw labeledProductLaw auxProductLaw
    infer_instance
  have ht := ateFunctional_mem_Icc P
  have hrisk : ruleRisk (liftRule (baselineEstimator n m d)) P =
      (ateFunctional P) ^ 2 := by
    simp [ruleRisk, liftRule, baselineEstimator, hsmall, integral_const,
      Measure.real_def]
  rw [hrisk]
  nlinarith [ht.1, ht.2]

/-- [Under the stated inputs and conditions](hyp:P,n,m,d), Clipping both the baseline and the target bounds squared loss by four.  This gives [the stated result](goal).-/
-- @node: baseline_risk_le_four
lemma baseline_risk_le_four (n m d : Nat) (P : DiscreteLaw d) :
    ruleRisk (liftRule (baselineEstimator n m d)) P ≤ 4 := by
  let : IsProbabilityMeasure (obsLaw P) := by
    unfold obsLaw
    infer_instance
  let : IsProbabilityMeasure seedLaw := ⟨by
    norm_num [seedLaw, Real.volume_Icc]⟩
  let : IsProbabilityMeasure (annotationLaw P n m) := by
    unfold annotationLaw labeledProductLaw auxProductLaw
    infer_instance
  have ht := ateFunctional_mem_Icc P
  have hpoint (z : Sample n m d × Real) :
      (liftRule (baselineEstimator n m d) z - ateFunctional P) ^ 2 ≤ 4 := by
    have hb := baselineEstimator_mem_Icc n m d z.1
    dsimp [liftRule]
    nlinarith [hb.1, hb.2, ht.1, ht.2]
  unfold ruleRisk
  calc
    _ ≤ ∫ _z : Sample n m d × Real, (4 : Real)
        ∂((annotationLaw P n m).prod seedLaw) :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        (integrable_const 4) (Filter.Eventually.of_forall hpoint)
    _ = 4 := by simp

/-- [Under the stated inputs and conditions](hyp:eps,hn,hsmall,heps,heps',n,d,m), For fewer than six labeled records, the capped baseline rate is at least four fifths.  This gives [the stated result](goal).-/
-- @node: baseline_small_sample_rate
lemma baseline_small_sample_rate (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hsmall : n < 6) (heps : 0 < eps) (heps' : eps ≤ 1 / 4) :
    (4 / 5 : Real) ≤
      min 1 (1 / ((n : Real) * eps) + ((d : Real) / (((n : Real) + m) * eps)) ^ 2) := by
  have hn0 : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hn5 : (n : Real) ≤ 5 := by exact_mod_cast (show n ≤ 5 by omega)
  have hS : 0 < (n : Real) * eps := mul_pos hn0 heps
  have hSupper : (n : Real) * eps ≤ 5 / 4 := by nlinarith
  have hinv : (4 / 5 : Real) ≤ 1 / ((n : Real) * eps) := by
    apply (le_div_iff₀ hS).2
    nlinarith
  exact le_min (by norm_num) (hinv.trans (le_add_of_nonneg_right (sq_nonneg _)))

-- @node: thm:uniform-baseline
/-- Under the stated inputs and conditions, The total inverse-count baseline has a universal overlap-explicit risk guarantee. This gives [the stated conclusion](goal). -/
theorem uniform_baseline :
    ∃ C : Real, 0 < C ∧ -- @realizes C(positive universal bound constant)
      ∀ (n m d : Nat) (eps : Real), 1 ≤ n → 2 ≤ d → 0 < eps → eps ≤ 1 / 4 →
        Measurable (baselineEstimator n m d) ∧
        (∀ s, baselineEstimator n m d s ∈ Set.Icc (-1) 1) ∧
        ∀ P : ClassLaw d eps, ruleRisk (liftRule (baselineEstimator n m d)) P.1 ≤
          C * min 1 (1 / ((n : Real) * eps) + ((d : Real) / (((n : Real) + m) * eps)) ^ 2) :=
  by
    have hlarge : ∃ C : Real, 0 < C ∧
        ∀ (n m d : Nat) (eps : Real), 6 ≤ n → 2 ≤ d → 0 < eps → eps ≤ 1 / 4 →
          ∀ P : ClassLaw d eps, ruleRisk (liftRule (baselineEstimator n m d)) P.1 ≤
            C * (1 / ((n : Real) * eps) +
              ((d : Real) / (((n : Real) + m) * eps)) ^ 2) := by
      obtain ⟨C, hC, hpoisson⟩ := baseline_ordered_prefix_risk
      refine ⟨4 * (40 * C + 1026), by positivity, ?_⟩
      intro n m d eps hn hd heps heps' P
      have hpool : ruleRisk (liftRule (baselineEstimator n m d)) P.1 ≤
          C * (1 / (((n / 2 : Nat) : Real) / 8 * eps) +
            1 / (((n - n / 2 + m : Nat) : Real) / 8 * eps)) +
          4 * ((d : Real) /
            (Real.exp 1 * ((n - n / 2 + m : Nat) : Real) / 8 * eps)) ^ 2 +
          4 * (Real.exp (-(n / 2 : Nat)) + Real.exp (-(n - n / 2 + m : Nat))) := by
        rw [baseline_ruleRisk_eq_fixed_average P.1 hn]
        have hu : (0 : NNReal) < (n / 2 : Nat) / 8 := by
          have hh : 0 < n / 2 := by omega
          positivity
        have ht : (0 : NNReal) < (n - n / 2 + m : Nat) / 8 := by
          have hg : 0 < n - n / 2 + m := by omega
          positivity
        have htransfer := sqRisk_independentPrefixRaoBlackwellStatistic_le
          (obsLaw P.1) (auxMarginal P.1).toMeasure
          ((n / 2 : Nat) / 8 : NNReal) ((n - n / 2 + m : Nat) / 8 : NNReal)
          (n / 2) (n - n / 2 + m)
          (baselineOrderedPrefixStatistic_measurable d ((n / 2 : Nat) / 8 : NNReal))
          (by norm_num : (-1 : Real) ≤ 1)
          (baselineOrderedPrefixStatistic_mem_Icc ((n / 2 : Nat) / 8 : NNReal))
          (ateFunctional_mem_Icc P.1)
          (by norm_num : (0 : Real) ∈ Set.Icc (-1) 1)
        have hprefix := hpoisson d eps P.1 _ _ hd heps heps' P.2 hu ht
        have htail := add_le_add (eighth_pool_poisson_overflow (n / 2))
          (eighth_pool_poisson_overflow (n - n / 2 + m))
        norm_num only at htransfer
        simpa only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_ofNat, mul_div_assoc] using
          htransfer.trans (add_le_add hprefix
          (mul_le_mul_of_nonneg_left htail (by norm_num)))
      have hrate := baseline_pool_rate_bound n m d eps C hn heps heps' hC
      have hnonneg : 0 ≤ C * (1 / (((n / 2 : Nat) : Real) / 8 * eps) +
          1 / (((n - n / 2 + m : Nat) : Real) / 8 * eps)) +
          4 * ((d : Real) /
            (Real.exp 1 * ((n - n / 2 + m : Nat) : Real) / 8 * eps)) ^ 2 := by
        positivity
      nlinarith
    obtain ⟨C, hC, hbound⟩ := hlarge
    refine ⟨max C 4, lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
    intro n m d eps hn hd heps heps'
    refine ⟨baselineEstimator_measurable n m d, baselineEstimator_mem_Icc n m d, ?_⟩
    intro P
    have hrate : 0 ≤ min 1 (1 / ((n : Real) * eps) +
        ((d : Real) / (((n : Real) + m) * eps)) ^ 2) := by positivity
    by_cases hsmall : n < 6
    · have hlow := baseline_small_sample_rate n m d eps hn hsmall heps heps'
      calc
        ruleRisk (liftRule (baselineEstimator n m d)) P.1 ≤ 1 :=
          baseline_small_sample_risk n m d P.1 hsmall
        _ ≤ 2 * min 1 (1 / ((n : Real) * eps) +
            ((d : Real) / (((n : Real) + m) * eps)) ^ 2) := by linarith
        _ ≤ _ := mul_le_mul_of_nonneg_right
          ((by norm_num : (2 : Real) ≤ 4).trans (le_max_right _ _)) hrate
    · by_cases hcap : 1 ≤ 1 / ((n : Real) * eps) +
          ((d : Real) / (((n : Real) + m) * eps)) ^ 2
      · rw [min_eq_left hcap, mul_one]
        exact (baseline_risk_le_four n m d P.1).trans (le_max_right _ _)
      · rw [min_eq_right (le_of_not_ge hcap)]
        exact (hbound n m d eps (by omega) hd heps heps' P).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

end CausalSmith.Stat.AnnotationRarearmFrontier

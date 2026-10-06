module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.BaselinePoolLaw
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.Risk

/-!
Deterministic identification of the array baseline with the fixed-pool prefix rule.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix

/-- [Under the stated hypotheses](hyp:hr), Prefixing an appended array retains the first block followed by the required
part of the second block, also when the prefix stops inside the first block.  This gives [the stated result](goal). -/
-- @node: baseline_prefix_append_eq
lemma baseline_prefix_append_eq {X : Type*} [MeasurableSpace X] {h m : Nat}
    (s : Fin h → X) (v : Fin m → X) (r : Nat) (hr : r ≤ h + m) :
    prefixOfLE (Fin.append s v) r hr =
      ⟨min r h + (r - h), Fin.append
        (fun i : Fin (min r h) => s ⟨i.val, by omega⟩)
        (fun i : Fin (r - h) => v ⟨i.val, by omega⟩)⟩ := by
  have hc : r = min r h + (r - h) := by omega
  apply Sigma.ext hc
  apply (Fin.heq_fun_iff hc).2
  intro i
  simp only [prefixOfLE]
  by_cases hi : i.val < min r h
  · have hi' : i.val < h := by omega
    simp [Fin.append, Fin.addCases, hi, hi']
  · have hi' : ¬ i.val < h := by omega
    have hmin : min r h = h := by omega
    simp [Fin.append, Fin.addCases, hi', hmin]

/-- [Under the stated inputs and conditions](hyp:s,r,hr,n,m,d), The complete prefix of the extracted pool is the first original-array block.  This gives [the stated result](goal).-/
-- @node: baseline_fixed_complete_prefix_eq
lemma baseline_fixed_complete_prefix_eq {n m d : Nat} (s : Sample n m d)
    (r : Nat) (hr : r ≤ n / 2) :
    prefixOfLE (baselineFixedPools s).1 r hr =
      baselineBlockPrefix s.1 0 r (by omega) := by
  simp [prefixOfLE, baselineFixedPools, baselineBlockPrefix]

/-- [Under the stated inputs and conditions](hyp:s,v,hv,n,m,d), The marginal prefix of the extracted pool is the prescribed projected block
concatenated with the prescribed auxiliary block.  This gives [the stated result](goal).-/
-- @node: baseline_fixed_auxiliary_prefix_eq
lemma baseline_fixed_auxiliary_prefix_eq {n m d : Nat} (s : Sample n m d)
    (v : Nat) (hv : v ≤ n - n / 2 + m) :
    prefixOfLE (baselineFixedPools s).2 v hv =
      baselineAuxiliaryPrefix s (n / 2) (n - n / 2) 0 v (by omega) (by omega) := by
  simpa [baselineFixedPools, baselineAuxiliaryPrefix, baselineBlockPrefix,
    FiniteSample.points, FiniteSample.count] using
    baseline_prefix_append_eq
      (fun i : Fin (n - n / 2) =>
        ((s.1 ⟨n / 2 + i.val, by omega⟩).1,
          (s.1 ⟨n / 2 + i.val, by omega⟩).2.1)) s.2 v hv

/-- [Under the stated inputs and conditions](hyp:s,hr,hv,n,m,d,r,v), Every valid original-array prefix computes the fixed-pool statistic exactly.  This gives [the stated result](goal).-/
-- @node: baseline_fixed_prefix_statistic_eq
lemma baseline_fixed_prefix_statistic_eq {n m d : Nat} (s : Sample n m d)
    (r v : Nat) (hr : r ≤ n / 2) (hv : v ≤ n - n / 2 + m) :
    baselinePrefixStatistic r v s =
      baselineOrderedPrefixStatistic ((n / 2 : Nat) / 8 : NNReal)
        (prefixOfLE (baselineFixedPools s).1 r hr,
          prefixOfLE (baselineFixedPools s).2 v hv) := by
  rw [baseline_fixed_complete_prefix_eq, baseline_fixed_auxiliary_prefix_eq]
  exact baseline_prefix_statistic_eq_ordered s r v (by omega) (by omega) (by omega)

/-- [Under the stated inputs and conditions](hyp:s,k,n,m,d), Overflow is zero in both implementations, and valid prefixes agree exactly.  This gives [the stated result](goal).-/
-- @node: baseline_capped_array_eq_fixed
lemma baseline_capped_array_eq_fixed {n m d : Nat} (s : Sample n m d) (k : Nat × Nat) :
    baselineCappedArrayStatistic s k =
      cappedPrefixStatistic (baselineOrderedPrefixStatistic ((n / 2 : Nat) / 8 : NNReal))
        0 (((baselineFixedPools s).1, k.1), ((baselineFixedPools s).2, k.2)) := by
  by_cases hr : k.1 ≤ n / 2
  · by_cases hv : k.2 ≤ n - n / 2 + m
    · simp only [baselineCappedArrayStatistic, hr, hv, and_self, ite_true,
        cappedPrefixStatistic, dif_pos]
      exact baseline_fixed_prefix_statistic_eq s k.1 k.2 hr hv
    · simp [baselineCappedArrayStatistic, cappedPrefixStatistic, hr, hv]
  · simp [baselineCappedArrayStatistic, cappedPrefixStatistic, hr]

/-- [Under the stated inputs and conditions](hyp:s,hn,n,m,d), The deterministic baseline is exactly the prefix average of its extracted pools.  This gives [the stated result](goal).-/
-- @node: baseline_estimator_eq_fixed_average
lemma baseline_estimator_eq_fixed_average {n m d : Nat} (s : Sample n m d)
    (hn : 6 ≤ n) :
    baselineEstimator n m d s =
      independentPrefixRaoBlackwellStatistic ((n / 2 : Nat) / 8 : NNReal)
        ((n - n / 2 + m : Nat) / 8 : NNReal)
        (baselineOrderedPrefixStatistic ((n / 2 : Nat) / 8 : NNReal)) 0
        (baselineFixedPools s) := by
  rw [independentPrefixRaoBlackwellStatistic_eq_integral _ _ _
    (baselineOrderedPrefixStatistic_measurable d _) 0,
    baseline_estimator_eq_poisson_integral s hn]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun k => baseline_capped_array_eq_fixed s k)

/-- [Under the stated inputs and conditions](hyp:P,hn,n,m,d), The original rule risk equals the independent fixed-pool prefix-average risk.  This gives [the stated result](goal).-/
-- @node: baseline_ruleRisk_eq_fixed_average
lemma baseline_ruleRisk_eq_fixed_average {n m d : Nat} (P : DiscreteLaw d)
    (hn : 6 ≤ n) :
    ruleRisk (liftRule (baselineEstimator n m d)) P =
      Causalean.Stat.sqRisk
        (fixedPoolsLaw (obsLaw P) (auxMarginal P).toMeasure
          (n / 2) (n - n / 2 + m))
        (independentPrefixRaoBlackwellStatistic ((n / 2 : Nat) / 8 : NNReal)
          ((n - n / 2 + m : Nat) / 8 : NNReal)
          (baselineOrderedPrefixStatistic ((n / 2 : Nat) / 8 : NNReal)) 0)
        (ateFunctional P) := by
  rw [baseline_ruleRisk_eq_sqRisk]
  have heq : baselineEstimator n m d =
      (independentPrefixRaoBlackwellStatistic ((n / 2 : Nat) / 8 : NNReal)
        ((n - n / 2 + m : Nat) / 8 : NNReal)
        (baselineOrderedPrefixStatistic ((n / 2 : Nat) / 8 : NNReal)) 0) ∘
          baselineFixedPools := by
    funext s
    exact baseline_estimator_eq_fixed_average s hn
  rw [heq, baseline_fixed_pools_sqRisk P _ (by fun_prop)]
  rfl

end CausalSmith.Stat.AnnotationRarearmFrontier

module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.T_KnownMarginalBoundary
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.T_KnownMarginalLimit
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.T_UniformMixedUpper
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.T_CommonMarginalConverse
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.StrictImprovement
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Analysis.Asymptotics.Defs

/-! Sharp finite-sample and asymptotic annotation-frontier consequences. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open Filter Topology Asymptotics

/-- The complete finite-sample bracket, known-marginal limit, and three sequence
characterizations asserted by the headline theorem.  [the stated conditions](hyp:eps,c,C) [the stated conclusion](goal). -/
def AnnotationFrontierConsequences (eps c C : Real) : Prop :=
  (∀ (n m d : Nat), 1 ≤ n → 2 ≤ d →
    c * frontierRate n m d ≤ minimaxRisk n m d eps ∧
      minimaxRisk n m d eps ≤ C * frontierRate n m d) ∧
  (∀ (n d : Nat), 1 ≤ n →
    frontierRate n 0 d = min 1
      (1 / (n : Real) + (d : Real) ^ 2 / ((n : Real) ^ 2 * logEN n ^ 2))) ∧
  (∀ (n d : Nat), 1 ≤ n → 2 ≤ d →
    Tendsto (fun m => minimaxRisk n m d eps) atTop
      (nhds (knownMarginalRisk n d eps))) ∧
  ∀ (mSeq dSeq : Nat → Nat),
    -- @realizes (m_n)_{n\ge1}(arbitrary Nat-valued auxiliary-size sequence)
    -- @realizes (d_n)_{n\ge1}(arbitrary Nat-valued alphabet-size sequence)
    (∀ n, 1 ≤ n → 2 ≤ dSeq n) →
    (Tendsto (fun n => minimaxRisk n (mSeq n) (dSeq n) eps) atTop (nhds 0) ↔
      Tendsto (fun n => (dSeq n : Real) /
        (((n + mSeq n : Nat) : Real) * logEN n)) atTop (nhds 0)) ∧
    ((fun n => minimaxRisk n (mSeq n) (dSeq n) eps) =O[atTop]
        (fun n => 1 / (n : Real)) ↔
      (fun n => (dSeq n : Real)) =O[atTop]
        (fun n => ((n + mSeq n : Nat) : Real) * logEN n / Real.sqrt n)) ∧
    ((fun n => minimaxRisk n (mSeq n) (dSeq n) eps) =o[atTop]
        (fun n => minimaxRisk n 0 (dSeq n) eps) ↔
      Tendsto (fun n => (dSeq n : Real) / (Real.sqrt n * logEN n)) atTop atTop ∧
      Tendsto (fun n =>
        ((dSeq n : Real) / (((n + mSeq n : Nat) : Real) * logEN n)) /
          min 1 ((dSeq n : Real) / ((n : Real) * logEN n))) atTop (nhds 0))

-- @node: thm:sharp-annotation-frontier
/-- The minimax risk has the sharp annotation-frontier rate and exactly the stated
known-marginal and sequence-regime consequences.  [the stated conditions](hyp:heps,heps2) [the stated conclusion](goal). -/
theorem sharp_annotation_frontier {eps : Real}
    (heps : 0 < eps) (heps2 : eps < 1 / 2) :
    ∃ c C : Real,
      0 < c ∧ -- @realizes c_\epsilon(positive two-sided lower constant depending only on epsilon)
      c ≤ C ∧ -- @realizes C_\epsilon(finite two-sided upper constant depending only on epsilon)
      AnnotationFrontierConsequences eps c C := by
  obtain ⟨c, hc, calibration, hlower⟩ := common_marginal_converse heps heps2
  obtain ⟨C₀, hC₀, hupper⟩ := uniform_mixed_upper heps heps2
  let C := max c C₀
  have hC : 0 < C := hc.trans_le (le_max_left _ _)
  refine ⟨c, C, hc, le_max_left _ _, ?_, ?_, ?_, ?_⟩
  · intro n m d hn hd
    constructor
    · exact (hlower n m d hn hd).choose_spec.2
    · calc
        minimaxRisk n m d eps ≤
            ⨆ P : ClassLaw d eps,
              twoSampleMSE (annotationLaw P.1 n m) (mixedEstimator n m d eps)
                (ateFunctional P.1) :=
          minimaxRisk_le_measurable_estimator _ (measurable_mixedEstimator n m d eps)
        _ ≤ C₀ * frontierRate n m d := hupper n m d hn hd
        _ ≤ C * frontierRate n m d := by
          exact mul_le_mul_of_nonneg_right (le_max_right c C₀)
            (frontierRate_mem_Ioc_zero_one n m d hn).1.le
  · intro n d hn
    rw [frontierRate]
    norm_num
  · intro n d hn hd
    exact known_marginal_limit heps heps2 n d hn hd
  · intro mSeq dSeq hd
    let risk : Nat → Real := fun n ↦ minimaxRisk n (mSeq n) (dSeq n) eps
    let rate : Nat → Real := fun n ↦ frontierRate n (mSeq n) (dSeq n)
    let risk₀ : Nat → Real := fun n ↦ minimaxRisk n 0 (dSeq n) eps
    let rate₀ : Nat → Real := fun n ↦ frontierRate n 0 (dSeq n)
    have htheta : risk =Θ[atTop] rate := by
      apply positive_two_sided_bounds_isTheta risk rate hc hC
      · exact Filter.Eventually.of_forall fun n ↦ (minimaxRisk_mem_Icc_zero_one _ _ _ _).1
      · filter_upwards [eventually_ge_atTop 1] with n hn
        exact (frontierRate_mem_Ioc_zero_one _ _ _ hn).1.le
      · filter_upwards [eventually_ge_atTop 1] with n hn
        exact (hlower n (mSeq n) (dSeq n) hn (hd n hn)).choose_spec.2
      · filter_upwards [eventually_ge_atTop 1] with n hn
        dsimp [risk, rate]
        calc
          minimaxRisk n (mSeq n) (dSeq n) eps ≤
              C₀ * frontierRate n (mSeq n) (dSeq n) := by
            exact (minimaxRisk_le_measurable_estimator _
              (measurable_mixedEstimator n (mSeq n) (dSeq n) eps)).trans
                (hupper n (mSeq n) (dSeq n) hn (hd n hn))
          _ ≤ C * frontierRate n (mSeq n) (dSeq n) := by
            exact mul_le_mul_of_nonneg_right (le_max_right c C₀)
              (frontierRate_mem_Ioc_zero_one n (mSeq n) (dSeq n) hn).1.le
    have htheta₀ : risk₀ =Θ[atTop] rate₀ := by
      apply positive_two_sided_bounds_isTheta risk₀ rate₀ hc hC
      · exact Filter.Eventually.of_forall fun n ↦ (minimaxRisk_mem_Icc_zero_one _ _ _ _).1
      · filter_upwards [eventually_ge_atTop 1] with n hn
        exact (frontierRate_mem_Ioc_zero_one _ _ _ hn).1.le
      · filter_upwards [eventually_ge_atTop 1] with n hn
        exact (hlower n 0 (dSeq n) hn (hd n hn)).choose_spec.2
      · filter_upwards [eventually_ge_atTop 1] with n hn
        dsimp [risk₀, rate₀]
        calc
          minimaxRisk n 0 (dSeq n) eps ≤ C₀ * frontierRate n 0 (dSeq n) := by
            exact (minimaxRisk_le_measurable_estimator _
              (measurable_mixedEstimator n 0 (dSeq n) eps)).trans
                (hupper n 0 (dSeq n) hn (hd n hn))
          _ ≤ C * frontierRate n 0 (dSeq n) := by
            exact mul_le_mul_of_nonneg_right (le_max_right c C₀)
              (frontierRate_mem_Ioc_zero_one n 0 (dSeq n) hn).1.le
    constructor
    · constructor
      · intro hrisk
        apply annotation_frontier_consistency_iff mSeq dSeq hd |>.1
        exact htheta.isBigO_symm.trans_tendsto hrisk
      · intro hrate
        apply htheta.isBigO.trans_tendsto
        exact (annotation_frontier_consistency_iff mSeq dSeq hd).2 hrate
    · constructor
      · exact htheta.isBigO_congr_left.trans
          (annotation_frontier_parametric_iff mSeq dSeq hd)
      · exact htheta.isLittleO_congr_left.trans <|
          htheta₀.isLittleO_congr_right.trans <|
            annotation_frontier_strict_improvement_iff mSeq dSeq hd

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

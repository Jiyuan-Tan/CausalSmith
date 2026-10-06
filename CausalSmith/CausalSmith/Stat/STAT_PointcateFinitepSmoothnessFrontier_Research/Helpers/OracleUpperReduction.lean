module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.LowerIntervalDecision
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.OracleConstruction

/-! Explicit oracle decision witnesses give the four minimax upper comparisons. -/
@[expose] public section
noncomputable section
open MeasureTheory Set
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

/-- A nonnegative real envelope controls the supremum even for an empty model. -/
-- @node: oracle_real_iSup_le
lemma oracle_real_iSup_le {ι : Type*} (f : ι → ℝ) (b : ℝ)
    (hb : 0 ≤ b) (hf : ∀ i, f i ≤ b) : (⨆ i, f i) ≤ b := by
  cases isEmpty_or_nonempty ι with
  | inl hi =>
    letI := hi
    simpa only [iSup, Set.range_eq_empty, Real.sSup_empty] using hb
  | inr hi =>
    letI := hi
    exact ciSup_le hf

/-- A uniformly controlled decision bounds the minimax absolute risk. -/
-- @node: oracle_minimax_upper_of_decision
lemma oracle_minimax_upper_of_decision {S : Type*} [MeasurableSpace S]
    (κ : Params) (n : ℕ) (side : ObservedLaw → S) (t : SideEstimator n S)
    (b : ℝ) (hb : 0 ≤ b)
    (ht : ∀ law, InModel κ law → decisionRisk n jointLaw side t law ≤ b) :
    minimaxRiskWith κ n jointLaw side ≤ b := by
  unfold minimaxRiskWith
  refine ciInf_le_of_le ?_ t ?_
  · refine ⟨0, ?_⟩
    rintro v ⟨t', rfl⟩
    exact Real.iSup_nonneg fun law => integral_nonneg fun z => abs_nonneg _
  · exact oracle_real_iSup_le _ b hb (fun law => ht law.1 law.2)

/-- A uniformly short honest interval bounds the minimax honest length. -/
-- @node: oracle_length_upper_of_decision
lemma oracle_length_upper_of_decision {S : Type*} [MeasurableSpace S]
    (κ : Params) (n : ℕ) (side : ObservedLaw → S) (i : IntervalProc n S)
    (b : ℝ) (hb : 0 ≤ b)
    (hc : ∀ law, InModel κ law → 9/10 ≤ coverage n jointLaw side i law)
    (hl : ∀ law, InModel κ law → expectedLength n jointLaw side i law ≤ b) :
    honestLengthWith κ n jointLaw side ≤ b := by
  unfold honestLengthWith
  refine ciInf_le_of_le ?_ ⟨i, hc⟩ ?_
  · refine ⟨0, ?_⟩
    rintro v ⟨i', rfl⟩
    exact Real.iSup_nonneg fun law => integral_nonneg fun z =>
      (lower_interval_length_properties.2 _).1
  · exact oracle_real_iSup_le _ b hb (fun law => hl law.1 law.2)

/-- A propensity decision can ignore the additionally revealed baseline. -/
-- @node: oracle_lift_estimator
def oracle_lift_estimator (n : ℕ) (t : SideEstimator n Nuisance) :
    SideEstimator n (Nuisance × Nuisance) :=
  ⟨fun z => t.1 (z.1, z.2.1, z.2.2.1),
    t.2.1.comp (by fun_prop), fun z => t.2.2 _⟩

/-- A propensity interval can ignore the additionally revealed baseline. -/
-- @node: oracle_lift_interval
def oracle_lift_interval (n : ℕ) (i : IntervalProc n Nuisance) :
    IntervalProc n (Nuisance × Nuisance) :=
  ⟨fun z => i.1 (z.1, z.2.1, z.2.2.1), i.2.comp (by fun_prop)⟩

/-- A pointwise length envelope bounds expected length under the original experiment. -/
-- @node: oracle_expected_length_upper
lemma oracle_expected_length_upper {S : Type*} [MeasurableSpace S]
    (n : ℕ) (side : ObservedLaw → S) (i : IntervalProc n S) (b : ℝ)
    (hl : ∀ z, (i.1 z).length ≤ b) (law : ObservedLaw) :
    expectedLength n jointLaw side i law ≤ b := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  letI : IsProbabilityMeasure (jointLaw n law.P) := by unfold jointLaw; infer_instance
  unfold expectedLength
  calc
    _ ≤ ∫ _ : Experiment n, b ∂jointLaw n law.P :=
      integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun z => (lower_interval_length_properties.2 _).1)
        (integrable_const b) (Filter.Eventually.of_forall fun z => hl _)
    _ = b := by simp

/-- The two explicit oracle decisions control all four revelation minimax quantities. -/
-- @node: oracle_values_upper_of_procedures
lemma oracle_values_upper_of_procedures (κ : Params) (n : ℕ)
    (expLaw : ExperimentFamily)
    (hr : ∀ law, InModel κ law →
      decisionRisk n jointLaw sideE (oracleDecision κ n) law ≤
        oracleConstant κ*(n : ℝ)^(-rOracle κ))
    (hc : ∀ law, InModel κ law →
      9/10 ≤ coverage n jointLaw sideE (oracleIntervalDecision κ n) law)
    (hl : ∀ z, (oracleInterval κ n z).length ≤
      min 1 (20*oracleConstant κ*(n : ℝ)^(-rOracle κ))) (j : Fin 4) :
    oracleValues κ n expLaw j ≤ oracleUpper κ*(n : ℝ)^(-rOracle κ) := by
  let b := oracleUpper κ*(n : ℝ)^(-rOracle κ)
  have hb : 0 ≤ b := by dsimp [b, oracleUpper, oracleConstant, oracleMoment]; positivity
  have hr' : ∀ law, InModel κ law →
      decisionRisk n jointLaw sideE (oracleDecision κ n) law ≤ b := by
    intro law hm
    apply (hr law hm).trans
    dsimp [b, oracleUpper]
    have hp : 0 ≤ oracleConstant κ*(n : ℝ)^(-rOracle κ) := by
      unfold oracleConstant oracleMoment; positivity
    nlinarith
  have hl' : ∀ z, ((oracleIntervalDecision κ n).1 z).length ≤ b := by
    intro z
    exact (hl z).trans (min_le_right _ _)
  have hE := oracle_minimax_upper_of_decision κ n sideE (oracleDecision κ n) b hb hr'
  have hEM := oracle_minimax_upper_of_decision κ n sideEM
    (oracle_lift_estimator n (oracleDecision κ n)) b hb hr'
  have hL := oracle_length_upper_of_decision κ n sideE
    (oracleIntervalDecision κ n) b hb hc
    (fun law _ => oracle_expected_length_upper n sideE _ b hl' law)
  have hLM := oracle_length_upper_of_decision κ n sideEM
    (oracle_lift_interval n (oracleIntervalDecision κ n)) b hb hc
    (fun law _ => oracle_expected_length_upper n sideEM _ b (fun z => hl' _) law)
  unfold oracleValues
  split
  · exact hE
  · split
    · exact hL
    · split
      · exact hEM
      · exact hLM

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Basic

/-! Finite-moment point-CATE frontier: Helpers/OracleComparison. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier


/-- An original estimator can ignore arbitrary supplied side information. -/
-- @node: lift_original_estimator
def lift_original_estimator {S : Type*} [MeasurableSpace S] (n : ℕ)
    (t : Estimator n) : SideEstimator n S :=
  ⟨fun z => t.1 (z.1, z.2.1, ()), by
    constructor
    · exact t.2.1.comp (measurable_fst.prodMk
        ((measurable_fst.comp measurable_snd).prodMk measurable_const))
    · intro z
      exact t.2.2 _⟩

/-- Ignoring side information leaves every original risk unchanged. -/
-- @node: minimax_ignores_side
lemma minimax_ignores_side {S : Type*} [MeasurableSpace S] (κ : Params) (n : ℕ)
    (side : ObservedLaw → S) :
    minimaxRiskWith κ n jointLaw side ≤ minimaxRisk κ n := by
  letI : Nonempty (SideEstimator n Unit) := ⟨⟨fun _ => 0, measurable_const, by
    intro z
    constructor <;> norm_num⟩⟩
  unfold minimaxRisk minimaxRiskWith
  apply ciInf_mono_of_forall_exists
  · refine ⟨0, ?_⟩
    rintro x ⟨t, rfl⟩
    exact Real.iSup_nonneg fun law => integral_nonneg fun z => abs_nonneg _
  · intro t
    refine ⟨lift_original_estimator n t, ?_⟩
    rfl

/-- An original interval can ignore arbitrary supplied side information. -/
-- @node: lift_original_interval
def lift_original_interval {S : Type*} [MeasurableSpace S] (n : ℕ)
    (i : OriginalIntervalProc n) : IntervalProc n S :=
  ⟨fun z => i.1 (z.1, z.2.1, ()), i.2.comp (measurable_fst.prodMk
    ((measurable_fst.comp measurable_snd).prodMk measurable_const))⟩

/-- Every bounded interval code has nonnegative length. -/
-- @node: intervalCode_length_nonneg
lemma intervalCode_length_nonneg (c : IntervalCode) : 0 ≤ c.length := by
  cases c with
  | inl u => exact le_rfl
  | inr c => exact le_max_left _ _

/-- The full target interval is an honest original procedure. -/
-- @node: original_honest_nonempty
lemma original_honest_nonempty (κ : Params) (n : ℕ) :
    Nonempty {i : OriginalIntervalProc n //
      ∀ law, InModel κ law → 9/10 ≤ coverage n jointLaw (fun _ => ()) i law} := by
  let c : Endpoints := ⟨(-1/2, 1/2, true, true), by
    constructor
    · exact le_rfl
    · constructor <;> norm_num⟩
  refine ⟨⟨⟨fun _ => .inr c, measurable_const⟩, ?_⟩⟩
  intro law hlaw
  have ht : law.theta ∈ Icc (-1/2) (1/2) := by
    simpa [ObservedLaw.theta, neg_div] using abs_le.mp (hlaw.effectRange xstar)
  have he : {z : Experiment n | law.theta ∈ IntervalCode.toSet (.inr c)} = univ := by
    ext z
    simpa [IntervalCode.toSet, c] using ht
  change 9/10 ≤ (jointLaw n law.P).real
    {z : Experiment n | law.theta ∈ IntervalCode.toSet (.inr c)}
  rw [he]
  haveI : IsProbabilityMeasure (jointLaw n law.P) := by
    unfold jointLaw design
    infer_instance
  simp
  <;> norm_num

/-- Ignoring side information preserves whole-class honesty and expected length. -/
-- @node: honest_length_ignores_side
lemma honest_length_ignores_side {S : Type*} [MeasurableSpace S] (κ : Params) (n : ℕ)
    (side : ObservedLaw → S) :
    honestLengthWith κ n jointLaw side ≤ honestLength κ n := by
  letI := original_honest_nonempty κ n
  unfold honestLength honestLengthWith
  apply ciInf_mono_of_forall_exists
  · refine ⟨0, ?_⟩
    rintro x ⟨i, rfl⟩
    exact Real.iSup_nonneg fun law => integral_nonneg fun z => intervalCode_length_nonneg _
  · intro i
    refine ⟨⟨lift_original_interval n i.1, ?_⟩, le_rfl⟩
    intro law hlaw
    exact i.2 law hlaw

/-- Original decisions may ignore revealed nuisances, so revelation decreases each minimax value. -/
-- @node: oracle_comparison
lemma oracle_comparison (κ : Params) (hκ : κ.Valid) (n : ℕ) (hn : 2 ≤ n)
    (expLaw : ExperimentFamily) (hiid : IIDSampling expLaw) :
  oracleRisk κ n ≤ minimaxRisk κ n ∧
  oracleRiskEM κ n ≤ minimaxRisk κ n ∧
  oracleLengthE κ n ≤ honestLength κ n ∧
  oracleLengthEM κ n ≤ honestLength κ n := by
  exact ⟨minimax_ignores_side κ n sideE, minimax_ignores_side κ n sideEM,
    honest_length_ignores_side κ n sideE, honest_length_ignores_side κ n sideEM⟩

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

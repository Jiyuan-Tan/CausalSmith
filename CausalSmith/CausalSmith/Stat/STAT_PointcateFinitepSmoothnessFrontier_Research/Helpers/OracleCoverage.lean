module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.OracleConstruction
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The oracle interval's deterministic containment and Markov coverage argument. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

/-- A target in range within the public radius belongs to the reported oracle interval. -/
-- @node: oracleInterval_covers_of_error
lemma oracleInterval_covers_of_error (κ : Params) (n : ℕ)
    (z : Dataset n × unitInterval × Nuisance) (θ : ℝ)
    (hθ : θ ∈ Icc (-1/2) (1/2))
    (herr : |oracleEstimator κ n z - θ| ≤
      max 0 (10*oracleConstant κ*(n : ℝ)^(-rOracle κ))) :
    θ ∈ (oracleInterval κ n z).toSet := by
  let t := oracleEstimator κ n z
  let r := max 0 (10*oracleConstant κ*(n : ℝ)^(-rOracle κ))
  have ht := (oracleEstimator_total κ n).2 z
  have hr : 0 ≤ r := le_max_left _ _
  have hlo : max (-1/2 : ℝ) (t-r) ≤ t := max_le ht.1 (by linarith)
  have hhi : t ≤ min (1/2 : ℝ) (t+r) := le_min ht.2 (by linarith)
  have hv : (-1/2 : ℝ) ≤ max (-1/2) (t-r) ∧
      max (-1/2) (t-r) ≤ min (1/2) (t+r) ∧ min (1/2) (t+r) ≤ 1/2 :=
    ⟨le_max_left _ _, hlo.trans hhi, min_le_left _ _⟩
  change θ ∈ (closedInterval (max (-1/2) (t-r)) (min (1/2) (t+r))).toSet
  simp only [closedInterval, dif_pos hv, IntervalCode.toSet, ↓reduceIte, mem_Icc]
  have he := abs_le.mp herr
  change -r ≤ t - θ ∧ t - θ ≤ r at he
  exact ⟨max_le hθ.1 (by linarith [he.2]), le_min hθ.2 (by linarith [he.1])⟩

/-- Boundedness of the total oracle decision supplies integrable absolute loss. -/
-- @node: oracleEstimator_error_integrable
lemma oracleEstimator_error_integrable (κ : Params) (n : ℕ)
    (μ : Measure (Experiment n)) [IsProbabilityMeasure μ] (f : Nuisance) (θ : ℝ) :
    Integrable (fun z => |oracleEstimator κ n (z.1,z.2,f)-θ|) μ := by
  have hm : Measurable (fun z : Experiment n => |oracleEstimator κ n (z.1,z.2,f)-θ|) := by
    have ht := (oracleEstimator_total κ n).1
    fun_prop
  apply Integrable.of_bound hm.aestronglyMeasurable (1/2+|θ|)
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_abs]
  have ht := (oracleEstimator_total κ n).2 (z.1,z.2,f)
  have ha : |oracleEstimator κ n (z.1,z.2,f)| ≤ 1/2 :=
    abs_le.mpr ⟨by linarith [ht.1],ht.2⟩
  exact (abs_sub _ _).trans (by linarith only [ha])

/-- Markov's inequality converts the oracle risk ledger to whole-class coverage. -/
-- @node: oracleInterval_coverage_of_risk
lemma oracleInterval_coverage_of_risk (κ : Params) (n : ℕ) (hn : 2 ≤ n)
    (law : ObservedLaw) (hm : InModel κ law)
    (hrisk : decisionRisk n jointLaw sideE (oracleDecision κ n) law ≤
      oracleConstant κ*(n : ℝ)^(-rOracle κ)) :
    9/10 ≤ coverage n jointLaw sideE (oracleIntervalDecision κ n) law := by
  let μ := jointLaw n law.P
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  let : IsProbabilityMeasure μ := by dsimp [μ]; unfold jointLaw; infer_instance
  let err : Experiment n → ℝ := fun z =>
    |oracleEstimator κ n (z.1,z.2,sideE law)-law.theta|
  let c := oracleConstant κ*(n : ℝ)^(-rOracle κ)
  have hc : 0 < c := by
    have hconstant : 0 < oracleConstant κ := by
      unfold oracleConstant oracleMoment
      positivity
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    dsimp [c]
    positivity
  have he : Integrable err μ :=
    oracleEstimator_error_integrable κ n μ (sideE law) law.theta
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := μ) (f := err)
    (Filter.Eventually.of_forall (fun z => abs_nonneg _)) he (10*c)
  have hbad : μ.real {z | 10*c < err z} ≤ (1/10 : ℝ) := by
    have hsub : μ.real {z | 10*c < err z} ≤ μ.real {z | 10*c ≤ err z} :=
      measureReal_mono (μ := μ) (fun z (hz : 10*c < err z) => le_of_lt hz) (measure_ne_top μ _)
    have hmul := (mul_le_mul_of_nonneg_left hsub (by positivity : 0 ≤ 10*c)).trans hmarkov
    change (∫ z, err z ∂μ) ≤ c at hrisk
    nlinarith only [hmul.trans hrisk, hc]
  have hgood : MeasurableSet {z | err z ≤ 10*c} := by
    have ht := (oracleEstimator_total κ n).1
    apply measurableSet_le _ measurable_const
    dsimp [err]
    fun_prop
  have hcompl := measureReal_compl (μ := μ) hgood
  have hgoodprob : (9/10 : ℝ) ≤ μ.real {z | err z ≤ 10*c} := by
    have heq : {z | err z ≤ 10*c}ᶜ = {z | 10*c < err z} := by ext z; simp
    rw [heq, probReal_univ] at hcompl
    linarith only [hcompl, hbad]
  apply hgoodprob.trans
  change μ.real {z | err z ≤ 10*c} ≤
    μ.real {z | law.theta ∈ (oracleInterval κ n (z.1,z.2,sideE law)).toSet}
  apply measureReal_mono (μ := μ) _ (measure_ne_top μ _)
  intro z hz
  have hθ : law.theta ∈ Icc (-1/2) (1/2) := by
    simpa only [ObservedLaw.theta, mem_Icc, neg_div] using abs_le.mp (hm.effectRange xstar)
  apply oracleInterval_covers_of_error κ n _ law.theta hθ
  change err z ≤ max 0 (10*oracleConstant κ*(n : ℝ)^(-rOracle κ))
  have hr : 10*oracleConstant κ*(n : ℝ)^(-rOracle κ) = 10*c := by dsimp [c]; ring
  rw [hr, max_eq_right (by positivity)]
  exact hz

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

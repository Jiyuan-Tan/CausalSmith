module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.OracleCoverage
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.RatioRisk
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.TwoBlockLegs
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.UpperTruncatedExpectation

/-! Exact iid score-average moments and their absolute-risk consequence. -/
public section
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
variable {Ω : Type*} [MeasurableSpace Ω]

/-- A scaled iid sum has its single-record mean and exact independent-sum variance. -/
-- @node: oracle_iid_sum_moments
lemma oracle_iid_sum_moments (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (f : Ω → ℝ) (hf : MemLp f 2 P) (c : ℝ) :
    MemLp (fun o : Fin n → Ω => c * ∑ i, f (o i)) 2 (Measure.pi (fun _ => P)) ∧
    (∫ o : Fin n → Ω, c * ∑ i, f (o i) ∂Measure.pi (fun _ => P)) =
      c * (n : ℝ) * ∫ x, f x ∂P ∧
    variance (fun o : Fin n → Ω => c * ∑ i, f (o i)) (Measure.pi (fun _ => P)) =
      c^2 * (n : ℝ) * variance f P := by
  have hm (i : Fin n) := measurePreserving_eval (fun _ : Fin n => P) i
  have hi (i : Fin n) : MemLp (fun o : Fin n → Ω => f (o i)) 2
      (Measure.pi (fun _ => P)) := hf.comp_measurePreserving (hm i)
  refine ⟨(memLp_finsetSum Finset.univ (fun i _ => hi i)).const_mul c, ?_, ?_⟩
  · rw [integral_const_mul, integral_finsetSum _ (fun i _ => (hi i).integrable (by norm_num))]
    have he (i : Fin n) : (∫ o : Fin n → Ω, f (o i) ∂Measure.pi (fun _ => P)) =
        ∫ x, f x ∂P := by
      have h := (integral_map (hm i).measurable.aemeasurable
        ((hm i).map_eq.symm ▸ hf.aestronglyMeasurable)).symm
      simpa only [(hm i).map_eq] using h
    simp_rw [he]
    simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  · rw [variance_const_mul]
    have hv := variance_sum_pi (μ := fun _ : Fin n => P) (X := fun _ => f) (fun _ => hf)
    have hs : (fun o : Fin n → Ω => ∑ i, f (o i)) =
        ∑ i : Fin n, (fun o : Fin n → Ω => f (o i)) := by
      funext o
      simp only [Finset.sum_apply]
    rw [hs, hv]
    simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-- The iid average's absolute error is bounded by its bias and single-record square energy. -/
-- @node: oracle_iid_sum_absolute_risk
lemma oracle_iid_sum_absolute_risk (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (f : Ω → ℝ) (hf : MemLp f 2 P) (c θ : ℝ) :
    (∫ o : Fin n → Ω, |c * ∑ i, f (o i) - θ| ∂Measure.pi (fun _ => P)) ≤
      |c * (n : ℝ) * (∫ x, f x ∂P) - θ| +
        Real.sqrt (c^2 * (n : ℝ) * ∫ x, (f x)^2 ∂P) := by
  let Q := Measure.pi (fun _ : Fin n => P)
  let V := fun o : Fin n → Ω => c * ∑ i, f (o i)
  let m := ∫ o, V o ∂Q
  have h := oracle_iid_sum_moments P n f hf c
  have hcenter : MemLp (fun o => V o - m) 2 Q := h.1.sub (memLp_const m)
  have hz : (∫ o, V o - m ∂Q) = 0 := by
    rw [integral_sub (h.1.integrable (by norm_num)) (integrable_const m)]
    simp [m, Q, V]
  have hab := twoBlock_abs_le_standard_deviation Q _ hcenter hz
  have hv : variance (fun o => V o - m) Q = variance V Q := by
    simpa only using variance_sub_const h.1.aestronglyMeasurable m
  rw [hv] at hab
  have he : variance V Q ≤ c^2 * (n : ℝ) * ∫ x, (f x)^2 ∂P := by
    rw [h.2.2]
    exact mul_le_mul_of_nonneg_left (variance_le_expectation_sq hf.aestronglyMeasurable)
      (by positivity)
  have hi := (h.1.sub (memLp_const θ)).integrable (by norm_num)
  calc
    (∫ o, |V o - θ| ∂Q) ≤ ∫ o, |V o - m| + |m - θ| ∂Q :=
      integral_mono hi.abs (hcenter.integrable (by norm_num) |>.abs.add (integrable_const _))
        (fun o => abs_sub_le (V o) m θ)
    _ = (∫ o, |V o - m| ∂Q) + |m - θ| := by
      rw [integral_add (hcenter.integrable (by norm_num)).abs (integrable_const _)]
      simp [Q]
    _ ≤ Real.sqrt (c^2 * (n : ℝ) * ∫ x, (f x)^2 ∂P) + |m - θ| :=
      by linarith [hab.trans (Real.sqrt_le_sqrt he)]
    _ = _ := by
      rw [add_comm]
      have hm : m = c * (n : ℝ) * ∫ x, f x ∂P := h.2.1
      rw [hm]

/-- The oracle decision's projection and independent seed preserve the iid score-risk bound. -/
-- @node: oracle_decision_sample_risk
lemma oracle_decision_sample_risk (κ : Params) (n : ℕ) (law : ObservedLaw)
    (hm : InModel κ law) :
    let f : O → ℝ := fun o => if X o ∈ window (oracleH κ n) then
      trunc (oracleT κ n) (suppliedScore (sideE law) o) else 0
    let c : ℝ := ((n : ℝ)*oracleH κ n)⁻¹
    decisionRisk n jointLaw sideE (oracleDecision κ n) law ≤
      |c * (n : ℝ) * (∫ o, f o ∂law.P) - law.theta| +
        Real.sqrt (c^2 * (n : ℝ) * ∫ o, (f o)^2 ∂law.P) := by
  dsimp only
  let f : O → ℝ := fun o => if X o ∈ window (oracleH κ n) then
    trunc (oracleT κ n) (suppliedScore (sideE law) o) else 0
  let c : ℝ := ((n : ℝ)*oracleH κ n)⁻¹
  have hmeas : Measurable f := by
    apply Measurable.ite
    · exact measurableSet_Icc.preimage (by unfold X; fun_prop)
    · exact (measurable_trunc _).comp (measurable_suppliedScore.comp
        (by fun_prop : Measurable (fun o : O => (sideE law, o))))
    · fun_prop
  have hf : MemLp f 2 law.P := by
    apply MemLp.of_bound hmeas.aestronglyMeasurable |oracleT κ n|
    filter_upwards [] with o
    dsimp only [f]
    split_ifs
    · simpa only [Real.norm_eq_abs] using upper_trunc_abs_bound (oracleT κ n) _
    · simp
  have h := oracle_iid_sum_moments law.P n f hf c
  have hθ : law.theta ∈ Set.Icc (-1/2) (1/2) := by
    have ht := abs_le.mp (hm.effectRange xstar)
    simpa only [ObservedLaw.theta, neg_div, Set.mem_Icc] using ht
  let Q := Measure.pi (fun _ : Fin n => law.P)
  have hclip : Integrable (fun o : Dataset n => |clip (c * ∑ i, f (o i))-law.theta|) Q := by
    have hmc : Measurable (fun o : Dataset n => c * ∑ i, f (o i)) :=
      (Finset.measurable_sum Finset.univ (fun i _ =>
        hmeas.comp (measurable_pi_apply i))).const_mul c
    have hma : Measurable (fun o : Dataset n => |clip (c * ∑ i, f (o i))-law.theta|) := by
      fun_prop
    apply Integrable.of_bound hma.aestronglyMeasurable (1/2+|law.theta|)
    filter_upwards [] with o
    rw [Real.norm_eq_abs, abs_abs]
    have ht : |clip (c * ∑ i, f (o i))| ≤ 1/2 := by
      unfold clip
      apply abs_le.mpr
      constructor
      · simpa only [neg_div] using le_max_left (-1/2 : ℝ) (min (c * ∑ i, f (o i)) (1/2))
      · exact max_le (by norm_num) (min_le_right _ _)
    exact (abs_sub _ _).trans (by linarith)
  have hseed : decisionRisk n jointLaw sideE (oracleDecision κ n) law =
      ∫ o : Dataset n, |clip (c * ∑ i, f (o i))-law.theta| ∂Q := by
    let : IsProbabilityMeasure design := by unfold design; infer_instance
    change (∫ z : Experiment n, |clip (c * ∑ i, f (z.1 i))-law.theta| ∂Q.prod design) = _
    simpa using
      (integral_fun_fst (μ := Q) (ν := design)
        (fun o : Dataset n => |clip (c * ∑ i, f (o i))-law.theta|))
  rw [hseed]
  exact (integral_mono hclip ((h.1.sub (memLp_const law.theta)).integrable (by norm_num)).abs
    (fun o => clip_error_le _ _ hθ)).trans
      (oracle_iid_sum_absolute_risk law.P n f hf c law.theta)

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

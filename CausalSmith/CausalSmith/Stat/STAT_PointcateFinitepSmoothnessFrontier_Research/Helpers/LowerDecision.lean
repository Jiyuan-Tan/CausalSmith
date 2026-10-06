module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.LowerComponents
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.TwoPrior

/-! Decision-theoretic reduction of the explicit finite sign priors. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

/-- Uniform averaging of finite probability laws retains total mass one. -/
-- @node: lower_uniform_mixture_probability
lemma lower_uniform_mixture_probability {ι Ω : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace Ω] (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)] :
    IsProbabilityMeasure ((Fintype.card ι : ℝ≥0∞)⁻¹ • ∑ i, ν i) := by
  constructor
  simp only [Measure.smul_apply, Measure.finset_sum_apply, measure_univ, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel
    (by exact_mod_cast (Fintype.card_ne_zero (α := ι))) (by simp)

/-- The integral under a uniform finite mixture is bounded by any common integral bound. -/
-- @node: lower_uniform_mixture_integral_le
lemma lower_uniform_mixture_integral_le {ι Ω : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace Ω] (ν : ι → Measure Ω) (f : Ω → ℝ) (M : ℝ)
    (hi : ∀ i, Integrable f (ν i)) (hb : ∀ i, (∫ z, f z ∂ν i) ≤ M) :
    (∫ z, f z ∂((Fintype.card ι : ℝ≥0∞)⁻¹ • ∑ i, ν i)) ≤ M := by
  rw [integral_smul_measure, integral_finsetSum_measure (fun i _ => hi i)]
  simp only [smul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  calc
    (Fintype.card ι : ℝ)⁻¹ * ∑ i, ∫ z, f z ∂ν i
        ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _ : ι, M := by
          apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hb i))
          positivity
    _ = M := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc]
      rw [inv_mul_cancel₀ (by exact_mod_cast (Fintype.card_ne_zero (α := ι))), one_mul]

/-- Adding the common seed commutes with the finite uniform prior. -/
-- @node: lower_seeded_mixture_eq
lemma lower_seeded_mixture_eq (κ : Params) (n : ℕ) (ε : Bool) :
    (lowerMixture κ n ε).prod design =
      (Fintype.card (Signs κ n) : ℝ≥0∞)⁻¹ •
        ∑ v : Signs κ n, jointLaw n (lowerPriorLaw κ n ε v).P := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  unfold lowerMixture jointLaw
  rw [Measure.prod_smul_left]
  congr 1
  induction (Finset.univ : Finset (Signs κ n)) using Finset.induction_on with
  | empty => simp
  | @insert v s hv ih => simp only [Finset.sum_insert hv, Measure.add_prod, ih]

/-- Every seeded finite sign mixture is a probability experiment. -/
-- @node: lower_seeded_mixture_probability
lemma lower_seeded_mixture_probability (κ : Params) (n : ℕ) (ε : Bool) :
    IsProbabilityMeasure ((lowerMixture κ n ε).prod design) := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  letI (v : Signs κ n) : IsProbabilityMeasure (jointLaw n (lowerPriorLaw κ n ε v).P) := by
    unfold jointLaw
    infer_instance
  rw [lower_seeded_mixture_eq]
  exact lower_uniform_mixture_probability _

/-- An original range-valued decision has integrable loss under every probability experiment. -/
-- @node: lower_decision_loss_integrable
lemma lower_decision_loss_integrable (n : ℕ) (t : Estimator n) (θ : ℝ)
    (μ : Measure (Experiment n)) [IsProbabilityMeasure μ] :
    Integrable (fun z => |t.1 (z.1,z.2,())-θ|) μ := by
  have hm : Measurable (fun z : Experiment n => |t.1 (z.1,z.2,())-θ|) := by
    have ht : Measurable (fun z : Experiment n => t.1 (z.1,z.2,())) :=
      t.2.1.comp (by fun_prop)
    exact continuous_abs.measurable.comp (ht.sub measurable_const)
  apply Integrable.of_bound hm.aestronglyMeasurable (1/2+|θ|)
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_abs]
  have hr := t.2.2 (z.1,z.2,())
  calc
    |t.1 (z.1,z.2,())-θ| ≤ |t.1 (z.1,z.2,())|+|θ| := abs_sub _ _
    _ ≤ 1/2+|θ| := by
      have ha : |t.1 (z.1,z.2,())| ≤ 1/2 := abs_le.mpr ⟨by linarith [hr.1],hr.2⟩
      linarith

/-- The constant effect makes every member of a sign prior have the same point target. -/
-- @node: lower_prior_target
lemma lower_prior_target (κ : Params) (n : ℕ) (hκ : κ.Valid)
    (hb : boundary κ ≤ 1) (hn : 2 ≤ n) (ε : Bool) (v : Signs κ n) :
    (lowerPriorLaw κ n ε v).theta = lowerEffect κ n ε xstar := by
  exact congrFun (lower_prior_membership κ n hκ hb hn ε v).2 xstar

/-- Model effect range and decision range bound absolute risk by one. -/
-- @node: lower_decision_risk_bounds
lemma lower_decision_risk_bounds (κ : Params) (n : ℕ) (t : Estimator n)
    (law : ObservedLaw) (hm : InModel κ law) :
    0 ≤ decisionRisk n jointLaw (fun _ => ()) t law ∧
      decisionRisk n jointLaw (fun _ => ()) t law ≤ 1 := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  letI : IsProbabilityMeasure (jointLaw n law.P) := by unfold jointLaw; infer_instance
  constructor
  · exact integral_nonneg (fun _ => abs_nonneg _)
  · have hi := lower_decision_loss_integrable n t law.theta (jointLaw n law.P)
    have hb (z : Experiment n) : |t.1 (z.1,z.2,())-law.theta| ≤ 1 := by
      have hr := t.2.2 (z.1,z.2,())
      have ht : |t.1 (z.1,z.2,())| ≤ 1/2 := abs_le.mpr ⟨by linarith [hr.1],hr.2⟩
      have hθ := hm.effectRange xstar
      exact (abs_sub _ _).trans (by change _ ≤ 1; change |law.theta| ≤ 1/2 at hθ; linarith)
    simpa [decisionRisk] using integral_mono hi (integrable_const (1 : ℝ)) hb

/-- The finite sign-prior risk cannot exceed the original whole-model worst risk. -/
-- @node: lower_mixture_risk_le_worst
lemma lower_mixture_risk_le_worst (κ : Params) (n : ℕ) (hκ : κ.Valid)
    (hb : boundary κ ≤ 1) (hn : 2 ≤ n) (t : Estimator n) (ε : Bool) :
    (∫ z, |t.1 (z.1,z.2,())-lowerEffect κ n ε xstar|
      ∂(lowerMixture κ n ε).prod design) ≤
    ⨆ law : {law // InModel κ law}, decisionRisk n jointLaw (fun _ => ()) t law.1 := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have hB : BddAbove (Set.range (fun law : {law // InModel κ law} =>
      decisionRisk n jointLaw (fun _ => ()) t law.1)) :=
    ⟨1, by rintro _ ⟨law,rfl⟩; exact (lower_decision_risk_bounds κ n t law.1 law.2).2⟩
  rw [lower_seeded_mixture_eq]
  apply lower_uniform_mixture_integral_le
  · intro v
    letI : IsProbabilityMeasure (jointLaw n (lowerPriorLaw κ n ε v).P) := by
      unfold jointLaw; infer_instance
    exact lower_decision_loss_integrable n t _ _
  · intro v
    rw [← lower_prior_target κ n hκ hb hn ε v]
    exact le_ciSup hB ⟨lowerPriorLaw κ n ε v,
      (lower_prior_membership κ n hκ hb hn ε v).1⟩

/-- Le Cam's absolute-risk reduction applied to the original seeded sign mixtures. -/
-- @node: lower_interaction_worst_risk
lemma lower_interaction_worst_risk (κ : Params) (n : ℕ) (hκ : κ.Valid)
    (hb : boundary κ ≤ 1) (hn : 2 ≤ n) (t : Estimator n) :
    cInter κ*(n : ℝ)^(-rInter κ) ≤
      ⨆ law : {law // InModel κ law}, decisionRisk n jointLaw (fun _ => ()) t law.1 := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  let ν0 := (lowerMixture κ n true).prod design
  let ν1 := (lowerMixture κ n false).prod design
  letI : IsProbabilityMeasure ν0 := lower_seeded_mixture_probability κ n true
  letI : IsProbabilityMeasure ν1 := lower_seeded_mixture_probability κ n false
  letI (ε : Bool) : IsProbabilityMeasure (lowerMixture κ n ε) :=
    lower_uniform_mixture_probability _
  have htv : Causalean.Stat.tvDist ν0 ν1 ≤ 1/4 := by
    rw [two_prior_seed_tv]
    exact lower_mixture_tv κ n hκ hb hn
  have hgap : 0 < |lowerEffect κ n false xstar-lowerEffect κ n true xstar| := by
    rw [abs_sub_comm, lower_effect_separation κ n hn]
    unfold lowerP0 lowerC
    positivity
  have h := two_prior_absolute_risk ν0 ν1
    (lowerEffect κ n true xstar) (lowerEffect κ n false xstar) (1/4)
    hgap htv (fun z => t.1 (z.1,z.2,())) (t.2.1.comp (by fun_prop))
  rw [← ofReal_integral_eq_lintegral_ofReal (lower_decision_loss_integrable n t _ ν0)
      (Filter.Eventually.of_forall (fun _ => abs_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal (lower_decision_loss_integrable n t _ ν1)
      (Filter.Eventually.of_forall (fun _ => abs_nonneg _)), ← ENNReal.ofReal_max] at h
  have hr := (ENNReal.ofReal_le_ofReal_iff (le_trans
    (integral_nonneg (fun _ => abs_nonneg _)) (le_max_left _ _))).mp h
  rw [cInter_separation_identity κ n hn]
  have hcoef : |lowerEffect κ n false xstar-lowerEffect κ n true xstar| * (1-1/4)/4 =
      (3/16 : ℝ) * |lowerEffect κ n true xstar-lowerEffect κ n false xstar| := by
    rw [abs_sub_comm]; ring
  rw [hcoef] at hr
  exact hr.trans (max_le (lower_mixture_risk_le_worst κ n hκ hb hn t true)
    (lower_mixture_risk_le_worst κ n hκ hb hn t false))

/-- Infimizing the estimator-wise bound gives the interaction minimax-risk bound. -/
-- @node: lower_interaction_minimax_risk
lemma lower_interaction_minimax_risk (κ : Params) (n : ℕ) (hκ : κ.Valid)
    (hb : boundary κ ≤ 1) (hn : 2 ≤ n) :
    cInter κ*(n : ℝ)^(-rInter κ) ≤ minimaxRisk κ n := by
  haveI : Nonempty (SideEstimator n Unit) := ⟨⟨fun _ => 0, measurable_const,
    fun _ => ⟨by norm_num,by norm_num⟩⟩⟩
  exact le_ciInf (lower_interaction_worst_risk κ n hκ hb hn)

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

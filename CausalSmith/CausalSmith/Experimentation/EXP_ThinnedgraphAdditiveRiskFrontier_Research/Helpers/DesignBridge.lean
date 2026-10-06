module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Basic
public import Causalean.Experimentation.DesignBased.Designs.BernoulliMoments
public import Causalean.Stat.FiniteDesign.ProductMeasure

/-!
# Assignment and audit bridges
-/

public section

open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The canonical product design has the required assignment marginal.  [For the stated data and conditions](hyp:q,hq), [the stated conclusion holds](goal). -/
-- @node: thinnedDesign_assignment
lemma thinnedDesign_assignment (q : ℝ) (hq : q ∈ Set.Icc 0 1) :
    AssignmentLaw (thinnedDesign V q) := by
  let : IsProbabilityMeasure (bernoulliLaw (1 / 2)) :=
    bernoulliLaw_probability _ (by constructor <;> norm_num)
  let : IsProbabilityMeasure (bernoulliLaw q) := bernoulliLaw_probability q hq
  unfold AssignmentLaw thinnedDesign halfBernoulli auditLaw
  rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- The canonical product design has the required audit marginal.  [For the stated data and conditions](hyp:q,hq), [the stated conclusion holds](goal). -/
-- @node: thinnedDesign_audit
lemma thinnedDesign_audit (q : ℝ) (hq : q ∈ Set.Icc 0 1) :
    AuditLaw (thinnedDesign V q) q := by
  let : IsProbabilityMeasure (bernoulliLaw (1 / 2)) :=
    bernoulliLaw_probability _ (by constructor <;> norm_num)
  let : IsProbabilityMeasure (bernoulliLaw q) := bernoulliLaw_probability q hq
  refine ⟨hq.1, hq.2, ?_⟩
  unfold thinnedDesign halfBernoulli auditLaw
  rw [Measure.map_snd_prod, measure_univ, one_smul]

/-- The two coordinates of the canonical product design are independent.  [For the stated data and conditions](hyp:q,hq), [the stated conclusion holds](goal). -/
-- @node: thinnedDesign_independent
lemma thinnedDesign_independent (q : ℝ) (hq : q ∈ Set.Icc 0 1) :
    DesignIndependent (thinnedDesign V q) := by
  let : IsProbabilityMeasure (bernoulliLaw (1 / 2)) :=
    bernoulliLaw_probability _ (by constructor <;> norm_num)
  let : IsProbabilityMeasure (bernoulliLaw q) := bernoulliLaw_probability q hq
  unfold DesignIndependent thinnedDesign halfBernoulli auditLaw
  exact ProbabilityTheory.indepFun_prod measurable_id measurable_id

/-- The three design atoms determine the canonical assignment-audit product law.  [For the stated data and conditions](hyp:D,q,ha,hw,hi), [the stated conclusion holds](goal). -/
-- @node: design_eq_thinnedDesign
lemma design_eq_thinnedDesign (D : Measure (Assign V × Audit V)) (q : ℝ)
    (ha : AssignmentLaw D) (hw : AuditLaw D q) (hi : DesignIndependent D) :
    D = thinnedDesign V q := by
  let : IsProbabilityMeasure (bernoulliLaw (1 / 2)) :=
    bernoulliLaw_probability _ (by constructor <;> norm_num)
  have hm : IsProbabilityMeasure (D.map Prod.fst) := by
    rw [ha]
    unfold halfBernoulli
    infer_instance
  let : IsProbabilityMeasure D := Measure.isProbabilityMeasure_of_map Prod.fst
  have heq := hi.map_prod_eq_prod_map_map measurable_fst.aemeasurable
    measurable_snd.aemeasurable
  change D.map id = (D.map Prod.fst).prod (D.map Prod.snd) at heq
  rw [Measure.map_id, ha, hw.2.2] at heq
  exact heq

/-- The three design atoms imply that the joint design is a probability law.  [For the stated data and conditions](hyp:D,q,ha,hw,hi), [the stated conclusion holds](goal). -/
-- @node: design_isProbabilityMeasure
lemma design_isProbabilityMeasure (D : Measure (Assign V × Audit V)) (q : ℝ)
    (ha : AssignmentLaw D) (hw : AuditLaw D q) (hi : DesignIndependent D) :
    IsProbabilityMeasure D := by
  rw [design_eq_thinnedDesign D q ha hw hi]
  exact thinnedDesign_probabilityDesign q ⟨hw.1, hw.2.1⟩

/-- Measure-valued assignment expectations equal finite-design Bernoulli expectations.  [For the stated data and conditions](hyp:f), [the stated conclusion holds](goal). -/
-- @node: integral_halfBernoulli_eq_bernoulliDesign_E
lemma integral_halfBernoulli_eq_bernoulliDesign_E (f : Assign V → ℝ) :
    ∫ z, f z ∂(halfBernoulli V) =
      (Causalean.Experimentation.DesignBased.bernoulliDesign (fun _ : V => (1 / 2 : ℝ))
        (fun _ => div_nonneg (show (0 : ℝ) ≤ 1 from zero_le_one) (show (0 : ℝ) ≤ 2 from
          zero_le_two))
        (fun _ => half_le_self (show (0 : ℝ) ≤ 1 from zero_le_one))).E f := by
  let D := Causalean.Experimentation.DesignBased.bernoulliDesign
    (fun _ : V => (1 / 2 : ℝ))
    (fun _ => div_nonneg (show (0 : ℝ) ≤ 1 from zero_le_one)
      (show (0 : ℝ) ≤ 2 from zero_le_two))
    (fun _ => half_le_self (show (0 : ℝ) ≤ 1 from zero_le_one))
  have hcoin : ∀ i : V,
      (Causalean.Experimentation.DesignBased.coinDesign (1 / 2)
        (by norm_num) (by norm_num)).toMeasure = bernoulliLaw (1 / 2) := by
    intro i
    simp [Causalean.Experimentation.DesignBased.FiniteDesign.toMeasure,
      Causalean.Experimentation.DesignBased.coinDesign, bernoulliLaw, add_comm]
  have hD : D.toMeasure = halfBernoulli V := by
    unfold D Causalean.Experimentation.DesignBased.bernoulliDesign
    rw [Causalean.Experimentation.DesignBased.prodDesign_toMeasure_eq_pi]
    exact congrArg Measure.pi (funext hcoin)
  rw [← hD]
  exact D.integral_toMeasure f

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier

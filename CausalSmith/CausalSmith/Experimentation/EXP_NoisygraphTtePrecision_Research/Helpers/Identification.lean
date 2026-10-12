module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.DesignBridge
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Identification from constant-assignment cells

Every assignment has positive mass. On each assignment cell the observed
outcome is the fixed schedule's deterministic potential outcome, so its
normalized cell integral recovers that outcome even for an uninformative channel.
-/

public section

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- [The fair product assignment puts mass two to the negative population size on each atom.](goal) -/
-- @node: halfBernoulli_assignment_mass
lemma halfBernoulli_assignment_mass (z : Assign V) :
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.halfBernoulli V {z} =
      (2 : ℝ≥0∞)⁻¹ ^ Fintype.card V := by
  letI := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw_probability
    (1/2) (by constructor <;> norm_num)
  rw [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.halfBernoulli,
    Measure.pi_singleton]
  have hbit (b : Bool) :
      CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (1/2) {b} =
        (2 : ℝ≥0∞)⁻¹ := by
    cases b <;> norm_num [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw]
      <;> rw [ENNReal.ofReal_div_of_pos (by norm_num)] <;> norm_num
  simp_rw [hbit]
  simp

/-- Given [the stated assumptions](hyp:ha), [Adjoining the independent seed and recording the experiment preserves assignment-cell mass.](goal) -/
-- @node: recordLaw_assignment_mass
lemma recordLaw_assignment_mass (D : Design V) (η : Schedule V)
    (ha : AssignmentLaw D) (z : Assign V) :
    recordLaw D η {x | x.1.2.1 = z} = (2 : ℝ≥0∞)⁻¹ ^ Fintype.card V := by
  letI : IsProbabilityMeasure seedLaw :=
    ⟨by simp [seedLaw, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.seedLaw,
      Real.volume_Icc]⟩
  have hm : Measurable (fun ω : (Assign V × Acq V) × ℝ => (recordOf η ω.1, ω.2)) := by
    fun_prop
  have hs : MeasurableSet {x : Record V × ℝ | x.1.2.1 = z} := by
    exact measurableSet_eq_fun (by fun_prop) measurable_const
  rw [recordLaw, Measure.map_apply hm hs]
  rw [show (fun ω : (Assign V × Acq V) × ℝ => (recordOf η ω.1, ω.2)) ⁻¹'
      {x : Record V × ℝ | x.1.2.1 = z} = (Prod.fst ⁻¹' {z}) ×ˢ Set.univ by
    ext ω; simp [recordOf]]
  rw [Measure.prod_prod, measure_univ, mul_one]
  rw [← Measure.map_apply measurable_fst (MeasurableSet.singleton z), ha η]
  exact halfBernoulli_assignment_mass z

/-- [The numerical response on an assignment cell is its deterministic potential outcome.](goal) -/
-- @node: recordLaw_assignment_integral
lemma recordLaw_assignment_integral (D : Design V) (η : Schedule V)
    (z : Assign V) (i : V) :
    (∫ x in {x : Record V × ℝ | x.1.2.1 = z}, x.1.2.2 i ∂recordLaw D η) =
      (recordLaw D η {x | x.1.2.1 = z}).toReal * potentialOutcome η i z := by
  have hm : Measurable (fun ω : (Assign V × Acq V) × ℝ => (recordOf η ω.1, ω.2)) := by
    fun_prop
  have hs : MeasurableSet {x : Record V × ℝ | x.1.2.1 = z} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  rw [recordLaw, setIntegral_map hs (by fun_prop) hm.aemeasurable]
  have heq : ∫ ω in (fun ω : (Assign V × Acq V) × ℝ => (recordOf η ω.1, ω.2)) ⁻¹'
      {x : Record V × ℝ | x.1.2.1 = z}, (recordOf η ω.1, ω.2).1.2.2 i
        ∂(D η).prod seedLaw =
      ∫ _ω in (fun ω : (Assign V × Acq V) × ℝ => (recordOf η ω.1, ω.2)) ⁻¹'
      {x : Record V × ℝ | x.1.2.1 = z}, potentialOutcome η i z ∂(D η).prod seedLaw := by
    apply setIntegral_congr_fun (hm hs)
    intro ω hω
    change ω.1.1 = z at hω
    change potentialOutcome η i ω.1.1 = potentialOutcome η i z
    rw [hω]
  rw [heq, integral_const, measureReal_restrict_apply_univ,
    Measure.map_apply hm hs]
  rfl

/-- Given [the stated assumptions](hyp:ha), [Normalizing a positive assignment cell identifies its potential outcome.](goal) -/
-- @node: recordLaw_assignment_mean
lemma recordLaw_assignment_mean (D : Design V) (η : Schedule V)
    (ha : AssignmentLaw D) (z : Assign V) (i : V) :
    (∫ x in {x : Record V × ℝ | x.1.2.1 = z}, x.1.2.2 i ∂recordLaw D η) /
      (recordLaw D η {x | x.1.2.1 = z}).toReal = potentialOutcome η i z := by
  rw [recordLaw_assignment_integral, recordLaw_assignment_mass D η ha z]
  have hp : ((2 : ℝ≥0∞)⁻¹ ^ Fintype.card V).toReal ≠ 0 := by
    simp
  exact mul_div_cancel_left₀ _ hp

end CausalSmith.Experimentation.NoisygraphTtePrecision

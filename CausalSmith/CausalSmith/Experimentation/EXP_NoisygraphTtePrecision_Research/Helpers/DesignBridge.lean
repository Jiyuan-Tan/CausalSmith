module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Basic
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.DesignBridge

/-!
# Joint law and comparison experiment bridges

Cold scaffold: definitions are complete; proof obligations are reserved for Stage 3.
-/

public section

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.style.whitespace false

variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Given [the stated assumptions](hyp:hqr), [Every coordinate of an admissible acquisition channel has unit mass.](goal) -/
-- @node: acquisitionLaw_probability
lemma acquisitionLaw_probability (q r : ℝ) (hqr : ChannelDomain q r) (η : Schedule V) :
    IsProbabilityMeasure (acquisitionLaw η q r) := by
  have hq : q ∈ Set.Icc 0 1 := ⟨hqr.1.trans hqr.2.1, hqr.2.2⟩
  have hr : r ∈ Set.Icc 0 1 := ⟨hqr.1, hqr.2.1.trans hqr.2.2⟩
  letI : ∀ e : OffDiag V, IsProbabilityMeasure
      (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw
        (if η.edge e.1.1 e.1.2 then q else r)) := fun e => by
    split <;> exact CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw_probability _ (by assumption)
  unfold acquisitionLaw
  infer_instance

/-- Given [the stated assumptions](hyp:hqr), [Admissible channels define probability laws at every fixed schedule.](goal) -/
-- @node: noisyDesign_probability
lemma noisyDesign_probability (q r : ℝ) (hqr : ChannelDomain q r) (η : Schedule V) :
    IsProbabilityMeasure (noisyDesign q r η) := by
  letI := acquisitionLaw_probability q r hqr η
  letI : IsProbabilityMeasure
      (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (1 / 2)) :=
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw_probability
      _ (by constructor <;> norm_num)
  unfold noisyDesign CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.halfBernoulli
  infer_instance

/-- Given [the stated assumptions](hyp:hqr), [The canonical channel satisfies all three design atoms.](goal) -/
-- @node: noisyDesign_atoms
lemma noisyDesign_atoms (q r : ℝ) (hqr : ChannelDomain q r) :
    AssignmentLaw (noisyDesign (V := V) q r) ∧ AcquisitionLaw (noisyDesign (V := V) q r) q r ∧
    DesignIndependent (noisyDesign (V := V) q r) := by
  letI : IsProbabilityMeasure
      (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (1 / 2)) :=
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw_probability
      _ (by constructor <;> norm_num)
  refine ⟨?_, ?_, ?_⟩
  · intro η
    letI := acquisitionLaw_probability q r hqr η
    unfold noisyDesign
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  · intro η
    unfold noisyDesign CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.halfBernoulli
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  · intro η
    letI := acquisitionLaw_probability q r hqr η
    unfold noisyDesign CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.halfBernoulli
    exact ProbabilityTheory.indepFun_prod measurable_id measurable_id

/-- Given [the stated assumptions](hyp:ha,hH,hi), [The three atoms determine the whole joint design, not just its marginals.](goal) -/
-- @node: design_eq_noisyDesign
lemma design_eq_noisyDesign (D : Design V) (q r : ℝ) (ha : AssignmentLaw D)
    (hH : AcquisitionLaw D q r) (hi : DesignIndependent D) : D = noisyDesign q r := by
  funext η
  let : IsProbabilityMeasure
      (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (1 / 2)) :=
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw_probability
      _ (by constructor <;> norm_num)
  have hm : IsProbabilityMeasure ((D η).map Prod.fst) := by
    rw [ha η]
    unfold CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.halfBernoulli
    infer_instance
  let : IsProbabilityMeasure (D η) := Measure.isProbabilityMeasure_of_map Prod.fst
  have heq := (hi η).map_prod_eq_prod_map_map measurable_fst.aemeasurable
    measurable_snd.aemeasurable
  change (D η).map id = ((D η).map Prod.fst).prod ((D η).map Prod.snd) at heq
  rw [Measure.map_id, ha η, hH η] at heq
  exact heq
/-- [The original-record construction is measurable.](goal) -/
-- @node: recordOf_measurable
@[fun_prop] lemma recordOf_measurable (η : Schedule V) : Measurable (recordOf η) := by
  fun_prop
/-- Given [the stated assumptions](hyp:hp), [Masking a Bernoulli audit by a fixed true-arrow indicator gives the acquisition bit.](goal) -/
-- @node: bernoulliLaw_mask
lemma bernoulliLaw_mask (p : ℝ) (hp : p ∈ Set.Icc 0 1) (b : Bool) :
    (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw p).map
      (fun w => b && w) =
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw
      (if b then p else 0) := by
  cases b
  · letI := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw_probability p hp
    change (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw p).map
      (fun _ => false) = CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw 0
    rw [Measure.map_const, measure_univ, one_smul]
    simp [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw]
  · simp [Measure.map_id]

/-- Given [the stated assumptions](hyp:hp), [Masking all audit coordinates gives exactly the no-false-positive acquisition law.](goal) -/
-- @node: acquisitionLaw_eq_masked_audit
lemma acquisitionLaw_eq_masked_audit (η : Schedule V) (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    acquisitionLaw η p 0 =
      (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.auditLaw V p).map
        (fun H e => decide (η.edge e.1.1 e.1.2) && H e) := by
  letI := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw_probability p hp
  rw [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.auditLaw,
    Measure.pi_map_pi (fun _ => (Measurable.of_discrete).aemeasurable)]
  unfold acquisitionLaw
  congr 1
  funext e
  rw [bernoulliLaw_mask p hp]
  simp

/-- Given [the stated assumptions](hyp:hp), [The zero-false-positive record law equals the inherited thinned experiment.](goal) -/
-- @node: comparison_record_law_eq_thin
lemma comparison_record_law_eq_thin (η : Schedule V) (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    (μZ : Measure (Assign V)) :
    (μZ.prod (acquisitionLaw η p 0)).map (recordOf η) =
    (μZ.prod (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.auditLaw V p)).map (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.recordOf η) := by
  letI := acquisitionLaw_probability p 0 ⟨le_refl 0, hp.1, hp.2⟩ η
  letI := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw_probability p hp
  have hm : Measurable (fun H : Acq V => fun e => decide (η.edge e.1.1 e.1.2) && H e) := by
    fun_prop
  have ht : Measurable (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.recordOf η) := by
    fun_prop
  ext s hs
  rw [Measure.map_apply (recordOf_measurable η) hs, Measure.map_apply ht hs,
    Measure.prod_apply ((recordOf_measurable η) hs), Measure.prod_apply (ht hs)]
  apply lintegral_congr
  intro z
  rw [acquisitionLaw_eq_masked_audit η p hp,
    Measure.map_apply hm (measurable_prodMk_left ((recordOf_measurable η) hs))]
  rfl

end CausalSmith.Experimentation.NoisygraphTtePrecision

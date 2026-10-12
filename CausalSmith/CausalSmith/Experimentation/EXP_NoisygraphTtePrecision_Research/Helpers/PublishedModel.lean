module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.DesignBridge
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.PublishedModel

/-!
# The cited SNIPE convention gate and published representation

Cold scaffold: definitions are complete; proof obligations are reserved for Stage 3.
-/

@[expose] public section

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
/-- Cortez-Rodriguez, Eichhorn and Yu (2023), Sections 3.1–3.3,
Assumptions 1–2 and equations (3.2)–(3.5), public manuscript v3.
Source: https://arxiv.org/html/2208.05553v3#S3 .
At order one, directed neighborhoods may include their own vertex, the polynomial includes
a constant, the absolute coefficient envelope includes that constant, and edge coefficients
may vanish. The target is the inherited all-treated minus all-control average.
This frozen logical convention is an assumed gate, passed explicitly to published_model. -/
-- @node: lem:snipe-source-conventions
def SnipeSourceConventions : Sort 0 :=
  ∀ ϑ : CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.PublishedSchedule V, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.PublishedOrderOne ϑ →
    (∀ i z, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.pubOutcome ϑ i z = ϑ.coef i ∅ +
      ∑ j ∈ CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.pubNbhd ϑ i, ϑ.coef i {j} * CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.treatment (z j)) ∧
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.pubEnvelope ϑ = Finset.univ.sup (fun i =>
      (|ϑ.coef i ∅| + ∑ j ∈ CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.pubNbhd ϑ i, |ϑ.coef i {j}|).toNNReal)
/-- The two-sided acquisition law reads only published off-diagonal arrows. -/
def pubAcquisitionLaw (ϑ : CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.PublishedSchedule V) (q r : ℝ) : Measure (Acq V) :=
  Measure.pi (fun e : OffDiag V => CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (if ϑ.edge e.1.1 e.1.2 then q else r))
/-- The original record for a published representation, with the diagonal unacquired. -/
def pubRecordOf (ϑ : CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.PublishedSchedule V) (ω : Assign V × Acq V) : Record V :=
  (ω.2, ω.1, fun i => CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.pubOutcome ϑ i ω.1)
/-- Given [the stated assumptions](hyp:hconv_of_gate), [Adjoining compulsory known own-treatment arrows gives the two inverse class maps,
preserving every response, causal target, and off-diagonal acquisition record.
The published convention is an explicit assumed input.](goal) -/
-- @node: lem:published-model
lemma published_model (hconv_of_gate : SnipeSourceConventions (V := V)) :
    (∀ (η : Schedule V) (d : ℕ), ScheduleClass η d →
      CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.PublishedClass (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.augment η) (d+1) ∧ ∀ i, (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.augment η).edge i i) ∧
    (∀ (ϑ : CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.PublishedSchedule V) (d : ℕ), CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.PublishedClass ϑ (d+1) → (∀ i, ϑ.edge i i) →
      ScheduleClass (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.strip ϑ) d ∧ CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.PublishedEquivalent (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.augment (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.strip ϑ)) ϑ) ∧
    (∀ η : Schedule V, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.ScheduleEquivalent (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.strip (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.augment η)) η) ∧
    (∀ (η : Schedule V) i z, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.pubOutcome (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.augment η) i z = CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.potentialOutcome η i z) ∧
    (∀ η : Schedule V, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.pubTte (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.augment η) = CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte η) ∧
    (∀ (η : Schedule V) q r, pubAcquisitionLaw (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.augment η) q r = acquisitionLaw η q r) ∧
    (∀ (D : Design V) q r, AssignmentLaw D → AcquisitionLaw D q r → DesignIndependent D →
      ∀ η, (D η).map (pubRecordOf (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.augment η)) =
        ((CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.halfBernoulli V).prod (pubAcquisitionLaw (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.augment η) q r)).map
          (pubRecordOf (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.augment η)) ∧
        ∀ ω, pubRecordOf (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.augment η) ω = recordOf η ω) := by
  have hconv : CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.SnipeModelConventions
      (V := V) := hconv_of_gate
  have hacq (η : Schedule V) (q r : ℝ) :
      pubAcquisitionLaw
        (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.augment η) q r =
      acquisitionLaw η q r := by
    unfold pubAcquisitionLaw acquisitionLaw
    congr 1
    funext e
    simp only [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.augment,
      or_iff_left e.2]
  have hrecord (η : Schedule V) (ω : Assign V × Acq V) :
      pubRecordOf (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.augment η) ω =
      recordOf η ω := by
    simp only [pubRecordOf, recordOf,
      CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.pubOutcome_augment hconv]
  refine ⟨?_, ?_,
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.strip_augment_equivalent,
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.pubOutcome_augment hconv,
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.pubTte_augment hconv,
    hacq, ?_⟩
  · intro η d hη
    exact CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.augment_publishedClass
      hconv η d ((scheduleClass_iff_thin η d).mp hη)
  · intro ϑ d hϑ hdiag
    exact ⟨(scheduleClass_iff_thin _ d).mpr
      (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.strip_scheduleClass
        hconv ϑ d hϑ hdiag),
      CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.augment_strip_equivalent
        ϑ hϑ.1 hdiag⟩
  · intro D q r ha hH hi η
    constructor
    · rw [design_eq_noisyDesign D q r ha hH hi, hacq]
      rfl
    · exact hrecord η

end CausalSmith.Experimentation.NoisygraphTtePrecision

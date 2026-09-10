import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.HitFactorization
import Causalean.Stat.Minimax.MarkovKernelTransport
import Causalean.Stat.Minimax.MinimaxValue
import Mathlib.Probability.Decision.Risk.Basic

set_option linter.style.longLine false

/-! # Bernoulli nuisance deletion -/

open MeasureTheory

namespace CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

noncomputable section

-- @node: thm:nuisance-deletion-bernoulli
/-- Full and target-hit Bernoulli experiments have equal all-rule minimax risk
for every bounded target-only loss. -/
theorem nuisance_deletion_bernoulli {C n K : ℕ} [NeZero n] [NeZero K]
    (P : Measure (Schedule n)) (sampleLaw : Measure (Fin C → Schedule n))
    (labelLaw : Measure (Fin C → Fin K))
    (jointLaw : Measure ((Fin C → Schedule n) × (Fin C → Fin K)))
    (assignmentLaw : AssignmentKernel C K n)
    (p alpha : Fin K → ℝ)
    (counts m : Fin K → ℕ)
    (loss : {l : (Fin K → ℝ) → Fin K → ℝ // TargetOnlyLoss l})
    (h_iid : IidSchedules P sampleLaw)
    (h_isolated : IsolatedClusters sampleLaw)
    (h_labels : BernoulliLabelIid p labelLaw)
    (h_indep : BernoulliLabelScheduleIndep sampleLaw labelLaw jointLaw)
    (h_units : BernoulliUnits m P labelLaw assignmentLaw)
    (hmenu : WellFormedMenu n K m) :
    Measurable (reduceToHit (n := n) m) ∧
    Measurable (deleteHitLabel : HitRecord K n → LabelDeletedHitRecord n) ∧
    Measurable (fun O : Fin C → Record K n => fun c => reduceToHit m (O c)) ∧
    Measurable (fun O : Fin C → HitRecord K n => fun c => deleteHitLabel (O c)) ∧
    experimentMinimaxRisk (BoundedScheduleLawClass n)
      (fun Q => (regimeExperiment (C := C) Q p alpha counts m).1.1) (fun Q => exactSliceWelfare Q m) loss.1 =
    experimentMinimaxRisk (BoundedScheduleLawClass n)
      (fun Q => (regimeExperiment (C := C) Q p alpha counts m).1.2) (fun Q => exactSliceWelfare Q m) loss.1 ∧
    (∀ {Action : Type*} [MeasurableSpace Action] [StandardBorelSpace Action]
        (generalLoss : (Fin K → ℝ) → Action → ℝ),
      BoundedTargetLoss generalLoss →
      standardBorelExperimentMinimaxRisk (BoundedScheduleLawClass n)
        (fun Q => (regimeExperiment (C := C) Q p alpha counts m).1.1)
        (fun Q => exactSliceWelfare Q m) generalLoss =
      standardBorelExperimentMinimaxRisk (BoundedScheduleLawClass n)
        (fun Q => (regimeExperiment (C := C) Q p alpha counts m).1.2)
        (fun Q => exactSliceWelfare Q m) generalLoss) ∧
    (∀ {Action : Type*} [MeasurableSpace Action] [StandardBorelSpace Action]
        (generalLoss : (Fin K → ℝ) → Action → ℝ),
      BoundedTargetLoss generalLoss →
      standardBorelExperimentMinimaxRisk (BoundedScheduleLawClass n)
        (fun Q => (regimeExperiment (C := C) Q p alpha counts m).1.1)
        (fun Q => exactSliceWelfare Q m) generalLoss =
      standardBorelExperimentMinimaxRisk (BoundedScheduleLawClass n)
        (fun Q => deleteLabelsFromHitExperimentLaw
          (regimeExperiment (C := C) Q p alpha counts m).1.2)
        (fun Q => exactSliceWelfare Q m) generalLoss) := by sorry

end

end CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

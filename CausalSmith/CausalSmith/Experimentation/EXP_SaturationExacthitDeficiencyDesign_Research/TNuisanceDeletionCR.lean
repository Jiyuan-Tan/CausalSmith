import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Basic
import Causalean.Stat.Minimax.MarkovKernelTransport
import Causalean.Stat.Minimax.MinimaxValue

set_option linter.style.longLine false

/-! # Fixed-count label deletion -/

open MeasureTheory

namespace CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

noncomputable section

-- @node: thm:nuisance-deletion-cr
/-- Recording the exact-count assignments makes the randomized label vector
parameter-free and deletable without changing bounded target-only minimax risk. -/
theorem nuisance_deletion_cr {C n K : ℕ} [NeZero n] [NeZero K]
    (P : Measure (Schedule n)) (sampleLaw : Measure (Fin C → Schedule n))
    (labelLaw : Measure (Fin C → Fin K))
    (jointLaw : Measure ((Fin C → Schedule n) × (Fin C → Fin K)))
    (assignmentLaw : AssignmentKernel C K n)
    (p alpha : Fin K → ℝ)
    (counts m : Fin K → ℕ)
    (loss : {l : (Fin K → ℝ) → Fin K → ℝ // TargetOnlyLoss l})
    (h_iid : IidSchedules P sampleLaw)
    (h_isolated : IsolatedClusters sampleLaw)
    (h_labels : CrLabelVector counts labelLaw)
    (h_indep : CrLabelScheduleIndep sampleLaw labelLaw jointLaw)
    (h_slices : CrExactSlices m P labelLaw assignmentLaw)
    (hmenu : WellFormedMenu n K m) :
    experimentMinimaxRisk (BoundedScheduleLawClass n)
      (fun Q => (regimeExperiment (C := C) Q p alpha counts m).2.1) (fun Q => exactSliceWelfare Q m) loss.1 =
    experimentMinimaxRisk (BoundedScheduleLawClass n)
      (fun Q => (regimeExperiment (C := C) Q p alpha counts m).2.2) (fun Q => exactSliceWelfare Q m) loss.1 ∧
    ∀ {Action : Type*} [MeasurableSpace Action] [StandardBorelSpace Action]
        (generalLoss : (Fin K → ℝ) → Action → ℝ),
      BoundedTargetLoss generalLoss →
      standardBorelExperimentMinimaxRisk (BoundedScheduleLawClass n)
        (fun Q => (regimeExperiment (C := C) Q p alpha counts m).2.1)
        (fun Q => exactSliceWelfare Q m) generalLoss =
      standardBorelExperimentMinimaxRisk (BoundedScheduleLawClass n)
        (fun Q => (regimeExperiment (C := C) Q p alpha counts m).2.2)
        (fun Q => exactSliceWelfare Q m) generalLoss := by sorry

end

end CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

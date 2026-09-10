import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Basic
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Sequences

/-!
# Weak compactness of compact-space schedule laws

The paper uses Mathlib's compactness instance for probability measures on a
compact Borel space.  This is a thin named specialization, not a cited gate.
-/

open MeasureTheory

namespace CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

-- @node: lem:weak-compactness-compact-laws
/-- Borel probability laws on a compact Hausdorff Borel space form a compact
space for weak convergence. -/
lemma weak_compactness_schedule_laws {E : Type*} [MeasurableSpace E]
    [TopologicalSpace E] [T2Space E] [BorelSpace E] [CompactSpace E] :
    CompactSpace (ProbabilityMeasure E) :=
  inferInstance

end CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

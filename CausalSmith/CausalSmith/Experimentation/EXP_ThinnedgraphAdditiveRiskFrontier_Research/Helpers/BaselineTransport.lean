module
public import Causalean.Mathlib.MeasureTheory.WithDensityTransport
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BlockLawBasics

/-!
# Transport of the block baseline under translation
-/

public section

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Translation of a baseline law has exactly the translated cosine density.  [For the stated data and conditions](hyp:s), [the stated conclusion holds](goal). -/
-- @node: baseline_map_add_density
lemma baseline_map_add_density (s : ℝ) :
    (volume.withDensity (fun w => ENNReal.ofReal (cosSqDensity w))).map (fun w => w + s) =
      volume.withDensity (fun w => ENNReal.ofReal (cosSqDensity (w - s))) := by
  have ht := Causalean.Mathlib.MeasureTheory.map_withDensity_comp_measurableEquiv
    (MeasurableEquiv.addRight s) (measurePreserving_add_right volume s)
    (fun w => ENNReal.ofReal (cosSqDensity (w - s)))
  simpa [Function.comp_def] using ht

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier

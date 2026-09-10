import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.CondClasses
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! # Common-conull kernel pasting infrastructure -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory ProbabilityTheory Set

/-- A finite intersection of measurable conull sets is measurable and conull.  For the specified model objects, [the stated conditions](hyp:hS,hT,hSc,hTc), [the stated mathematical relationship holds](goal).
-/
-- @node: two_conull_inter
lemma two_conull_inter {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (S T : Set X) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hSc : mu Sᶜ = 0) (hTc : mu Tᶜ = 0) :
    MeasurableSet (S ∩ T) ∧ mu (S ∩ T)ᶜ = 0 := by
  refine ⟨hS.inter hT, ?_⟩
  rw [compl_inter]
  exact measure_union_null hSc hTc

end CausalSmith.SCM.PropensityLvSharpnessFrontier

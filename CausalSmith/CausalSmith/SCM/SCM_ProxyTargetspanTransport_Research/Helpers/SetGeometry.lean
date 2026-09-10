import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Order.LiminfLimsup
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Causalean.PO.ID.Partial.RandomSet.Hausdorff

/-! Real set geometry and varying-measure probability-rate predicates. -/

open MeasureTheory

namespace CausalSmith.SCM.ProxyTargetspanTransport

-- @node: def:euclidean-diameter
/-- [The confidence-set sequence, _hC](hyp:C,_hC) establish [the supremum of pairwise Euclidean distances between points of the set inside the unit interval](goal). -/
noncomputable def euclideanDiameter (C : Set ℝ) (_hC : C ⊆ Set.Icc (0 : ℝ) 1) : ℝ :=
  Metric.diam C
-- @realizes \operatorname{diam}_2(Euclidean diameter; empty set has diameter zero)
-- @realizes C(subset of [0,1]) @realizes \xi(real member) @realizes \zeta(real member)

/-- [The set](hyp:D) establish [the supplied set is contained in the closed unit interval](goal). -/
def IsUnitIntervalSubset (D : Set ℝ) : Prop :=
  D ⊆ Set.Icc (0 : ℝ) 1
-- @realizes D(carrier Set ℝ; subset of [0,1]; possibly empty)

/-- This abbreviation is used only with both sets nonempty, the domain on which the reused
real-valued Hausdorff construction agrees with the paper's formula. -/
-- @node: def:euclidean-hausdorff-distance
noncomputable def euclideanHausdorffDistance (C D : Set ℝ)
    (_hC : IsUnitIntervalSubset C) (_hD : IsUnitIntervalSubset D)
    (_hneC : C.Nonempty) (_hneD : D.Nonempty) : ℝ :=
  Causalean.PartialID.RandomSet.hausdorffDist C D
-- @realizes d_H(nonempty-set Euclidean Hausdorff distance)

/-- [The hA, hx](hyp:hA,hx) establish [a point in the first bounded set is no farther from the comparison set than the Hausdorff distance between the two sets](goal). -/
theorem infDist_le_randomSet_hausdorffDist_of_mem
    {A B : Set ℝ} {x : ℝ} (hA : Bornology.IsBounded A)
    (hx : x ∈ A) :
    Metric.infDist x B ≤ Causalean.PartialID.RandomSet.hausdorffDist A B := by
  have hbdd : BddAbove ((fun a : ℝ => Metric.infDist a B) '' A) :=
    ((Metric.lipschitz_infDist_pt B).isBounded_image hA).bddAbove
  have hxdir : Metric.infDist x B ≤
      Causalean.PartialID.RandomSet.directedHausdorff A B := by
    unfold Causalean.PartialID.RandomSet.directedHausdorff
    exact le_csSup hbdd ⟨x, hx, rfl⟩
  exact hxdir.trans (le_max_left _ _)

end CausalSmith.SCM.ProxyTargetspanTransport

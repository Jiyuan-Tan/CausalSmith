module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Basic
public import Causalean.Stat.Minimax.HonestConfidenceSet

/-! # Restricted random-set length support

Specialize the measurable random-set identity to the two-sample
expected-length functional and the parameter interval `[-1,1]`.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- Expected restricted length is the integral of pointwise inclusion probabilities.
The shared theorem interchanges the two integrals of the measurable indicator.  Under [the displayed assumptions and inputs](hyp:P,nS,nT,C,hgraph), [the stated conclusion holds](goal). -/
-- @node: expectedLength_eq_integral_inclusion
lemma expectedLength_eq_integral_inclusion (P : TransportLaw) (nS nT : ℕ)
    [IsFiniteMeasure (dataLaw P nS nT)] (C : TwoSample nS nT → Set ℝ)
    (hgraph : MeasurableSet {p : TwoSample nS nT × ℝ | p.2 ∈ C p.1}) :
    expectedLength P nS nT C =
      ∫ t in parameterSpace, (dataLaw P nS nT {ω | t ∈ C ω}).toReal := by
  exact Causalean.Stat.expected_restrictedSetVolume_eq_integral_inclusion
    (dataLaw P nS nT) C parameterSpace hgraph measurableSet_Icc
    (by simp [parameterSpace, Real.volume_Icc])

end CausalSmith.Stat.TransportCaceRoughnuisanceLength

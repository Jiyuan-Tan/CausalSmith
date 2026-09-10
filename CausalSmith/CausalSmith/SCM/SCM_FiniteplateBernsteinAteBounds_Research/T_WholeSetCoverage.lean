import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.Helpers.MomentReduction
import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.T_FiniteComplexityInference

/-! # Whole-identified-set finite-sample coverage -/

namespace CausalSmith.SCM.FiniteplateBernsteinAteBounds

open MeasureTheory

/-- A model-generated aggregate count vector has the literal coordinate counts. -/
def IsModelAggregate {Ω : Type*} [MeasurableSpace Ω]
    {m n : ℕ} {ε : ℝ} (P : Measure Ω) [IsProbabilityMeasure P]
    (M : HierarchicalPlateModel m n ε P) (Z : Ω → AggregateSpace m n) : Prop :=
  ∀ ω c, aggregateCount (Z ω) c = ∑ i, if M.C i ω = c then 1 else 0
  -- @realizes Z(aggregate count of the observed cluster counts)

/-- Exact count-law coverage implies coverage of the whole sharp identified
interval, uniformly over the hierarchical model class, including singleton
boundary fibers. -/
-- @node: prop:whole-set-coverage
theorem whole_set_coverage {Ω : Type*} [MeasurableSpace Ω]
    (m n : ℕ) (ε α : ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (M : HierarchicalPlateModel m n ε P) :
    0 < α → α < 1 →
    ∃ (b : CountIndex m → ℝ) (Z : Ω → AggregateSpace m n),
      IsModelAggregate P M Z ∧ b ∈ bernsteinMomentBody m ε ∧
      (∀ i c, Measure.map (M.C i) P {c} = ENNReal.ofReal (b c)) ∧
      ENNReal.ofReal (1 - α) ≤
        P {ω | b ∈ exactMultinomialRegion n α (Z ω)} ∧
      ENNReal.ofReal (1 - α) ≤
        P {ω | Set.Icc (lowerEndpoint m ε b) (upperEndpoint m ε b) ⊆
          wholeSetConfidenceSet m n ε α (Z ω)} := by
  sorry

end CausalSmith.SCM.FiniteplateBernsteinAteBounds

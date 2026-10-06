module
public import CausalSmith.Mathlib.Probability.PoissonUsableOccupancy
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.RelaxedPoissonBridge
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.BoundedRisk
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Depoissonization

/-! Normalization and fixed-sample risk transfer for relaxed Zeng intensities. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal NNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- For [the specified inputs and assumptions](hyp:d,a0,z,P₀), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def normalizedRelaxedZengLaw {d : ℕ} (a0 : ℝ)
    (z : Fin d → MarkedParam)
    (P₀ : Measure (RelaxedZengRecord d)) [IsProbabilityMeasure P₀] :
    ZengLaw (d + 1) :=
  ⟨normalizedFiniteMeasure (relaxedZengTable d a0 z) P₀, inferInstance⟩

/-- For [the specified inputs and assumptions](hyp:d,a0,z), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable instance normalizedRelaxedZengLaw_isProbabilityMeasure
    {d : ℕ} (a0 : ℝ) (z : Fin d → MarkedParam)
    (P₀ : Measure (RelaxedZengRecord d)) [IsProbabilityMeasure P₀] :
    IsProbabilityMeasure (normalizedRelaxedZengLaw a0 z P₀).1 :=
  (normalizedRelaxedZengLaw a0 z P₀).2

end CausalSmith.Stat.MarRareqLogfrontier

module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.PredictiveProductBridge
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.Concentration
public import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmConditioning

/-! Total-variation cost of conditioning the relaxed iid prior. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Causalean.Stat.Minimax.MomentMatchedMixture

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate

end CausalSmith.Stat.MarRareqLogfrontier

namespace CausalSmith.Stat.MarRareqLogfrontier

end CausalSmith.Stat.MarRareqLogfrontier

namespace CausalSmith.Stat.MarRareqLogfrontier
open Causalean.Stat
open Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate

private lemma measurableSet_iidRareGood_local {d : ℕ}
    (ν : Measure MarkedParam) (massRadius targetRadius : ℝ) :
    MeasurableSet {z : Fin d → MarkedParam |
      iidRareGood ν massRadius targetRadius z} := by
  change MeasurableSet
    ({z : Fin d → MarkedParam |
      |(∑ x, (z x).1) - d * ∫ t, t.1 ∂ν| < massRadius} ∩
    {z : Fin d → MarkedParam |
      |(∑ x, targetFunctional (z x)) -
        d * ∫ t, targetFunctional t ∂ν| < targetRadius})
  apply MeasurableSet.inter
  · exact measurableSet_lt (by fun_prop) measurable_const
  · exact measurableSet_lt (by
      unfold targetFunctional
      fun_prop) measurable_const

/-- For [the specified inputs and assumptions](hyp:d,a0,lam), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def relaxedCountKernel
    (d : ℕ) (a0 : ℝ) (lam : ℝ≥0) :
    Kernel (Fin d → MarkedParam)
      (((ℕ × ℕ) × ℕ) × (Fin d → ((ℕ × ℕ) × ℕ))) :=
  (Kernel.const (Fin d → MarkedParam)
    (relaxedDummyCountLaw d a0 lam)).prod
      (coordinatewiseFiniteKernel (markedPoissonKernel (lam : ℝ)) d)

/-- For [the specified inputs and assumptions](hyp:d,a0,lam), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable instance relaxedCountKernel_isMarkov
    (d : ℕ) (a0 : ℝ) (lam : ℝ≥0) :
    IsMarkovKernel (relaxedCountKernel d a0 lam) := by
  unfold relaxedCountKernel
  infer_instance

end CausalSmith.Stat.MarRareqLogfrontier

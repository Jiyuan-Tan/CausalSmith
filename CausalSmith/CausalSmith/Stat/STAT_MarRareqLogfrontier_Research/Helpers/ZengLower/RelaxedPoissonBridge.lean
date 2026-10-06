module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.FixedPoissonBridge
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.RelaxedTable
public import Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate

/-! Finite-intensity Poisson representation of the relaxed Zeng table. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram

/-- For [the specified inputs and assumptions](hyp:d,a0,z), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable instance relaxedZengTable_isFiniteMeasure
    (d : ℕ) (a0 : ℝ) (z : Fin d → MarkedParam) :
    IsFiniteMeasure (relaxedZengTable d a0 z) := by
  apply IsFiniteMeasure.mk
  simp [relaxedZengTable]

/-- For [the specified inputs and assumptions](hyp:d,a0,lam), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def relaxedDummyCountLaw (d : ℕ) (a0 : ℝ) (lam : ℝ≥0) :
    Measure ((ℕ × ℕ) × ℕ) :=
  ((poissonMeasure 0).prod
      (poissonMeasure (lam * (ENNReal.ofReal ((1 - d * a0) / 2)).toNNReal))).prod
    (poissonMeasure (lam * (ENNReal.ofReal ((1 - d * a0) / 2)).toNNReal))

end CausalSmith.Stat.MarRareqLogfrontier

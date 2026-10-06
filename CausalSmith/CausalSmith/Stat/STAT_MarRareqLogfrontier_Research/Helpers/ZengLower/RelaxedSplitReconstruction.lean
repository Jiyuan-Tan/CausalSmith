module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.ConditionedPredictiveTV
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.UnequalMassKL.Count
public import Causalean.Stat.Minimax.MarkovKernelTransport
-- private import
import all CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.ConditionedPredictiveTV
-- private import
import all CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.FixedPoissonBridge
-- private import
import all CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.RelaxedPoissonBridge

/-!
# Split-count sufficiency for the relaxed Zeng experiment

This module reconstructs the full relaxed histogram and then a uniformly
ordered raw Poisson sample from the split dummy/rare three-count statistic.
The reconstruction is parameter-free and remains exact when the dummy cell
has both treated-failure and control-failure mass.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Mathlib.Probability.Poisson.FinitePartition.UnequalMassKL
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram

/-- For [the specified inputs and assumptions](hyp:d,c), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def unpackRelaxedThreeCounts {d : ℕ}
    (c : Fin (d + 1) → ((ℕ × ℕ) × ℕ)) : RelaxedZengRecord d → ℕ
  | (x, true, true) => (c x).1.1
  | (x, true, false) => (c x).1.2
  | (x, false, false) => (c x).2
  | (_x, false, true) => 0

/-- For [the specified inputs and assumptions](hyp:d,c), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def unsplitRelaxedCounts {d : ℕ}
    (c : ((ℕ × ℕ) × ℕ) × (Fin d → ((ℕ × ℕ) × ℕ))) :
    RelaxedZengRecord d → ℕ :=
  unpackRelaxedThreeCounts
    ((MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (d + 1) => ((ℕ × ℕ) × ℕ)) (Fin.last d)).symm c)

/-- Given [the specified inputs and assumptions](hyp:d), [the stated mathematical conclusion holds](goal). -/
@[fun_prop]
lemma measurable_unsplitRelaxedCounts {d : ℕ} :
    Measurable (unsplitRelaxedCounts (d := d)) := by
  fun_prop

/-- For [the specified inputs and assumptions](hyp:d), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def relaxedSplitReconstructionKernel (d : ℕ) :
    Kernel (((ℕ × ℕ) × ℕ) × (Fin d → ((ℕ × ℕ) × ℕ)))
      (FiniteSample (RelaxedZengRecord d)) :=
  (histogramReconstructionKernel (RelaxedZengRecord d)).comap
      unsplitRelaxedCounts measurable_unsplitRelaxedCounts

/-- For [the specified inputs and assumptions](hyp:d), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable instance relaxedSplitReconstructionKernel_isMarkov (d : ℕ) :
    IsMarkovKernel (relaxedSplitReconstructionKernel d) := by
  unfold relaxedSplitReconstructionKernel
  infer_instance

end CausalSmith.Stat.MarRareqLogfrontier

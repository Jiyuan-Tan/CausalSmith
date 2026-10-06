module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.Kernels
public import Causalean.Mathlib.Probability.FiniteMarkovOscillation

set_option linter.style.longLine false

/-! # Finite Markov operators and oscillation contraction

This file contains the distribution/function duality needed for the disjoint-window PHIW
covariance calculation.  It is independent of the dependent trajectory carriers.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open Causalean.Mathlib.Probability.FiniteMarkovOscillation

/-- The manuscript future conditional-mean function
`P_b^gap P_e^k g_e`. -/
noncomputable def phiwFutureFunction {T nX nH : Nat}
    (M : RawPomdpExperiment T nX nH) (gap k : Nat) : JointState nX nH → ℝ :=
  markovOperatorIter (policyKernel M M.b) gap
    (markovOperatorIter (policyKernel M M.e) k (rewardRegression M))

end CausalSmith.Stat.PomdpLatentOverlapMinimax

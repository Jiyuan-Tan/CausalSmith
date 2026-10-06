module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.Estimator
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.LowerPairs

/-! # Score-threshold overlap regret — quantile and open question

The concrete potential-outcome law uses Mathlib measures.
The abstract POSystem and strict-overlap ATE model have different scope.
Product experiments match the paper sampling model; lower-pair proofs
reuse Causalean chi-square and total variation lemmas.
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory
open scoped BigOperators ENNReal

-- @node: def:regret-quantile
/-- Minimax regret quantile at confidence level δ. -/
noncomputable def minimaxRegretQuantile (α γ θ : ℝ) (n : ℕ) (δ : {δ : ℝ // δ ∈ Set.Ioo (0:ℝ) (1/2)}) : ℝ := -- @realizes delta(confidence δ∈(0,1/2) at type level)
  ⨅ Φ : {Φ : Learner n // LearnerClass n Φ},
    sInf {q : ℝ | ∀ Pe : {Pe : RowLaw × (ℝ → ℝ) // LawClass α γ θ n Pe.1 Pe.2},
      (experiment Pe.1.1 n).real
        {du | regret (Pe.1.1.toWellFormedLaw Pe.2.wf Pe.2.bounded)
          (measurablePolicy (fun x => Φ.1 Pe.1.2 du.1 du.2 x)) > q} ≤ δ.1} -- @realizes Qndelta(inf learner, inf valid quantile)

-- @node: def:quantile-handle
/-- Descriptive proof-strategy handle; this is not an asserted bound. -/
def orderedChainQuantileHandle : _root_.String :=
  "Apply an ordered-threshold mixture-supermartingale or empirical-Bernstein argument to localizedProcess S_a, then pair it with confidence-indexed same-logger localPair and highPair alternatives while preserving the global envelope." -- @realizes quantileHandle(ordered-chain confidence strategy)

-- @node: oeq:sharp-regret-quantile
/-- Open question carrier; no witness or theorem is asserted. -/
def SharpRegretQuantileQuestion : _root_.String :=
  "For each fixed theta>0, determine the sharp joint dependence of Q_(n,delta) on n, delta, alpha, gamma, theta over a nondegenerate confidence range. Certify it with a matching ordered-chain upper construction and same-class confidence-indexed lower alternatives for fixed-logger randomized learners, or give a counterexample delimiting the attainable range. The obstruction is a localized exponential maximal inequality for all four ordered chains with loss-indexed variance, fixed-support branches, and arbitrary zero-effect mass. The established partial bracket is c*(log(1/delta)/n)^r <= Q_(n,delta) <= C*(delta^(-1/2)/n)^r for exp(-c0*n) <= delta <= delta0. This string states an unresolved problem and does not assert a sharp rate, criterion, witness, or theorem."

end CausalSmith.Stat.ScorethresholdOverlapRegret

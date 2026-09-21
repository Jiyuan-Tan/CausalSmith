/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.ATE.InfluenceFunction
public import Causalean.Estimation.ATE.Remainder
public import Causalean.Estimation.ATE.Score.AIPWScoreL2
public import Causalean.Estimation.OrthogonalMoments.AIPWInstance
public import Causalean.Stat.Sample
public import Causalean.Stat.SampleSplit
public import Causalean.Stat.CLT.AsymptoticLinearity
public import Causalean.Stat.SampleSplit.PartialFoldCLT
public import Causalean.Stat.Limit.Convergence
public import Causalean.Stat.SampleSplit.FoldBEmpiricalProcess

/-! # One-shot ATE DML estimator

Defines `dmlEstimator`, the fold-B empirical average of the AIPW pseudo-outcome
for a one-shot sample split. Asymptotic linearity and normality are proved in
the two downstream files of this directory.
-/

@[expose] public section
namespace Causalean
namespace Estimation
namespace ATE

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO Causalean.Stat
open BackdoorEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
/-- For [a potential-outcome system with a measurable covariate space](hyp:P), [a
back-door estimation system](hyp:S), [an independent and identically distributed sample of
observed covariate, treatment, and outcome triples from its observable data law](hyp:sample),
[a one-shot split of that sample](hyp:split), [an outcome-regression learner indexed by sample
size and population realization](hyp:μ_hat), [a propensity-score learner indexed in the same
way](hyp:e_hat), and [a nonnegative integer sample-size index](hyp:n), the [one-shot DML/AIPW
estimator of the back-door average treatment effect](goal) assigns to each population realization
the average AIPW moment over that index's estimation fold.

One-shot DML / AIPW estimator of the back-door ATE
(`def:est-dml-ate`).

Inputs:
* `S`         — back-door estimation system carrying the value-space
                truth `(μ_val, e_val)`.
* `sample`    — i.i.d. sample of triples `(X, A, Y) ∼ P_Z`.
* `split`     — one-shot split of the sample.
* `μ_hat`     — outcome regression estimator at horizon `n`.
* `e_hat`     — propensity estimator at horizon `n`.

Output: empirical mean over `B(n)` of `m_AIPW( η̂(n), Zᵢ, 0 )`.
Equivalently, the empirical AIPW pseudo-outcome. -/
noncomputable def dmlEstimator
    (S : BackdoorEstimationSystem P γ)
    (sample : IIDSample P.Ω (γ × Bool × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    (μ_hat : ℕ → P.Ω → (Bool → γ → ℝ))
    (e_hat : ℕ → P.Ω → (γ → ℝ))
    (n : ℕ) : P.Ω → ℝ :=
  fun ω =>
    ((split.foldB n).card : ℝ)⁻¹ *
      ∑ i ∈ split.foldB n,
        aipwMoment (sample.Z i ω) (μ_hat n ω) (e_hat n ω) 0

end ATE
end Estimation
end Causalean

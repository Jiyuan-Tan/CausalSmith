/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# DR-Learner CATE estimator and its oracle

This file defines the one-shot DR-Learner CATE estimator and its oracle
counterpart, as defined in
`doc/basic_concepts/po/estimation/dr_learner_cate.tex`
(`def:est-cate-dr-learner`):

    τ̂^{DR}_n(x) := Ê_{n,B}{ φ̂_n(Z) | X = x },
    τ̃_n(x)     := Ê_{n,B}{ φ_0(Z) | X = x },
    R^*_n(x)^2 := E[ (τ̃_n(x) - τ_0(x))^2 ].

The second-stage regression operator `Ê_{n,B}` is supplied as an abstract
`SecondStageOperator P.Ω P.μ γ`, and the pseudo-outcomes `phi_eta` / `phi₀`
come from `Causalean.Estimation.CATE.Core.PseudoOutcome`.

The declarations are thin definitional wrappers around the abstract
second-stage regression operator.
-/

import Causalean.Estimation.CATE.Core.PseudoOutcome
import Causalean.Estimation.OrthogonalMoments.SecondStageOperator

/-! # DR-Learner CATE Estimator

This file defines the doubly robust learner for conditional average treatment
effects using an abstract second-stage regression operator. It also defines the
oracle version `drOracleEstimator` that uses the true pseudo-outcome, the
associated pointwise risk scale `drOracleRiskScale`, and the unfolding lemma
`drOracleEstimator_eq_oracleEstimator` for connecting the CATE-specific API to
the generic second-stage-operator API. -/

namespace Causalean
namespace Estimation
namespace CATE

open MeasureTheory ProbabilityTheory Filter Topology
  Causalean.PO Causalean.Estimation.ATE Causalean.Estimation.OrthogonalMoments

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- For [a population outcome system](hyp:P) and [a covariate space](hyp:γ), given [a CATE estimation system](hyp:_S), [a second-stage regression
operator](hyp:op), [a sequence of estimated nuisance vectors indexed by sample size and
sample realization](hyp:η_hat), [a sample size](hyp:n), [a sample realization](hyp:ω), and
[a covariate query point](hyp:x), the [DR-Learner CATE estimator](goal) is that operator,
at the stated sample size, realization, and query point, applied to the uncentered augmented
inverse-probability-weighted pseudo-outcome formed with the corresponding estimated nuisance vector.

**DR-Learner CATE estimator** at `x` (Def `def:est-cate-dr-learner`, `τ̂^{DR}_n(x)`).

The system parameter `_S` is kept in the signature for API symmetry with
`drOracleEstimator` / `drOracleRiskScale`, even though the estimator itself
only depends on `η_hat`. -/
noncomputable def drLearnerEstimator
    (_S : CATEEstimationSystem P γ)
    (op : SecondStageOperator P.Ω P.μ γ)
    (η_hat : ℕ → P.Ω → NuisanceVec γ)
    (n : ℕ) (ω : P.Ω) (x : γ) : ℝ :=
  op.evalAt n ω (fun z => phi_eta z (η_hat n ω)) x

/-- For [a population outcome system](hyp:P) and [a covariate space](hyp:γ), given [a CATE estimation system](hyp:S), [a second-stage regression operator](hyp:op),
[a sample size](hyp:n), [a sample realization](hyp:ω), and [a covariate query point](hyp:x),
the [oracle DR-Learner estimator](goal) is the operator at that sample size, realization,
and query point applied to the true augmented inverse-probability-weighted pseudo-outcome.

**Oracle DR-Learner** at `x` (Def `def:est-cate-dr-learner`, `τ̃_n(x)`). The oracle
counterpart of `drLearnerEstimator` substitutes the true pseudo-outcome `φ_0` (built from
the truth nuisance `η₀` carried by the back-door substrate of `S`) in place of the estimated
pseudo-outcome. -/
noncomputable def drOracleEstimator
    (S : CATEEstimationSystem P γ)
    (op : SecondStageOperator P.Ω P.μ γ)
    (n : ℕ) (ω : P.Ω) (x : γ) : ℝ :=
  op.evalAt n ω (fun z => phi₀ S z) x

/-- For [a population outcome system](hyp:P) and [a covariate space](hyp:γ), given [a CATE estimation system](hyp:S), [a second-stage regression operator](hyp:op),
[a covariate query point](hyp:x), and [a sample size](hyp:n), the [oracle pointwise risk
scale](goal) is the square root of the population expectation of the squared difference
between the oracle DR-Learner at that point and the system's conditional average treatment-effect target.

**Oracle pointwise risk scale** `R^*_n(x)` (Def `def:est-cate-dr-learner`). This specializes
`SecondStageOperator.oracleRiskScale` to the AIPW pseudo-outcome `φ_0` and the value-space CATE target `τ_val`:

    R^*_n(x) := sqrt( ∫ (op.evalAt n ω φ_0 x - τ_val x)^2 ∂P.μ ).

It is the L²(P.μ) deviation of the oracle DR-Learner from the CATE target at
the fixed query point `x`, treated as a deterministic function of `n`. -/
noncomputable def drOracleRiskScale
    (S : CATEEstimationSystem P γ)
    (op : SecondStageOperator P.Ω P.μ γ)
    (x : γ) (n : ℕ) : ℝ :=
  op.oracleRiskScale (fun z => phi₀ S z) S.τ_val x n

/-- For [a CATE estimation system](hyp:S) and [a second-stage operator](hyp:op), [the oracle
DR-learner estimator built from S and op equals the abstract oracle estimator of op applied
to the true pseudo-outcome `φ_0`](goal). -/
lemma drOracleEstimator_eq_oracleEstimator
    (S : CATEEstimationSystem P γ)
    (op : SecondStageOperator P.Ω P.μ γ) :
    drOracleEstimator S op = op.oracleEstimator (fun z => phi₀ S z) := rfl

end CATE
end Estimation
end Causalean

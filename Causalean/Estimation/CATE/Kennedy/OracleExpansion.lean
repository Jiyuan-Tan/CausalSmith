/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Assumption-driven oracle-expansion wrappers for the DR-Learner

This file specializes the abstract `Stable` implication to the AIPW
pseudo-outcomes `phi_eta` / `phi₀` and combines its assumed expansion with an
assumed negligible smoothed-bias term. It does not establish stability or the
smoothed-bias rate from primitive learner conditions.

Two declarations are provided:

* `dr_oracle_expansion_of_stable` — direct specialisation of
  `Causalean.Estimation.OrthogonalMoments.Stable.isLittleOp` to the AIPW
  pseudo-outcomes.
* `dr_oracle_efficient_of_stable_of_smoothed_bias` — bookkeeping corollary from
  assumed stability and an assumed `o_p(R*_n(x))` smoothed-bias term.

The proofs specialize the abstract second-stage expansion and combine
stochastic-order remainders.
-/

module
public import Causalean.Estimation.CATE.Kennedy.DRLearner
public import Causalean.Estimation.CATE.Core.ConditionalBias
public import Causalean.Estimation.ATE.Remainder.Identity
public import Causalean.Estimation.OrthogonalMoments.SecondStageOperator
public import Causalean.Stat.Limit.Convergence
public import Causalean.Stat.SampleSplit.OneShot

/-! # DR-Learner Oracle Bookkeeping under Stability

This file records consequences of caller-supplied abstract stability for the
doubly robust pseudo-outcomes used for conditional average treatment effects.
`dr_oracle_expansion_of_stable` specializes the expansion already contained in
`Stable`; `dr_oracle_efficient_of_stable_of_smoothed_bias` additionally combines
it with a caller-supplied negligible smoothed-bias rate. -/

public section

namespace Causalean
namespace Estimation
namespace CATE

open MeasureTheory ProbabilityTheory Filter Topology
  Causalean.PO Causalean.Stat Causalean.Estimation.ATE Causalean.Estimation.OrthogonalMoments

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- **DR-Learner expansion conditional on abstract stability.** Fix a CATE estimation system under
[the back-door causal assumptions](hyp:_hA), a query point `x`, and a sequence of estimated
nuisance vectors `η_hat`. Suppose [the abstract second-stage regression operator `op` is stable
at `x` with respect to a distance `d_n`, meaning the caller-supplied bias-identification
predicate `BiasIdent` correctly separates the operator-level discrepancy between the
estimated-nuisance and true pseudo-outcomes into a bias term plus a negligible
remainder](hyp:hStab); [`d_n` converges to zero in probability](hyp:hCons); and [the contrast
between the AIPW pseudo-outcome built from `η_hat` and the true pseudo-outcome is identified,
through `BiasIdent`, with the closed-form conditional bias `condBias(η_hat, η₀)`](hyp:hBias).
Then [the DR-Learner CATE estimator, minus its oracle counterpart, minus the operator applied to
that closed-form bias, equals `o_p(R*_n(x))`, where `R*_n(x)` is the oracle risk scale at
`x`](goal).

This wrapper does not prove the expansion from primitive learner conditions:
the operator-level conclusion is already the implication supplied by `hStab`.
It only instantiates that implication with the AIPW pseudo-outcomes and closed-form
bias. -/
theorem dr_oracle_expansion_of_stable
    (S : CATEEstimationSystem P γ)
    (_hA : S.toPOBackdoorSystem.Assumptions)
    (op : SecondStageOperator P.Ω P.μ γ)
    (η_hat : ℕ → P.Ω → NuisanceVec γ)
    (x : γ)
    (d_n : ℕ → P.Ω → ℝ)
    (BiasIdent :
      (ℕ → P.Ω → γ × Bool × ℝ → ℝ) →
      (γ × Bool × ℝ → ℝ) →
      (ℕ → P.Ω → γ → ℝ) → Prop)
    (hStab : Stable op S.τ_val d_n x BiasIdent)
    (hCons : Tendsto_inProb d_n (fun _ => 0) P.μ)
    (hBias : BiasIdent
              (fun n ω z => phi_eta z (η_hat n ω))
              (fun z => phi₀ S z)
              (fun n ω u => condBias (η_hat n ω)
                            S.toBackdoorEstimationSystem.η₀ u)) :
    IsLittleOp
      (fun n ω =>
        drLearnerEstimator S op η_hat n ω x
          - drOracleEstimator S op n ω x
          - op.evalAt n ω
              (fun z => condBias (η_hat n ω)
                          S.toBackdoorEstimationSystem.η₀ z.1) x)
      (fun n => drOracleRiskScale S op x n) P.μ := by
  unfold drLearnerEstimator drOracleEstimator drOracleRiskScale
  exact Causalean.Estimation.OrthogonalMoments.Stable.isLittleOp op S.τ_val x d_n
    (fun n ω z => phi_eta z (η_hat n ω))
    (fun z => phi₀ S z)
    (fun n ω u => condBias (η_hat n ω) S.toBackdoorEstimationSystem.η₀ u)
    BiasIdent hStab hCons hBias

/-- **DR-Learner oracle efficiency from assumed stability and smoothed-bias negligibility.** Under
[the back-door causal assumptions](hyp:hA) and the same operator-stability, consistency, and
bias-identification hypotheses as `dr_oracle_expansion_of_stable` —
[`op` is stable at `x` w.r.t. a distance `d_n`, via the bias-identification predicate
`BiasIdent`](hyp:hStab), [`d_n` converges to zero in probability](hyp:hCons), and [the AIPW
pseudo-outcome contrast is identified with the closed-form conditional bias `condBias(η_hat,
η₀)`](hyp:hBias) — if in addition [that smoothed conditional-bias term, the operator applied to
`condBias(η_hat, η₀)` at `x`, is itself `o_p(R*_n(x))`](hyp:hSmoothedBias), then [the DR-Learner
CATE estimator is oracle-efficient at `x`: it differs from its oracle counterpart by
`o_p(R*_n(x))`](goal).

This is an arithmetic bookkeeping corollary. It does not derive `hStab` or
`hSmoothedBias`; both scientific rate inputs are assumptions of the theorem. -/
theorem dr_oracle_efficient_of_stable_of_smoothed_bias
    (S : CATEEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (op : SecondStageOperator P.Ω P.μ γ)
    (η_hat : ℕ → P.Ω → NuisanceVec γ)
    (x : γ)
    (d_n : ℕ → P.Ω → ℝ)
    (BiasIdent :
      (ℕ → P.Ω → γ × Bool × ℝ → ℝ) →
      (γ × Bool × ℝ → ℝ) →
      (ℕ → P.Ω → γ → ℝ) → Prop)
    (hStab : Stable op S.τ_val d_n x BiasIdent)
    (hCons : Tendsto_inProb d_n (fun _ => 0) P.μ)
    (hBias : BiasIdent
              (fun n ω z => phi_eta z (η_hat n ω))
              (fun z => phi₀ S z)
              (fun n ω u => condBias (η_hat n ω)
                            S.toBackdoorEstimationSystem.η₀ u))
    (hSmoothedBias : IsLittleOp
      (fun n ω => op.evalAt n ω
        (fun z => condBias (η_hat n ω)
                    S.toBackdoorEstimationSystem.η₀ z.1) x)
      (fun n => drOracleRiskScale S op x n) P.μ) :
    IsLittleOp
      (fun n ω => drLearnerEstimator S op η_hat n ω x
                    - drOracleEstimator S op n ω x)
      (fun n => drOracleRiskScale S op x n) P.μ := by
  have hExp :=
    dr_oracle_expansion_of_stable S hA op η_hat x d_n BiasIdent hStab hCons hBias
  have hrn_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ drOracleRiskScale S op x n :=
    Filter.Eventually.of_forall (fun n => by
      unfold drOracleRiskScale SecondStageOperator.oracleRiskScale
      exact Real.sqrt_nonneg _)
  have hSum :=
    IsLittleOp.add_eventually_nonneg_rate (μ := P.μ) hrn_nonneg hExp hSmoothedBias
  convert hSum using 1
  funext n ω
  ring

end CATE
end Estimation
end Causalean

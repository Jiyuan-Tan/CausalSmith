/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.OrthogonalMoments.DMLChernozhukov
public import Causalean.Stat.SampleSplit.KFold

/-! # Linear-score DML estimators

This file defines the K-fold oracle one-step estimator and the feasible
one-shot and K-fold estimators for affine scores. The feasible estimators solve
their cross-fitted empirical moment equations and therefore use only observed
samples and fitted nuisances. -/

@[expose] public section

namespace Causalean
namespace Estimation
namespace OrthogonalMoments

open Causalean.Stat

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {H : Type*} [AddCommGroup H] [Module ℝ H]

/-- For [a general moment system](hyp:M), [an i.i.d. sample](hyp:sample), [a K-fold
split](hyp:split), [fold-specific nuisance fits](hyp:η_hat), and [a sample-size
index](hyp:n), the [K-fold oracle one-step DML estimator](goal) evaluates every
fold's score at the true target and rescales the fold-averaged score by the true
supplied linearization scale.

This object is a proof linearization, not a feasible statistic: it uses both
`M.θ₀` and `M.linScaleInv`. -/
noncomputable def crossFitOneStepOracleDML
    (M : GeneralMoment Ω μ Z P_Z H)
    (sample : IIDSample Ω Z μ P_Z) {K : ℕ}
    (split : KFoldSplit sample K)
    (η_hat : ℕ → Fin K → Ω → H)
    (n : ℕ) : Ω → ℝ :=
  fun ω =>
    M.θ₀ - M.linScaleInv *
      ((K : ℝ)⁻¹ *
        ∑ k : Fin K,
          ((split.fold n k).card : ℝ)⁻¹ *
            ∑ i ∈ split.fold n k, M.m (η_hat n k ω) (sample.Z i ω) M.θ₀)

/-- For [an affine moment system](hyp:M), [an i.i.d. sample](hyp:sample), [a
one-shot sample split](hyp:split), [a nuisance fit trained on the complementary
fold](hyp:η_hat), and [a sample-size index](hyp:n), the [feasible linear-score
DML estimator](goal) is [minus the inverse empirical coefficient mean times the
empirical constant-term mean](step:1).

It is the exact scalar solution of the evaluation-fold empirical moment
equation `P_B[m_a(η̂) θ + m_b(η̂)] = 0`; neither the true target nor the
supplied linearization scale enters its value. -/
noncomputable def feasibleLinearDML
    (M : LinearMoment Ω μ Z P_Z H)
    (sample : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit sample)
    (η_hat : ℕ → Ω → H)
    (n : ℕ) : Ω → ℝ :=
  fun ω =>
    -((((split.foldB n).card : ℝ)⁻¹ *
        ∑ i ∈ split.foldB n, M.m_a (η_hat n ω) (sample.Z i ω))⁻¹) *
      (((split.foldB n).card : ℝ)⁻¹ *
        ∑ i ∈ split.foldB n, M.m_b (η_hat n ω) (sample.Z i ω))

/-- For [an affine moment system](hyp:M), [an i.i.d. sample](hyp:sample), [a
K-fold split](hyp:split), [fold-specific complementary-sample nuisance
fits](hyp:η_hat), and [a sample-size index](hyp:n), the [feasible K-fold DML2
estimator](goal) is [minus the inverse fold-averaged empirical coefficient times
the fold-averaged empirical constant term](step:1).

This is the exact solution of the fold-averaged affine score equation from
Definitions 3.1--3.2 of Chernozhukov et al. (2018). -/
noncomputable def feasibleCrossFitLinearDML
    (M : LinearMoment Ω μ Z P_Z H)
    (sample : IIDSample Ω Z μ P_Z) {K : ℕ}
    (split : KFoldSplit sample K)
    (η_hat : ℕ → Fin K → Ω → H)
    (n : ℕ) : Ω → ℝ :=
  fun ω =>
    -(((K : ℝ)⁻¹ * (∑ k : Fin K,
      ((split.fold n k).card : ℝ)⁻¹ *
        ∑ i ∈ split.fold n k, M.m_a (η_hat n k ω) (sample.Z i ω)))⁻¹) *
      ((K : ℝ)⁻¹ * (∑ k : Fin K,
        ((split.fold n k).card : ℝ)⁻¹ *
          ∑ i ∈ split.fold n k, M.m_b (η_hat n k ω) (sample.Z i ω)))

end OrthogonalMoments
end Estimation
end Causalean

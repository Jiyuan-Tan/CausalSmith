module

public import Causalean.Stat.GMM.SmoothFeasibleGeneral

/-!
# Finite-sample smooth feasible-GMM quantities

This module defines the sample Jacobian, normalized moment, and first-order-condition residual
used by the bootstrap theory for smooth feasible GMM.
-/

@[expose] public section

namespace Causalean.Stat

open Causalean.Stat ContinuousLinearMap Filter MeasureTheory ProbabilityTheory Topology
open scoped BigOperators RealInnerProductSpace Topology

noncomputable section

variable {Omega X E F : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
  {mu : Measure Omega} {P : Measure X}

/-- For [smooth GMM regularity](hyp:reg), [a parameter](hyp:theta), and [a finite data
vector](hyp:data), [the sample-function GMM Jacobian](goal) is given by [the average of the
observationwise moment derivatives](step:1). -/
def gmmSampleJacobianFn {prob : GMMProblem (E := E) (F := F) P}
    (reg : SmoothGMomentRegularity prob) (theta : E)
    {n : ℕ} (data : Fin n → X) : E →L[ℝ] F :=
  Causalean.Stat.finMean (fun i ↦ reg.deriv theta (data i))

/-- For [a GMM problem](hyp:prob), [a parameter](hyp:theta), and [a finite data vector](hyp:data),
[the sample-function normalized moment](goal) is given by [the moment sum divided by the square
root of the sample size](step:1). -/
def gmmNormalizedMomentFn (prob : GMMProblem (E := E) (F := F) P)
    (theta : E) {n : ℕ} (data : Fin n → X) : F :=
  (Real.sqrt (n : ℝ))⁻¹ • ∑ i, prob.g theta (data i)

/-- For [a GMM problem and smooth regularity](hyp:prob,reg), [an estimated parameter](hyp:theta),
[an estimated weight](hyp:W), and [a finite data vector](hyp:data), [the normalized feasible-GMM
first-order-condition residual](goal) is given by [applying the empirical Jacobian adjoint and
estimated weight to the normalized moment](step:1). -/
def feasibleGMMFOCResidualFn
    (prob : GMMProblem (E := E) (F := F) P)
    (reg : SmoothGMomentRegularity prob) (theta : E) (W : F →L[ℝ] F)
    {n : ℕ} (data : Fin n → X) : E :=
  (adjoint (gmmSampleJacobianFn reg theta data) ∘L W)
  (gmmNormalizedMomentFn prob theta data)

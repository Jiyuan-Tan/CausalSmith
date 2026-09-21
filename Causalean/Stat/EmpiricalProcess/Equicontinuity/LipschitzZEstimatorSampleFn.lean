/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.CLT.SampleFnEstimator
public import Causalean.Stat.EmpiricalProcess.Equicontinuity.LipschitzZEstimator

/-! # Lipschitz Z-estimators defined on finite sample vectors

This module specializes the Lipschitz Z-estimator route to estimators implemented
as functions of the observed `Fin n` sample vector, following the generic
sample-function interface.
-/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Sample-function Lipschitz Z-estimator linearization (van der Vaart 1998,
Theorem 5.21).** For [a score](hyp:ψ), [target](hyp:θ₀), [population law](hyp:P),
[sampling law](hyp:μ), [iid sample](hyp:S), [finite-sample estimator](hyp:est),
[nonnegative envelope](hyp:L), [score and envelope measurability](hyp:hψmeas,hLmeas),
[envelope nonnegativity and square integrability](hyp:hL,hL2), [a positive radius](hyp:hδ₀), [Lipschitz
control on that ball](hyp:hLip), [identification](hyp:hIdentification), [finite
variance](hyp:hVar), [invertible derivative](hyp:J), [population derivative
identity](hyp:hDeriv), [consistency](hyp:hConsistent), and [an approximate
sample root](hyp:hMoment), [the estimator evaluated on the observed sample
vector has the usual asymptotic-linear representation](goal). -/
theorem zEstimator_asymLinear_of_lipschitz_of_sampleFn
    (ψ : E → X → E) (θ₀ : E) (P : Measure X) [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P) (est : (n : ℕ) → (Fin n → X) → E)
    (L : X → ℝ)
    (hψmeas : ∀ θ, Measurable (ψ θ)) (hLmeas : Measurable L)
    (hL : ∀ x, 0 ≤ L x) (hL2 : Integrable (fun x => L x ^ 2) P)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hLip : ∀ θ ∈ Metric.closedBall θ₀ δ₀, ∀ η ∈ Metric.closedBall θ₀ δ₀, ∀ z,
      ‖ψ θ z - ψ η z‖ ≤ L z * ‖θ - η‖)
    (hIdentification : ∫ x, ψ θ₀ x ∂P = 0)
    (hVar : Integrable (fun x => ‖ψ θ₀ x‖ ^ 2) P)
    (J : E ≃L[ℝ] E)
    (hDeriv : HasFDerivAt (fun θ => ∫ x, ψ θ x ∂P)
      J.toContinuousLinearMap θ₀)
    (hConsistent : ∀ ε > 0,
      Tendsto (fun n => μ {ω |
        ε < ‖est n (S.sampleVector n ω) - θ₀‖}) atTop (𝓝 0))
    (hMoment : IsLittleOp
      (fun n ω => ‖(Real.sqrt (n : ℝ))⁻¹ •
        ∑ i ∈ Finset.range n,
          ψ (est n (S.sampleVector n ω)) (S.Z i ω)‖)
      (fun _ => (1 : ℝ)) μ) :
    IsAsymLinearVec (E := E) (fun n ω => est n (S.sampleVector n ω)) θ₀
      (fun x => -(J.symm (ψ θ₀ x))) S (fun n => Finset.range n) :=
  zEstimator_asymLinear_of_lipschitz ψ θ₀ P S L hψmeas hLmeas hL hL2
    hδ₀ hLip hIdentification hVar J hDeriv
    (fun n ω => est n (S.sampleVector n ω)) hConsistent hMoment

/-- **Sample-function Lipschitz Z-estimator Gaussian limit (van der Vaart 1998,
Theorem 5.21).** For [a score](hyp:ψ), [target](hyp:θ₀), [population law](hyp:P),
[sampling law](hyp:μ), [iid sample](hyp:S), [finite-sample estimator](hyp:est),
[nonnegative envelope](hyp:L), [score and envelope measurability](hyp:hψmeas,hLmeas),
[envelope nonnegativity and square integrability](hyp:hL,hL2), [a positive radius](hyp:hδ₀), [Lipschitz
control on that ball](hyp:hLip), [identification](hyp:hIdentification), [finite
variance](hyp:hVar), [invertible derivative](hyp:J), [population derivative
identity](hyp:hDeriv), [consistency](hyp:hConsistent), [an approximate sample
root](hyp:hMoment), and [rescaled-estimator measurability](hyp:hEstMeas), [the
rescaled estimator evaluated on the observed sample vector converges to its
influence-function Gaussian law](goal). -/
theorem zEstimator_tendsto_normal_of_lipschitz_of_sampleFn
    (ψ : E → X → E) (θ₀ : E) (P : Measure X) [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P) (est : (n : ℕ) → (Fin n → X) → E)
    (L : X → ℝ)
    (hψmeas : ∀ θ, Measurable (ψ θ)) (hLmeas : Measurable L)
    (hL : ∀ x, 0 ≤ L x) (hL2 : Integrable (fun x => L x ^ 2) P)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hLip : ∀ θ ∈ Metric.closedBall θ₀ δ₀, ∀ η ∈ Metric.closedBall θ₀ δ₀, ∀ z,
      ‖ψ θ z - ψ η z‖ ≤ L z * ‖θ - η‖)
    (hIdentification : ∫ x, ψ θ₀ x ∂P = 0)
    (hVar : Integrable (fun x => ‖ψ θ₀ x‖ ^ 2) P)
    (J : E ≃L[ℝ] E)
    (hDeriv : HasFDerivAt (fun θ => ∫ x, ψ θ x ∂P)
      J.toContinuousLinearMap θ₀)
    (hConsistent : ∀ ε > 0,
      Tendsto (fun n => μ {ω |
        ε < ‖est n (S.sampleVector n ω) - θ₀‖}) atTop (𝓝 0))
    (hMoment : IsLittleOp
      (fun n ω => ‖(Real.sqrt (n : ℝ))⁻¹ •
        ∑ i ∈ Finset.range n,
          ψ (est n (S.sampleVector n ω)) (S.Z i ω)‖)
      (fun _ => (1 : ℝ)) μ)
    (hEstMeas : ∀ n, AEMeasurable
      (IsAsymLinearVec.rescaledEstimator
        (fun m ω => est m (S.sampleVector m ω)) θ₀
        (fun m => Finset.range m) n) μ) :
    Tendsto (β := ProbabilityMeasure E)
      (fun n => ⟨μ.map
        (IsAsymLinearVec.rescaledEstimator
          (fun m ω => est m (S.sampleVector m ω)) θ₀
          (fun m => Finset.range m) n),
        Measure.isProbabilityMeasure_map (hEstMeas n)⟩)
      atTop
      (𝓝 ⟨gaussianLimit
          ((J.symm.continuous.measurable.comp (hψmeas θ₀)).neg)
          (show Integrable (fun x => ‖-(J.symm (ψ θ₀ x))‖ ^ 2) P from by
            letI : IsProbabilityMeasure P := by
              rw [← S.law]
              exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
            let reg := zEstimatorRegularityOfLipschitz ψ θ₀ P L hψmeas hLmeas
              hL hL2 hδ₀ hLip hIdentification hVar J hDeriv
            have hi := integrable_sq_zEstimatorInfluence ψ θ₀ P reg
            change Integrable (fun x => ‖-(J.symm (ψ θ₀ x))‖ ^ 2) P at hi
            simpa using hi),
        inferInstance⟩) :=
  zEstimator_tendsto_normal_of_lipschitz ψ θ₀ P S L hψmeas hLmeas hL hL2
    hδ₀ hLip hIdentification hVar J hDeriv
    (fun n ω => est n (S.sampleVector n ω)) hConsistent hMoment hEstMeas

end Causalean.Stat

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.EmpiricalProcess.Equicontinuity.LipschitzParametric
public import Causalean.Stat.MEstimation.ZEstimatorCLT

/-! # Primitive Lipschitz Z-estimator central limit theorem

This module packages the Lipschitz-class equicontinuity result with the generic
Z-estimator rate, asymptotic-linearity, and Gaussian-limit theorems.

Use this route when the score has a square-integrable Lipschitz envelope
(van der Vaart 1998, Theorem 5.21). Use the smooth-score route for
observationwise differentiable scores (Newey--McFadden 1994, Theorem 3.1;
van der Vaart 1998, Theorem 5.41), and the high-level equicontinuity route for
nonsmooth scores covered by empirical-process arguments.
-/

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped BigOperators ENNReal

namespace Causalean.Stat

@[expose] public section

/-- **Lipschitz Z-estimator regularity (van der Vaart 1998, Theorem 5.21).**
For [a population law](hyp:P), [score](hyp:ψ), [target](hyp:θ₀), [nonnegative
envelope](hyp:L), [score and envelope measurability](hyp:hψmeas,hLmeas),
[envelope nonnegativity and square integrability](hyp:hL,hL2), [a positive radius](hyp:hδ₀), [Lipschitz
control on that ball](hyp:hLip), [population identification](hyp:hIdentification),
[finite score variance](hyp:hVar), [invertible derivative](hyp:J), and [the
population derivative identity](hyp:hDeriv), [the generic Z-estimator
regularity package holds](goal). -/
noncomputable def zEstimatorRegularityOfLipschitz
    {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (ψ : E → X → E) (θ₀ : E) (P : Measure X) [IsProbabilityMeasure P]
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
      J.toContinuousLinearMap θ₀) :
    ZEstimatorRegularity ψ θ₀ P := by
  have hLint : Integrable L P := by
    apply Integrable.mono' ((integrable_const (1 : ℝ)).add hL2)
      hLmeas.aestronglyMeasurable
    filter_upwards with x
    change |L x| ≤ 1 + L x ^ 2
    rw [abs_of_nonneg (hL x)]
    nlinarith [sq_nonneg (L x - 1 / 2)]
  have hψ₀int : Integrable (ψ θ₀) P := by
    apply Integrable.mono' ((integrable_const (1 : ℝ)).add hVar)
      (hψmeas θ₀).aestronglyMeasurable
    filter_upwards with x
    change ‖ψ θ₀ x‖ ≤ 1 + ‖ψ θ₀ x‖ ^ 2
    nlinarith [sq_nonneg (‖ψ θ₀ x‖ - 1 / 2)]
  have hψint (θ : E) (hθ : θ ∈ Metric.closedBall θ₀ δ₀) :
      Integrable (ψ θ) P := by
    apply Integrable.mono'
      (hψ₀int.norm.add (hLint.const_mul ‖θ - θ₀‖))
      (hψmeas θ).aestronglyMeasurable
    filter_upwards with x
    calc
      ‖ψ θ x‖ ≤ ‖ψ θ x - ψ θ₀ x‖ + ‖ψ θ₀ x‖ := by
        simpa only [sub_add_cancel] using norm_add_le (ψ θ x - ψ θ₀ x) (ψ θ₀ x)
      _ ≤ L x * ‖θ - θ₀‖ + ‖ψ θ₀ x‖ :=
        add_le_add (hLip θ hθ θ₀ (Metric.mem_closedBall_self hδ₀.le) x) le_rfl
      _ = ‖ψ θ₀ x‖ + ‖θ - θ₀‖ * L x := by ring
  exact
    { identification := hIdentification
      J₀ := J.toContinuousLinearMap
      J₀_inv := J.symm.toContinuousLinearMap
      J₀_inverse := by
        ext x
        simp
      J₀_spec := hDeriv
      finite_var := hVar
      psi_meas := hψmeas
      psi_int_neighborhood := ⟨δ₀, hδ₀, fun θ hθ => hψint θ (by
        simpa only [Metric.mem_closedBall, dist_eq_norm] using hθ.le)⟩ }

/-- **Lipschitz Z-estimator linearization (van der Vaart 1998, Theorem 5.21).**
Under [sampling law](hyp:μ), [population law](hyp:P), [iid sample](hyp:S),
[score](hyp:ψ), [target](hyp:θ₀), [nonnegative envelope](hyp:L), [score and
envelope measurability](hyp:hψmeas,hLmeas), [envelope nonnegativity and square
integrability](hyp:hL,hL2), [a positive radius](hyp:hδ₀), [Lipschitz control on that ball](hyp:hLip),
[identification](hyp:hIdentification), [finite variance](hyp:hVar), [invertible
derivative](hyp:J), [population derivative identity](hyp:hDeriv), [estimator](hyp:θn),
[consistency](hyp:hConsistent), and [approximate-root condition](hyp:hMoment),
[the estimator is asymptotically linear with influence function
$-J^{-1}\psi(\theta_0,\cdot)$](goal). -/
theorem zEstimator_asymLinear_of_lipschitz
    {Ω X E : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (ψ : E → X → E) (θ₀ : E) (P : Measure X)
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P) (L : X → ℝ)
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
    (θn : ℕ → Ω → E)
    (hConsistent : ∀ ε > 0,
      Tendsto (fun n => μ {ω | ε < ‖θn n ω - θ₀‖}) atTop (𝓝 0))
    (hMoment : IsLittleOp
      (fun n ω => ‖(Real.sqrt (n : ℝ))⁻¹ •
        ∑ i ∈ Finset.range n, ψ (θn n ω) (S.Z i ω)‖)
      (fun _ => (1 : ℝ)) μ) :
    IsAsymLinearVec (E := E) θn θ₀
      (fun x => -(J.symm (ψ θ₀ x))) S (fun n => Finset.range n) := by
  letI : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  let reg := zEstimatorRegularityOfLipschitz ψ θ₀ P L hψmeas hLmeas hL hL2 hδ₀ hLip
    hIdentification hVar J hDeriv
  have heq : (fun x => -(reg.J₀_inv (ψ θ₀ x))) =
      (fun x => -(J.symm (ψ θ₀ x))) := by rfl
  rw [← heq]
  exact zEstimator_asymLinear ψ θ₀ P reg S θn hConsistent
    (StochEquicontAt.of_lipschitz P S ψ L hψmeas hLmeas hL hL2 θ₀ hδ₀ hLip θn
      hConsistent)
    hMoment

/-- **Lipschitz Z-estimator Gaussian limit (van der Vaart 1998, Theorem 5.21).**
Under [sampling law](hyp:μ), [population law](hyp:P), [iid sample](hyp:S),
[score](hyp:ψ), [target](hyp:θ₀), [nonnegative envelope](hyp:L), [score and
envelope measurability](hyp:hψmeas,hLmeas), [envelope nonnegativity and square
integrability](hyp:hL,hL2), [a positive radius](hyp:hδ₀), [Lipschitz control on that ball](hyp:hLip),
[identification](hyp:hIdentification), [finite variance](hyp:hVar), [invertible
derivative](hyp:J), [population derivative identity](hyp:hDeriv), [estimator](hyp:θn),
[consistency](hyp:hConsistent), [approximate-root condition](hyp:hMoment), and
[rescaled-estimator measurability](hyp:hθn_meas), [the rescaled estimator laws
converge to the Gaussian law generated by $-J^{-1}\psi(\theta_0,\cdot)$](goal). -/
theorem zEstimator_tendsto_normal_of_lipschitz
    {Ω X E : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (ψ : E → X → E) (θ₀ : E) (P : Measure X)
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P) (L : X → ℝ)
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
    (θn : ℕ → Ω → E)
    (hConsistent : ∀ ε > 0,
      Tendsto (fun n => μ {ω | ε < ‖θn n ω - θ₀‖}) atTop (𝓝 0))
    (hMoment : IsLittleOp
      (fun n ω => ‖(Real.sqrt (n : ℝ))⁻¹ •
        ∑ i ∈ Finset.range n, ψ (θn n ω) (S.Z i ω)‖)
      (fun _ => (1 : ℝ)) μ)
    (hθn_meas : ∀ n, AEMeasurable
      (IsAsymLinearVec.rescaledEstimator θn θ₀ (fun m => Finset.range m) n) μ) :
    Tendsto (β := ProbabilityMeasure E)
      (fun n => ⟨μ.map
        (IsAsymLinearVec.rescaledEstimator θn θ₀ (fun m => Finset.range m) n),
        Measure.isProbabilityMeasure_map (hθn_meas n)⟩)
      atTop
      (𝓝 ⟨gaussianLimit
          ((J.symm.continuous.measurable.comp (hψmeas θ₀)).neg)
          (show Integrable (fun x => ‖-(J.symm (ψ θ₀ x))‖ ^ 2) P from by
            letI : IsProbabilityMeasure P := by
              rw [← S.law]
              exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
            let reg := zEstimatorRegularityOfLipschitz ψ θ₀ P L hψmeas hLmeas hL hL2
              hδ₀ hLip hIdentification hVar J hDeriv
            have hi := integrable_sq_zEstimatorInfluence ψ θ₀ P reg
            change Integrable (fun x => ‖-(J.symm (ψ θ₀ x))‖ ^ 2) P at hi
            simpa using hi),
        inferInstance⟩) := by
  letI : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  let reg := zEstimatorRegularityOfLipschitz ψ θ₀ P L hψmeas hLmeas hL hL2 hδ₀ hLip
    hIdentification hVar J hDeriv
  have hz := zEstimator_tendsto_normal ψ θ₀ P reg S θn hConsistent
    (StochEquicontAt.of_lipschitz P S ψ L hψmeas hLmeas hL hL2 θ₀ hδ₀ hLip θn
      hConsistent)
    hMoment hθn_meas
  convert hz using 1
  congr 2

end
end Causalean.Stat

module

public import Causalean.Stat.Bootstrap.SmoothZEstimator.Basic

/-!
# Sampling linearization for smooth Z-estimators

This module converts high-probability exact solution of the sample estimating equation into the
normalized residual required by the existing smooth Z-estimator theorem, and exposes its
finite-dimensional vector linearization in convergence-in-probability form.
-/

public section

namespace Causalean.Stat

open Causalean.Stat Filter MeasureTheory ProbabilityTheory Topology
open scoped BigOperators Topology

noncomputable section

variable {Omega X E : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {mu : Measure Omega} {P : Measure X}

/-- For [an iid sample](hyp:S), [an estimating function](hyp:psi), [a sample-function
estimator](hyp:est), and [data estimating-equation validity in probability](hyp:hSolve), [the
root-sample-size normalized score is negligible in probability](goal). -/
theorem normalizedScore_isLittleOp_of_solvesInProbability
    [IsProbabilityMeasure mu]
    (S : IIDSample Omega X mu P) (psi : E → X → E)
    (est : (n : ℕ) → (Fin n → X) → E)
    (hSolve : SolvesEstimatingEquationInProbability S psi est) :
    IsLittleOp
      (fun n omega ↦ ‖(Real.sqrt (n : ℝ))⁻¹ •
        ∑ i ∈ Finset.range n,
          psi (est n (S.sampleVector n omega)) (S.Z i omega)‖)
      (fun _ ↦ (1 : ℝ)) mu := by
  -- Proof plan: for `n ≠ 0`, a nonzero normalized sum forces the finite score mean to be
  -- nonzero; at `n = 0` the sum vanishes.  Bound every fixed positive tail by the failure event
  -- in `hSolve`, then unfold `IsLittleOp`.
  intro epsilon hepsilon
  simp only [mul_one, abs_norm]
  unfold SolvesEstimatingEquationInProbability at hSolve
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hSolve
    (fun _ ↦ zero_le) (fun n ↦ measure_mono fun omega homega ↦ ?_)
  simp only [Set.mem_ofPred_eq] at homega ⊢
  by_cases hn : n = 0
  · subst n
    simp at homega
    exfalso
    exact (not_lt_of_ge hepsilon.le) homega
  · intro hscore
    unfold zEstimatorSampleScore Causalean.Stat.finMean at hscore
    have hfin :
        (∑ i : Fin n,
          psi (est n (S.sampleVector n omega)) (S.sampleVector n omega i)) = 0 :=
      (smul_eq_zero.mp hscore).resolve_left
        (inv_ne_zero (Nat.cast_ne_zero.mpr hn))
    change
      (∑ i : Fin n,
        psi (est n (S.sampleVector n omega)) (S.Z (i : ℕ) omega)) = 0 at hfin
    have hsum :
        (∑ i ∈ Finset.range n,
          psi (est n (S.sampleVector n omega)) (S.Z i omega)) = 0 := by
      rw [← Fin.sum_univ_eq_sum_range]
      exact hfin
    simp [hsum] at homega
    exact (not_lt_of_ge hepsilon.le) homega

/-- For [an estimating function](hyp:psi), [a target parameter](hyp:theta0), [a population
law](hyp:P), [a smooth Z-estimator regularity package](hyp:reg), [an iid sample](hyp:S), [a
sample-function estimator](hyp:est), [data consistency](hyp:hConsistent), and [data
estimating-equation validity in probability](hyp:hSolve), [the vector sampling linearization
remainder converges to zero in probability](goal). -/
theorem zEstimator_samplingLinearization
    [IsProbabilityMeasure mu]
    (psi : E → X → E) (theta0 : E) (P : Measure X)
    (reg : SmoothZEstimatorRegularity psi theta0 P)
    (S : IIDSample Omega X mu P)
    (est : (n : ℕ) → (Fin n → X) → E)
    (hConsistent : ∀ epsilon > 0,
      Tendsto
        (fun n ↦ mu {omega |
          epsilon < ‖est n (S.sampleVector n omega) - theta0‖})
        atTop (nhds 0))
    (hSolve : SolvesEstimatingEquationInProbability S psi est) :
    Tendsto_inProb
      (fun n omega ↦ ‖zEstimatorSamplingRemainder
        S est theta0 reg.influence n omega‖)
      (fun _ ↦ 0) mu := by
  -- Proof plan: obtain the normalized-score hypothesis from the preceding lemma and invoke
  -- `zEstimator_asymLinear_of_smoothScore_of_sampleFn`.  Its `IsLittleOp` remainder is exactly
  -- the norm of `zEstimatorSamplingRemainder`; convert it with
  -- `Tendsto_inProb.of_isLittleOp_one`.
  have hMoment :=
    normalizedScore_isLittleOp_of_solvesInProbability S psi est hSolve
  have hLinear :=
    zEstimator_asymLinear_of_smoothScore_of_sampleFn
      psi theta0 P reg S est hConsistent hMoment
  apply Tendsto_inProb.of_isLittleOp_one
  simpa [zEstimatorSamplingRemainder, IsAsymLinearVec.normalizedSum] using
    hLinear.remainder

end

end Causalean.Stat

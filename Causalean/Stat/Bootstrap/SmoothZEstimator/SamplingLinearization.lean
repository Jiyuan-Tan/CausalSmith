module

public import Causalean.Stat.Bootstrap.SmoothZEstimator.Basic
public import Causalean.Stat.Limit.StochasticOrder

/-!
# Sampling linearization for smooth Z-estimators

This module records that eventual exact roots imply the standard negligible normalized-score
condition, and exposes smooth Z-estimator finite-dimensional vector linearization in
convergence-in-probability form under that standard condition.
-/

public section

namespace Causalean.Stat

open Filter MeasureTheory ProbabilityTheory Topology
open scoped BigOperators Topology

noncomputable section

variable {Omega X E : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {mu : Measure Omega} {P : Measure X}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For [an iid sample, estimating function, and sample-function estimator](hyp:S,psi,est), if
[the estimator solves its estimating equation exactly with probability tending to
one](hyp:hSolve), then [its root-sample-size normalized score is negligible in probability](goal).
The claim needs no bound on the score away from the solution event. -/
theorem solvesEstimatingEquationInProbability_of_eventuallyExactly
    [IsProbabilityMeasure mu]
    (S : IIDSample Omega X mu P) (psi : E → X → E)
    (est : (n : ℕ) → (Fin n → X) → E)
    (hSolve : EventuallySolvesEstimatingEquationExactly S psi est) :
    SolvesEstimatingEquationInProbability S psi est := by
  -- Proof plan: for `n ≠ 0`, a nonzero normalized sum forces the finite score mean to be
  -- nonzero; at `n = 0` the sum vanishes.  Bound every fixed positive tail by the failure event
  -- in `hSolve`, then unfold `IsLittleOp`.
  unfold EventuallySolvesEstimatingEquationExactly at hSolve
  unfold SolvesEstimatingEquationInProbability
  intro epsilon hepsilon
  simp only [mul_one]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hSolve
    (fun _ ↦ zero_le) (fun n ↦ measure_mono fun omega homega ↦ ?_)
  simp only [Set.mem_ofPred_eq] at homega ⊢
  by_cases hn : n = 0
  · subst n
    simp at homega
    exfalso
    exact (not_le_of_gt hepsilon) homega

  · intro hscore
    unfold zEstimatorSampleScore finMean at hscore
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
    exact (not_le_of_gt hepsilon) homega

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For [an iid sample, estimating function, and sample-function estimator](hyp:S,psi,est), if
[the estimator solves its bootstrap estimating equation exactly with conditional probability
tending to one in outer sampling probability](hyp:hSolve), then [its root-sample-size bootstrap
score residual is negligible in the same nested-probability sense](goal). The claim needs no bound
on the score away from the exact-root event. -/
theorem bootstrapSolvesEstimatingEquationInProbability_of_eventuallyExactly
    [IsProbabilityMeasure mu]
    (S : IIDSample Omega X mu P) (psi : E → X → E)
    (est : (n : ℕ) → (Fin n → X) → E)
    (hSolve : BootstrapEventuallySolvesEstimatingEquationExactly S psi est) :
    BootstrapSolvesEstimatingEquationInProbability S psi est := by
  unfold BootstrapEventuallySolvesEstimatingEquationExactly at hSolve
  unfold BootstrapSolvesEstimatingEquationInProbability
  intro epsilon hepsilon delta hdelta
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hSolve delta hdelta) (fun _ ↦ measureReal_nonneg) (fun n ↦ ?_)
  by_cases hn : n = 0
  · subst n
    simp [not_lt_of_ge hepsilon.le, not_lt_of_ge hdelta.le]
  apply measureReal_mono _ (measure_ne_top _ _)
  intro omega homega
  simp only [Set.mem_ofPred_eq] at homega ⊢
  let _ : IsProbabilityMeasure (bootstrapResample (S.sampleVector n omega)) :=
    bootstrapResample_isProbabilityMeasure _ hn
  refine homega.trans_le (measureReal_mono ?_ (measure_ne_top _ _))
  intro xstar hxstar
  simp only [Set.mem_ofPred_eq] at hxstar ⊢
  intro hzero
  rw [hzero, smul_zero, norm_zero] at hxstar
  exact (not_lt_of_ge hepsilon.le) hxstar

/-- For [a score, target, and population law](hyp:psi,theta0,P), [a smooth Z-estimator regularity
package](hyp:reg), [an iid sample and sample-function estimator](hyp:S,est), [data
consistency](hyp:hConsistent), and
[a negligible root-sample-size estimating-equation residual](hyp:hSolve), [the vector sampling
linearization remainder converges to zero in probability](goal). -/
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
  -- Apply the smooth-score theorem directly to the normalized-score hypothesis.  Its
  -- `IsLittleOp` remainder is exactly the norm of `zEstimatorSamplingRemainder`; convert it with
  -- `Tendsto_inProb.of_isLittleOp_one`.
  have hMoment :=
    hSolve
  have hLinear :=
    zEstimator_asymLinear_of_smoothScore_of_sampleFn
      psi theta0 P reg S est hConsistent hMoment
  rw [Tendsto_inProb_iff_hub,
    Modes.tendstoInProbability_zero_iff_isLittleOpF_one]
  simpa [IsLittleOp, zEstimatorSamplingRemainder,
    IsAsymLinearVec.normalizedSum] using hLinear.remainder

end

end Causalean.Stat

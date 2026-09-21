module

public import Causalean.Stat.Bootstrap.AsymptoticLinear.Coverage
public import Causalean.Stat.Bootstrap.SmoothFunctionOfMeans.Linearization
public import Causalean.Stat.MEstimation.SmoothZEstimatorSampleFn

/-!
# Bootstrap hypotheses and remainders for smooth Z-estimators

This module gives names to the finite-sample score, the sampling and Efron-bootstrap
linearization remainders, and the two conditional-in-probability hypotheses used by smooth
Z-estimator bootstrap validity.  The definitions keep the inner bootstrap error tolerance and
the outer sampling-probability tolerance separate.
-/

@[expose] public section

namespace Causalean.Stat

open Causalean.Stat Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators Topology

noncomputable section

variable {Omega X E : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {mu : Measure Omega} {P : Measure X}

/-- For [an estimating function](hyp:psi), [a parameter](hyp:theta), and [a finite data
vector](hyp:x), [the empirical estimating equation](goal) is given by [the average of its
observationwise scores](step:1). -/
def zEstimatorSampleScore (psi : E → X → E) (theta : E)
    {n : ℕ} (x : Fin n → X) : E :=
  Causalean.Stat.finMean (fun i ↦ psi theta (x i))

/-- For [an iid sample](hyp:S), [an estimating function](hyp:psi), and [a sample-function
estimator](hyp:est), [data estimating-equation validity in probability](goal) is given by [the
probability of a nonzero empirical score tending to zero](step:1). -/
def SolvesEstimatingEquationInProbability
    (S : IIDSample Omega X mu P) (psi : E → X → E)
    (est : (n : ℕ) → (Fin n → X) → E) : Prop :=
  Tendsto
    (fun n ↦ mu {omega |
      zEstimatorSampleScore psi (est n (S.sampleVector n omega))
        (S.sampleVector n omega) ≠ 0})
    atTop (nhds 0)

/-- For [an iid sample](hyp:S), [an estimating function](hyp:psi), and [a sample-function
estimator](hyp:est), [bootstrap estimating-equation validity in outer probability](goal) is given
by [every positive outer tolerance having a vanishing sampling tail for a nonzero resample
score](step:1). -/
def BootstrapSolvesEstimatingEquationInProbability
    (S : IIDSample Omega X mu P) (psi : E → X → E)
    (est : (n : ℕ) → (Fin n → X) → E) : Prop :=
  ∀ delta : ℝ, 0 < delta →
    Tendsto
      (fun n ↦ mu.real {omega |
        delta < (bootstrapResample (S.sampleVector n omega)).real
          {xstar |
            zEstimatorSampleScore psi (est n xstar) xstar ≠ 0}})
      atTop (nhds 0)

/-- For [an iid sample](hyp:S), [a bootstrap statistic](hyp:T), and [a data-dependent
target](hyp:t), [conditional convergence in bootstrap probability in outer probability](goal) is
given by [each positive inner error tolerance and positive outer probability tolerance having a
vanishing outer sampling tail](step:1). -/
def BootstrapTendstoInProbability
    (S : IIDSample Omega X mu P)
    (T : (n : ℕ) → (Fin n → X) → (Fin n → X) → E)
    (t : (n : ℕ) → (Fin n → X) → E) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∀ delta : ℝ, 0 < delta →
    Tendsto
      (fun n ↦ mu.real {omega |
        delta < (bootstrapResample (S.sampleVector n omega)).real
          {xstar | epsilon <
            ‖T n (S.sampleVector n omega) xstar -
              t n (S.sampleVector n omega)‖}})
      atTop (nhds 0)

/-- For [an iid sample](hyp:S), [a sample-function estimator](hyp:est), and [a population
target](hyp:theta0), [bootstrap consistency in outer probability](goal) is given by [conditional
convergence of the resampled estimator to that target](step:1). -/
def BootstrapEstimatorConsistent
    (S : IIDSample Omega X mu P)
    (est : (n : ℕ) → (Fin n → X) → E) (theta0 : E) : Prop :=
  BootstrapTendstoInProbability S
    (fun n _ xstar ↦ est n xstar) (fun _ _ ↦ theta0)

/-- For [an iid sample](hyp:S), [a sample-function estimator](hyp:est), [a target
parameter](hyp:theta0), [an influence function](hyp:influence), [a sample size](hyp:n), and [an
outcome](hyp:omega), [the sampling linearization remainder](goal) is given by [the
root-sample-size estimator error minus the normalized influence sum](step:1). -/
def zEstimatorSamplingRemainder
    (S : IIDSample Omega X mu P)
    (est : (n : ℕ) → (Fin n → X) → E)
    (theta0 : E) (influence : X → E) (n : ℕ) (omega : Omega) : E :=
  Real.sqrt (n : ℝ) • (est n (S.sampleVector n omega) - theta0) -
    IsAsymLinearVec.normalizedSum S influence (fun m ↦ Finset.range m) n omega

/-- For [a sample-function estimator](hyp:est), [an influence function](hyp:influence), [a
sample size](hyp:n), [observed data](hyp:x), and [a same-size resample](hyp:xstar), [the
bootstrap linearization remainder](goal) is given by [the centered root-sample-size estimator
difference minus the centered bootstrap influence mean](step:1). -/
def zEstimatorBootstrapRemainder
    (est : (n : ℕ) → (Fin n → X) → E)
    (influence : X → E) (n : ℕ) (x xstar : Fin n → X) : E :=
  Real.sqrt (n : ℝ) • (est n xstar - est n x) -
    scaledBootstrapMeanDifference influence n x xstar

end

end Causalean.Stat

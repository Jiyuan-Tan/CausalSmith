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

/-- Given [an estimating function](hyp:psi), [a parameter](hyp:theta), and
[finite data](hyp:x), the [empirical estimating equation](goal) is the finite average of the
observationwise scores. -/
def zEstimatorSampleScore (psi : E → X → E) (theta : E)
    {n : ℕ} (x : Fin n → X) : E :=
  Causalean.Stat.finMean (fun i ↦ psi theta (x i))

/-- For [an iid sample](hyp:S), [an estimating function](hyp:psi), and [an estimator](hyp:est),
[the estimator solves its data estimating equation with probability tending to one](goal) when
the probability of a nonzero empirical score tends to zero. -/
def SolvesEstimatingEquationInProbability
    (S : IIDSample Omega X mu P) (psi : E → X → E)
    (est : (n : ℕ) → (Fin n → X) → E) : Prop :=
  Tendsto
    (fun n ↦ mu {omega |
      zEstimatorSampleScore psi (est n (S.sampleVector n omega))
        (S.sampleVector n omega) ≠ 0})
    atTop (nhds 0)

/-- For [an iid sample](hyp:S), [an estimating function](hyp:psi), and [an estimator](hyp:est),
[the estimator solves its resampled estimating equation in bootstrap probability, in outer
sampling probability](goal) when every positive outer tolerance eventually has vanishing
sampling probability. -/
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
target](hyp:t), [conditional convergence in bootstrap probability, in outer sampling
probability](goal) means that every inner error tolerance and every outer probability tolerance
have a vanishing outer sampling tail. -/
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

/-- For [an iid sample](hyp:S), [an estimator](hyp:est), and [a population target](hyp:theta0),
[bootstrap consistency for the target, in outer sampling probability](goal) is conditional
convergence in probability of the resampled estimator to the fixed target. -/
def BootstrapEstimatorConsistent
    (S : IIDSample Omega X mu P)
    (est : (n : ℕ) → (Fin n → X) → E) (theta0 : E) : Prop :=
  BootstrapTendstoInProbability S
    (fun n _ xstar ↦ est n xstar) (fun _ _ ↦ theta0)

/-- Given [an iid sample](hyp:S), [an estimator](hyp:est), [a target](hyp:theta0), [an influence
function](hyp:influence), and [a sample size and realized outcome](hyp:n,omega), the [sampling
linearization remainder](goal) is the root-sample-size estimator error minus the normalized
influence sum. -/
def zEstimatorSamplingRemainder
    (S : IIDSample Omega X mu P)
    (est : (n : ℕ) → (Fin n → X) → E)
    (theta0 : E) (influence : X → E) (n : ℕ) (omega : Omega) : E :=
  Real.sqrt (n : ℝ) • (est n (S.sampleVector n omega) - theta0) -
    IsAsymLinearVec.normalizedSum S influence (fun m ↦ Finset.range m) n omega

/-- Given [an estimator](hyp:est), [an influence function](hyp:influence), [a sample
size](hyp:n), [data](hyp:x), and [a resample](hyp:xstar), the [bootstrap linearization
remainder](goal) is the centered root-sample-size estimator difference minus the centered
bootstrap influence mean. -/
def zEstimatorBootstrapRemainder
    (est : (n : ℕ) → (Fin n → X) → E)
    (influence : X → E) (n : ℕ) (x xstar : Fin n → X) : E :=
  Real.sqrt (n : ℝ) • (est n xstar - est n x) -
    scaledBootstrapMeanDifference influence n x xstar

end

end Causalean.Stat

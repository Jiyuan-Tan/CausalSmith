module
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Likelihood of a balanced pair of Poisson counts

The two rates have a fixed sum. Relative to the pair with equal rates, their
joint likelihood is a product of two powers, and its inner product has an
exponential Gram formula. These identities are the analytic input to the
moment-matched predictive comparison.
-/

@[expose] public section

namespace Causalean.Stat.Minimax.Multinomial.TwoSampleL1

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The joint law of two independent Poisson counts whose rates are the
opposite perturbations of a common nonnegative intensity. -/
noncomputable def scalarPoissonPairLaw (lambda t u : ℝ) : Measure (ℕ × ℕ) :=
  (poissonMeasure (Real.toNNReal (lambda * (1 + t * u)))).prod
    (poissonMeasure (Real.toNNReal (lambda * (1 - t * u))))

/-- The likelihood of a balanced Poisson pair relative to the pair with
equal rates; the two exponential factors cancel because the rates sum to a
constant. -/
noncomputable def scalarPoissonPairLikelihood (t u : ℝ) (z : ℕ × ℕ) : ℝ :=
  (1 + t * u) ^ z.1 * (1 - t * u) ^ z.2

/-- The expectation of a real power under a Poisson law is the exponential
of the intensity times the power base minus one. -/
theorem poisson_power_mgf (q : NNReal) (u : ℝ) :
    (∫ n : ℕ, u ^ n ∂poissonMeasure q) =
      Real.exp ((q : ℝ) * (u - 1)) := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  rw [show (fun n : ℕ => Real.exp (-(q : ℝ)) * (q : ℝ) ^ n /
      (n.factorial : ℝ) * u ^ n) =
      fun n => Real.exp (-(q : ℝ)) * (((q : ℝ) * u) ^ n /
        (n.factorial : ℝ)) by
    funext n
    rw [mul_pow]
    ring]
  rw [tsum_mul_left]
  rw [show (∑' n : ℕ, ((q : ℝ) * u) ^ n / (n.factorial : ℝ)) =
      Real.exp ((q : ℝ) * u) by
    simpa only [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp ((q : ℝ) * u)).tsum_eq]
  rw [← Real.exp_add]
  congr 1
  ring

/-- At positive baseline intensity and a nonnegative pair of perturbed rates,
the balanced Poisson law has the stated likelihood density relative to the
unperturbed pair. This localizes the real-to-nonnegative-rate conversion. -/
theorem scalarPoissonPairLaw_eq_withDensity
    (lambda t u : ℝ) (hlambda : 0 < lambda)
    (hplus : 0 ≤ 1 + t * u) (hminus : 0 ≤ 1 - t * u) :
    scalarPoissonPairLaw lambda t u =
      (scalarPoissonPairLaw lambda t 0).withDensity
        (fun z => ENNReal.ofReal (scalarPoissonPairLikelihood t u z)) := by
  /- Compare singleton masses using `poissonMeasure_singleton`. The
  exponential factors cancel exactly because the two rates sum to `2*lambda`.
  `Measure.ext_of_singleton` applies since the observation space is countable. -/
  apply Measure.ext_of_singleton
  rintro ⟨n, m⟩
  rw [withDensity_apply _ (by measurability), lintegral_singleton]
  simp only [scalarPoissonPairLaw, scalarPoissonPairLikelihood,
    ← Set.singleton_prod_singleton, Measure.prod_prod, poissonMeasure_singleton]
  have hp : 0 ≤ lambda * (1 + t * u) := mul_nonneg hlambda.le hplus
  have hm : 0 ≤ lambda * (1 - t * u) := mul_nonneg hlambda.le hminus
  simp only [Real.coe_toNNReal _ hp, Real.coe_toNNReal _ hm,
    mul_zero, add_zero, sub_zero, mul_one, Real.coe_toNNReal _ hlambda.le]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hexp :
      Real.exp (-(lambda * (1 + t * u))) * Real.exp (-(lambda * (1 - t * u))) =
        Real.exp (-lambda) * Real.exp (-lambda) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (-(lambda * (1 + t * u))) *
          Real.exp (-(lambda * (1 - t * u)))) *
          (lambda ^ n * lambda ^ m) *
          ((1 + t * u) ^ n * (1 - t * u) ^ m) /
          ((n.factorial : ℝ) * (m.factorial : ℝ)) := by
        rw [mul_pow, mul_pow]
        ring
    _ = _ := by rw [hexp]; ring

/-- Given [a nonnegative Poisson intensity](hyp:lambda,hlambda) and [two scalar tilt coordinates](hyp:t,u,v), [the likelihood inner product under the untitled scalar-Poisson law equals the stated exponential expression](goal). -/
theorem scalarPoissonPairLikelihood_inner
    (lambda t u v : ℝ) (hlambda : 0 ≤ lambda) :
    (∫ z, scalarPoissonPairLikelihood t u z *
        scalarPoissonPairLikelihood t v z ∂scalarPoissonPairLaw lambda t 0) =
      Real.exp (2 * lambda * t ^ 2 * u * v) := by
  /- Factor the product-Poisson integral into two Poisson power MGFs.
  The one-count identity `poisson_power_mgf` is private in Causalean's
  MarkedPoisson/AggregatePoisson module, so prove or expose a local version.
  Algebra reduces the two exponents to `2*lambda*t^2*u*v`. -/
  have hrate : Real.toNNReal (lambda * (1 + t * 0)) = Real.toNNReal lambda := by ring
  have hrate' : Real.toNNReal (lambda * (1 - t * 0)) = Real.toNNReal lambda := by ring
  have hcast : ((Real.toNNReal lambda : NNReal) : ℝ) = lambda :=
    Real.coe_toNNReal lambda hlambda
  have hfactor (z : ℕ × ℕ) :
      scalarPoissonPairLikelihood t u z * scalarPoissonPairLikelihood t v z =
        ((1 + t * u) * (1 + t * v)) ^ z.1 *
          ((1 - t * u) * (1 - t * v)) ^ z.2 := by
    simp only [scalarPoissonPairLikelihood, mul_pow]
    ring
  simp_rw [hfactor]
  simp only [scalarPoissonPairLaw, hrate, hrate']
  rw [integral_prod_mul, poisson_power_mgf, poisson_power_mgf, ← Real.exp_add]
  rw [hcast]
  congr 1
  ring

end Causalean.Stat.Minimax.Multinomial.TwoSampleL1

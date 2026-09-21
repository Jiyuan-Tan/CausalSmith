import Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.Certificate
import Causalean.Stat.Minimax.MomentMatchedMixture.SupportLocalized
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Kernel.WithDensity

/-!
# Aggregate affine-Poisson moment-matched mixtures

This module isolates the analytic core needed by the marked experiment.  It
combines the treated counts before marking, leaving two independent Poisson
counts whose affine rates add to `t * p`.  The resulting Jordan-prior mixture
is controlled by the standard exponential-Gram moment-matching bound.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture

/-- The [defined object](goal) is determined by the displayed assumptions and is given by [the following defining expression](step:1).  The two-count observation consisting of aggregate treated and aggregate
control counts. -/
abbrev AggregatePoissonObservation := ℕ × ℕ

/-- The [defined object](goal) is determined by [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the aggregate intensity](hyp:t), [the latent mass](hyp:p) and is given by [the following defining expression](step:1). -/
def aggregateTreatedRate (ε a t p : ℝ) : ℝ := t * ε * (p + a)

/-- The [defined object](goal) is determined by [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the aggregate intensity](hyp:t), [the latent mass](hyp:p) and is given by [the following defining expression](step:1). -/
def aggregateControlRate (ε a t p : ℝ) : ℝ :=
  t * ((1 - ε) * p - ε * a)

/-- The [defined object](goal) is determined by [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the aggregate intensity](hyp:t), [the latent mass](hyp:p) and is given by [the following defining expression](step:1).  The explicit pair of independent Poisson laws with aggregate treated and
control rates. -/
noncomputable def aggregatePoissonLaw
    (ε a t p : ℝ) : Measure AggregatePoissonObservation :=
  (poissonMeasure (Real.toNNReal (aggregateTreatedRate ε a t p))).prod
    (poissonMeasure (Real.toNNReal (aggregateControlRate ε a t p)))

/-- The [defined object](goal) is determined by [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the aggregate intensity](hyp:t), [the latent mass](hyp:p) and is given by [the following defining expression](step:1).  Every aggregate two-count law is a probability measure. -/
noncomputable instance aggregatePoissonLaw_isProbabilityMeasure
    (ε a t p : ℝ) : IsProbabilityMeasure (aggregatePoissonLaw ε a t p) := by
  unfold aggregatePoissonLaw
  infer_instance

private noncomputable def aggregatePoissonKernelOfRealRate
    (r : ℝ → ℝ) : Kernel ℝ ℕ :=
  (Kernel.const ℝ Measure.count).withDensity fun p n =>
    ENNReal.ofReal (Real.exp (-(Real.toNNReal (r p) : ℝ)) *
      (Real.toNNReal (r p) : ℝ) ^ n / Nat.factorial n)

private noncomputable instance aggregatePoissonKernelOfRealRate_isSFinite
    (r : ℝ → ℝ) : IsSFiniteKernel (aggregatePoissonKernelOfRealRate r) := by
  unfold aggregatePoissonKernelOfRealRate
  apply Kernel.IsSFiniteKernel.withDensity
  simp

private theorem aggregatePoissonKernelOfRealRate_apply
    (r : ℝ → ℝ) (hr : Measurable r) (p : ℝ) :
    aggregatePoissonKernelOfRealRate r p = poissonMeasure (Real.toNNReal (r p)) := by
  rw [aggregatePoissonKernelOfRealRate, Kernel.withDensity_apply]
  · apply Measure.ext_of_singleton
    intro n
    rw [withDensity_apply _ (measurableSet_singleton n), poissonMeasure_singleton]
    simp
  · apply measurable_from_prod_countable_left
    intro n
    fun_prop

/-- The [defined object](goal) is determined by [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the aggregate intensity](hyp:t) and is given by [the following defining expression](step:1).  The aggregate affine-Poisson experiment as a kernel from latent mass to
the treated/control count pair. -/
noncomputable def aggregatePoissonKernel (ε a t : ℝ) :
    Kernel ℝ AggregatePoissonObservation :=
  (aggregatePoissonKernelOfRealRate (aggregateTreatedRate ε a t)).prod
    (aggregatePoissonKernelOfRealRate (aggregateControlRate ε a t))

/-- The [stated conclusion](goal) follows from [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the aggregate intensity](hyp:t), [the latent mass](hyp:p).  The aggregate kernel fibre is the explicit product-Poisson law. -/
theorem aggregatePoissonKernel_apply (ε a t p : ℝ) :
    aggregatePoissonKernel ε a t p = aggregatePoissonLaw ε a t p := by
  unfold aggregatePoissonKernel aggregatePoissonLaw
  rw [Kernel.prod_apply,
    aggregatePoissonKernelOfRealRate_apply _ (by
      change Measurable (fun p : ℝ => t * ε * (p + a))
      fun_prop),
    aggregatePoissonKernelOfRealRate_apply _ (by
      change Measurable (fun p : ℝ => t * ((1 - ε) * p - ε * a))
      fun_prop)]

private noncomputable def affinePoissonLikelihood
    (q s θ : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-s * θ) * (1 + s * θ / q) ^ n

private lemma measurable_affinePoissonLikelihood (q s : ℝ) :
    Measurable (fun z : ℝ × ℕ => affinePoissonLikelihood q s z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro n
  unfold affinePoissonLikelihood
  fun_prop

private lemma affinePoissonLikelihood_nonnegative
    (q s θ : ℝ) (hq : 0 < q) (hr : 0 ≤ q + s * θ) (n : ℕ) :
    0 ≤ affinePoissonLikelihood q s θ n := by
  unfold affinePoissonLikelihood
  apply mul_nonneg (Real.exp_pos _).le (pow_nonneg _ _)
  rw [show 1 + s * θ / q = (q + s * θ) / q by field_simp]
  positivity

private lemma poisson_power_mgf (q : NNReal) (u : ℝ) :
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

private lemma poisson_affine_eq_withDensity
    (q s θ : ℝ) (hq : 0 < q) (hr : 0 ≤ q + s * θ) :
    poissonMeasure (Real.toNNReal (q + s * θ)) =
      (poissonMeasure (Real.toNNReal q)).withDensity
        (fun n => ENNReal.ofReal (affinePoissonLikelihood q s θ n)) := by
  apply Measure.ext_of_singleton
  intro n
  rw [withDensity_apply _ (measurableSet_singleton n)]
  simp [poissonMeasure_singleton]
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  have hlik : 0 ≤ affinePoissonLikelihood q s θ n :=
    affinePoissonLikelihood_nonnegative q s θ hq hr n
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hlik]
  rw [max_eq_left hr, max_eq_left hq.le]
  unfold affinePoissonLikelihood
  rw [show 1 + s * θ / q = (q + s * θ) / q by field_simp, div_pow]
  field_simp
  have hexp : Real.exp (-(q + s * θ)) =
      Real.exp (-q) * Real.exp (-(s * θ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

private lemma affinePoissonLikelihood_inner
    (q s θ θ' : ℝ) (hq : 0 < q) :
    (∫ n : ℕ, affinePoissonLikelihood q s θ n *
        affinePoissonLikelihood q s θ' n ∂poissonMeasure (Real.toNNReal q)) =
      Real.exp ((s ^ 2 / q) * θ * θ') := by
  rw [show (fun n : ℕ => affinePoissonLikelihood q s θ n *
      affinePoissonLikelihood q s θ' n) = fun n =>
        (Real.exp (-s * θ) * Real.exp (-s * θ')) *
          (((1 + s * θ / q) * (1 + s * θ' / q)) ^ n) by
    funext n
    simp only [affinePoissonLikelihood, mul_pow]
    ring]
  rw [integral_const_mul, poisson_power_mgf,
    Real.coe_toNNReal _ hq.le, ← Real.exp_add, ← Real.exp_add]
  congr 1
  field_simp
  ring

private noncomputable def aggregateCenteredLikelihood
    (qT qC sT sC θ : ℝ) (z : AggregatePoissonObservation) : ℝ :=
  affinePoissonLikelihood qT sT θ z.1 *
    affinePoissonLikelihood qC sC θ z.2

private lemma measurable_aggregateCenteredLikelihood (qT qC sT sC : ℝ) :
    Measurable (fun z : ℝ × AggregatePoissonObservation =>
      aggregateCenteredLikelihood qT qC sT sC z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro z
  unfold aggregateCenteredLikelihood affinePoissonLikelihood
  fun_prop

private lemma aggregateCenteredLikelihood_nonnegative
    (qT qC sT sC θ : ℝ) (hqT : 0 < qT) (hqC : 0 < qC)
    (hrT : 0 ≤ qT + sT * θ) (hrC : 0 ≤ qC + sC * θ)
    (z : AggregatePoissonObservation) :
    0 ≤ aggregateCenteredLikelihood qT qC sT sC θ z := by
  exact mul_nonneg
    (affinePoissonLikelihood_nonnegative qT sT θ hqT hrT z.1)
    (affinePoissonLikelihood_nonnegative qC sC θ hqC hrC z.2)

private lemma aggregatePoissonLaw_centered_eq_withDensity
    (ε a t c θ qT qC sT sC : ℝ)
    (hqT : 0 < qT) (hqC : 0 < qC)
    (hrT : 0 ≤ qT + sT * θ) (hrC : 0 ≤ qC + sC * θ)
    (hT : aggregateTreatedRate ε a t (θ + c) = qT + sT * θ)
    (hC : aggregateControlRate ε a t (θ + c) = qC + sC * θ) :
    aggregatePoissonLaw ε a t (θ + c) =
      ((poissonMeasure (Real.toNNReal qT)).prod
        (poissonMeasure (Real.toNNReal qC))).withDensity
          (fun z => ENNReal.ofReal
            (aggregateCenteredLikelihood qT qC sT sC θ z)) := by
  unfold aggregatePoissonLaw
  rw [hT, hC, poisson_affine_eq_withDensity qT sT θ hqT hrT,
    poisson_affine_eq_withDensity qC sC θ hqC hrC,
    prod_withDensity
      (measurable_of_countable _)
      (measurable_of_countable _)]
  apply withDensity_congr_ae
  filter_upwards with z
  rw [aggregateCenteredLikelihood,
    ENNReal.ofReal_mul
      (affinePoissonLikelihood_nonnegative qT sT θ hqT hrT z.1)]

private lemma aggregateCenteredLikelihood_inner
    (qT qC sT sC θ θ' : ℝ) (hqT : 0 < qT) (hqC : 0 < qC) :
    (∫ z : AggregatePoissonObservation,
        aggregateCenteredLikelihood qT qC sT sC θ z *
          aggregateCenteredLikelihood qT qC sT sC θ' z
      ∂(poissonMeasure (Real.toNNReal qT)).prod
        (poissonMeasure (Real.toNNReal qC))) =
      Real.exp ((sT ^ 2 / qT + sC ^ 2 / qC) * θ * θ') := by
  rw [show (fun z : AggregatePoissonObservation =>
      aggregateCenteredLikelihood qT qC sT sC θ z *
        aggregateCenteredLikelihood qT qC sT sC θ' z) = fun z =>
      (affinePoissonLikelihood qT sT θ z.1 *
        affinePoissonLikelihood qT sT θ' z.1) *
      (affinePoissonLikelihood qC sC θ z.2 *
        affinePoissonLikelihood qC sC θ' z.2) by
    funext z
    simp only [aggregateCenteredLikelihood]
    ring]
  rw [integral_prod_mul
      (fun n => affinePoissonLikelihood qT sT θ n *
        affinePoissonLikelihood qT sT θ' n)
      (fun n => affinePoissonLikelihood qC sC θ n *
        affinePoissonLikelihood qC sC θ' n),
    affinePoissonLikelihood_inner qT sT θ θ' hqT,
    affinePoissonLikelihood_inner qC sC θ θ' hqC,
    ← Real.exp_add]
  congr 1
  ring

/-- The [defined object](goal) is determined by [the latent prior](hyp:π), [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the aggregate intensity](hyp:t) and is given by [the following defining expression](step:1).  Mixing the aggregate affine-Poisson kernel against a latent prior gives
its prior-predictive treated/control count law. -/
noncomputable def aggregatePoissonPredictive
    (π : Measure ℝ) (ε a t : ℝ) : Measure AggregatePoissonObservation :=
  Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive π
    (aggregatePoissonKernel ε a t)


end Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture

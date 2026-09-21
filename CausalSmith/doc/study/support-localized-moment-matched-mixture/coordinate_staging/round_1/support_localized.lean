import Causalean.Stat.Minimax.MomentMatchedMixture.Product

/-!
# Support-localized moment-matched prior mixtures

This module localizes the predictive-density, exponential Gram, and total-variation theory for
moment-matched prior mixtures. Likelihood nonnegativity, density representation, and inner-product
identities are needed only on the bounded interval carrying the priors; values outside their
support do not affect the resulting one-coordinate or finite-product bounds.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Causalean.Stat.Minimax.MomentMatchedMixture

variable {X : Type*} [MeasurableSpace X]

/-- A [probability prior](hyp:π) that assigns mass one to the [interval of parameters with
absolute value at most the chosen radius](hyp:a,hsupp) is [almost surely concentrated on that
interval](goal). -/
theorem ae_abs_le_of_measure_interval_eq_one
    (π : Measure ℝ) [IsProbabilityMeasure π] (a : ℝ)
    (hsupp : π {θ | |θ| ≤ a} = 1) :
    ∀ᵐ θ ∂π, |θ| ≤ a := by
  exact (mem_ae_iff_prob_eq_one
    (measurableSet_le continuous_abs.measurable measurable_const)).2 hsupp

/-- The [average under a sigma-finite prior](hyp:π) of a [real-valued likelihood family](hyp:likelihood)
that is [jointly measurable in parameter and observation](hyp:hmeas) is [measurable as a function
of the observation](goal). -/
theorem measurable_mixtureLikelihood
    (π : Measure ℝ) [SFinite π] (likelihood : ℝ → X → ℝ)
    (hmeas : Measurable fun p : ℝ × X => likelihood p.1 p.2) :
    Measurable (mixtureLikelihood π likelihood) := by
  exact hmeas.stronglyMeasurable.integral_prod_left'.measurable

/-- The [average under a probability prior](hyp:π) of a [real-valued likelihood family](hyp:likelihood)
at an [observation](hyp:x) is [nonnegative](goal) when the prior is [supported on the interval of
parameters with absolute value at most the chosen radius](hyp:a,hsupp) and the likelihood is
[nonnegative throughout that interval](hyp:hnonneg), regardless of its values elsewhere. -/
theorem mixtureLikelihood_nonnegative_of_supported
    (π : Measure ℝ) (likelihood : ℝ → X → ℝ) [IsProbabilityMeasure π]
    (a : ℝ) (hsupp : π {θ | |θ| ≤ a} = 1)
    (hnonneg : ∀ θ, |θ| ≤ a → ∀ x, 0 ≤ likelihood θ x) (x : X) :
    0 ≤ mixtureLikelihood π likelihood x := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_abs_le_of_measure_interval_eq_one π a hsupp] with θ hθ
  exact hnonneg θ hθ x

/-- The [prior average of a likelihood family](hyp:π,likelihood) is [integrable under a common
dominating measure](goal) when [the experiment kernel has probability fibres](hyp:K,hK), the
[dominating measure is sigma-finite](hyp:Q), the prior is [supported on the interval of parameters
with absolute value at most the chosen radius](hyp:a,hsupp), the likelihood is [jointly
measurable](hyp:hmeas) and [nonnegative on that interval](hyp:hnonneg), and supported kernel fibres
[have the stated likelihood densities](hyp:hdensity). -/
theorem integrable_mixtureLikelihood_of_supported_density
    (π : Measure ℝ) (K : Kernel ℝ X) (Q : Measure X) (likelihood : ℝ → X → ℝ)
    [IsProbabilityMeasure π] [SigmaFinite Q]
    (hK : ∀ θ, IsProbabilityMeasure (K θ)) (a : ℝ)
    (hsupp : π {θ | |θ| ≤ a} = 1)
    (hmeas : Measurable fun p : ℝ × X => likelihood p.1 p.2)
    (hnonneg : ∀ θ, |θ| ≤ a → ∀ x, 0 ≤ likelihood θ x)
    (hdensity : ∀ θ, |θ| ≤ a →
      K θ = Q.withDensity fun x => ENNReal.ofReal (likelihood θ x)) :
    Integrable (mixtureLikelihood π likelihood) Q := by
  have hsupp_ae := ae_abs_le_of_measure_interval_eq_one π a hsupp
  have hfiber : ∀ᵐ θ ∂π,
      ∫⁻ x, ENNReal.ofReal (likelihood θ x) ∂Q = 1 := by
    filter_upwards [hsupp_ae] with θ hθ
    calc
      ∫⁻ x, ENNReal.ofReal (likelihood θ x) ∂Q =
          (Q.withDensity fun x => ENNReal.ofReal (likelihood θ x)) Set.univ := by
            rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      _ = K θ Set.univ := by rw [hdensity θ hθ]
      _ = 1 := isProbabilityMeasure_iff.mp (hK θ)
  have hnonneg_ae : ∀ᵐ p : ℝ × X ∂π.prod Q, 0 ≤ likelihood p.1 p.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le measurable_const hmeas)).2
    filter_upwards [hsupp_ae] with θ hθ
    exact ae_of_all Q fun x => hnonneg θ hθ x
  have hjoint : Integrable (fun p : ℝ × X => likelihood p.1 p.2) (π.prod Q) := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal hnonneg_ae).2
    rw [lintegral_prod _ hmeas.ennreal_ofReal.aemeasurable]
    rw [lintegral_congr_ae hfiber]
    simp
  change Integrable (fun x => ∫ θ, likelihood θ x ∂π) Q
  exact hjoint.integral_prod_right

/-- The [predictive law obtained by averaging a probability prior](hyp:π) through an [experiment
kernel with probability fibres](hyp:K,hK) [equals the common dominating measure weighted by the
prior-averaged likelihood](goal) when the [dominating measure is sigma-finite](hyp:Q), the
[likelihood family](hyp:likelihood) is [jointly measurable](hyp:hmeas), the prior is [supported on
the interval of parameters with absolute value at most the chosen radius](hyp:a,hsupp), and only
on that interval the likelihood is [nonnegative](hyp:hnonneg) and [represents each kernel fibre's
density](hyp:hdensity). -/
theorem priorPredictive_eq_withDensity_mixtureLikelihood_of_supported
    (π : Measure ℝ) (K : Kernel ℝ X) (Q : Measure X) (likelihood : ℝ → X → ℝ)
    [IsProbabilityMeasure π] [SigmaFinite Q]
    (hK : ∀ θ, IsProbabilityMeasure (K θ)) (a : ℝ)
    (hsupp : π {θ | |θ| ≤ a} = 1)
    (hmeas : Measurable fun p : ℝ × X => likelihood p.1 p.2)
    (hnonneg : ∀ θ, |θ| ≤ a → ∀ x, 0 ≤ likelihood θ x)
    (hdensity : ∀ θ, |θ| ≤ a →
      K θ = Q.withDensity fun x => ENNReal.ofReal (likelihood θ x)) :
    priorPredictive π K =
      Q.withDensity fun x => ENNReal.ofReal (mixtureLikelihood π likelihood x) := by
  have hsupp_ae := ae_abs_le_of_measure_interval_eq_one π a hsupp
  have hfiber : ∀ᵐ θ ∂π,
      ∫⁻ x, ENNReal.ofReal (likelihood θ x) ∂Q = 1 := by
    filter_upwards [hsupp_ae] with θ hθ
    calc
      ∫⁻ x, ENNReal.ofReal (likelihood θ x) ∂Q =
          (Q.withDensity fun x => ENNReal.ofReal (likelihood θ x)) Set.univ := by
            rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      _ = K θ Set.univ := by rw [hdensity θ hθ]
      _ = 1 := isProbabilityMeasure_iff.mp (hK θ)
  have hnonneg_ae : ∀ᵐ p : ℝ × X ∂π.prod Q, 0 ≤ likelihood p.1 p.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le measurable_const hmeas)).2
    filter_upwards [hsupp_ae] with θ hθ
    exact ae_of_all Q fun x => hnonneg θ hθ x
  have hjoint : Integrable (fun p : ℝ × X => likelihood p.1 p.2) (π.prod Q) := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal hnonneg_ae).2
    rw [lintegral_prod _ hmeas.ennreal_ofReal.aemeasurable]
    rw [lintegral_congr_ae hfiber]
    simp
  have hsections : ∀ᵐ x ∂Q, Integrable (fun θ => likelihood θ x) π :=
    hjoint.prod_left_ae
  have haverage : ∀ᵐ x ∂Q,
      ENNReal.ofReal (mixtureLikelihood π likelihood x) =
        ∫⁻ θ, ENNReal.ofReal (likelihood θ x) ∂π := by
    filter_upwards [hsections] with x hx
    apply ofReal_integral_eq_lintegral_ofReal hx
    filter_upwards [hsupp_ae] with θ hθ
    exact hnonneg θ hθ x
  refine Measure.ext fun A hA => ?_
  rw [priorPredictive_apply π K hA, withDensity_apply _ hA]
  calc
    ∫⁻ θ, K θ A ∂π =
        ∫⁻ θ, ∫⁻ x in A, ENNReal.ofReal (likelihood θ x) ∂Q ∂π := by
      apply lintegral_congr_ae
      filter_upwards [hsupp_ae] with θ hθ
      rw [hdensity θ hθ, withDensity_apply _ hA]
    _ = ∫⁻ x in A, ∫⁻ θ, ENNReal.ofReal (likelihood θ x) ∂π ∂Q := by
      apply lintegral_lintegral_swap
      exact hmeas.ennreal_ofReal.aemeasurable
    _ = ∫⁻ x in A, ENNReal.ofReal (mixtureLikelihood π likelihood x) ∂Q := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae haverage] with x hx
      exact hx.symm

/-- The [predictive law obtained by averaging a probability prior](hyp:π) through an [experiment
kernel](hyp:K) is [absolutely continuous with respect to a common measure](goal) when the prior is
[supported on the interval of parameters with absolute value at most the chosen radius](hyp:a,hsupp)
and, on that interval, the [likelihood family](hyp:likelihood) [represents every kernel fibre as a
density relative to the common measure](hyp:Q,hdensity). -/
theorem priorPredictive_absolutelyContinuous_of_supported
    (π : Measure ℝ) (K : Kernel ℝ X) (Q : Measure X) (likelihood : ℝ → X → ℝ)
    [IsProbabilityMeasure π]
    (a : ℝ) (hsupp : π {θ | |θ| ≤ a} = 1)
    (hdensity : ∀ θ, |θ| ≤ a →
      K θ = Q.withDensity fun x => ENNReal.ofReal (likelihood θ x)) :
    priorPredictive π K ≪ Q := by
  refine Measure.AbsolutelyContinuous.mk fun A hA hQA => ?_
  rw [priorPredictive_apply π K hA]
  rw [lintegral_eq_zero_iff (Kernel.measurable_coe K hA)]
  filter_upwards [ae_abs_le_of_measure_interval_eq_one π a hsupp] with θ hθ
  change K θ A = 0
  rw [hdensity θ hθ]
  exact withDensity_absolutelyContinuous Q _ hQA

/- The sign-count likelihood motivating this API is nonnegative on the prior support. -/
example (Nplus Nminus : ℕ) (θ : ℝ) (hθ : |θ| ≤ 1) :
    0 ≤ (1 + θ) ^ Nplus * (1 - θ) ^ Nminus := by
  rcases abs_le.mp hθ with ⟨hlower, hupper⟩
  exact mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)

/- The same formula can be negative away from the prior support, so global nonnegativity is
strictly stronger than the localized assumption. -/
example : (1 + (2 : ℝ)) ^ (0 : ℕ) * (1 - 2) ^ (1 : ℕ) < 0 := by
  norm_num

private theorem supported_cross_integrable_and_eq
    (π ρ : Measure ℝ) (Q : Measure X) (likelihood : ℝ → X → ℝ)
    [IsProbabilityMeasure π] [IsProbabilityMeasure ρ] [IsProbabilityMeasure Q]
    (lambda a : ℝ) (hlambda : 0 ≤ lambda) (ha : 0 ≤ a)
    (hmeas : Measurable fun p : ℝ × X => likelihood p.1 p.2)
    (hnonneg : ∀ θ, |θ| ≤ a → ∀ x, 0 ≤ likelihood θ x)
    (hinner : ∀ θ, |θ| ≤ a → ∀ θ', |θ'| ≤ a →
      ∫ x, likelihood θ x * likelihood θ' x ∂Q = Real.exp (lambda * θ * θ'))
    (hsuppπ : π {θ | |θ| ≤ a} = 1) (hsuppρ : ρ {θ | |θ| ≤ a} = 1) :
    Integrable
        (fun x => mixtureLikelihood π likelihood x * mixtureLikelihood ρ likelihood x) Q ∧
      ∫ x, mixtureLikelihood π likelihood x * mixtureLikelihood ρ likelihood x ∂Q =
        exponentialPriorEnergy π ρ lambda := by
  let g : (ℝ × ℝ) × X → ℝ := fun z =>
    likelihood z.1.1 z.2 * likelihood z.1.2 z.2
  have hgmeas : Measurable g := by
    unfold g
    fun_prop
  have hpairs : ∀ᵐ z ∂π.prod ρ, |z.1| ≤ a ∧ |z.2| ≤ a := by
    apply (Measure.ae_prod_iff_ae_ae
      ((measurableSet_le (continuous_abs.measurable.comp measurable_fst) measurable_const).inter
        (measurableSet_le (continuous_abs.measurable.comp measurable_snd) measurable_const))).2
    filter_upwards [ae_abs_le_of_measure_interval_eq_one π a hsuppπ] with θ hθ
    filter_upwards [ae_abs_le_of_measure_interval_eq_one ρ a hsuppρ] with θ' hθ'
    exact ⟨hθ, hθ'⟩
  have hprod_int : ∀ᵐ z ∂π.prod ρ,
      Integrable (fun x => likelihood z.1 x * likelihood z.2 x) Q := by
    filter_upwards [hpairs] with z hz
    rcases hz with ⟨hz1, hz2⟩
    by_contra h
    have heq := hinner z.1 hz1 z.2 hz2
    rw [integral_undef h] at heq
    exact Real.exp_ne_zero _ heq.symm
  have hexp_int :
      Integrable (fun z : ℝ × ℝ => Real.exp (lambda * z.1 * z.2)) (π.prod ρ) := by
    apply (integrable_const (μ := π.prod ρ) (Real.exp (lambda * a ^ 2))).mono'
      (by fun_prop)
    filter_upwards [hpairs] with z hz
    rcases hz with ⟨hz1, hz2⟩
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      lambda * z.1 * z.2 ≤ |lambda * z.1 * z.2| := le_abs_self _
      _ = lambda * |z.1| * |z.2| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hlambda]
      _ ≤ lambda * a * a := by gcongr
      _ = lambda * a ^ 2 := by ring
  have hg_int : Integrable g ((π.prod ρ).prod Q) := by
    rw [integrable_prod_iff hgmeas.aestronglyMeasurable]
    constructor
    · filter_upwards [hprod_int] with z hz
      simpa [g] using hz
    · apply hexp_int.congr
      filter_upwards [hpairs] with z hz
      rcases hz with ⟨hz1, hz2⟩
      symm
      calc
        ∫ x, ‖g (z, x)‖ ∂Q =
            ∫ x, likelihood z.1 x * likelihood z.2 x ∂Q := by
          apply integral_congr_ae
          filter_upwards with x
          simp only [g, Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg (hnonneg z.1 hz1 x) (hnonneg z.2 hz2 x))]
        _ = Real.exp (lambda * z.1 * z.2) := hinner z.1 hz1 z.2 hz2
  have hpoint (x : X) :
      (∫ z : ℝ × ℝ, g (z, x) ∂π.prod ρ) =
        mixtureLikelihood π likelihood x * mixtureLikelihood ρ likelihood x := by
    change (∫ z : ℝ × ℝ, likelihood z.1 x * likelihood z.2 x ∂π.prod ρ) =
      (∫ θ, likelihood θ x ∂π) * ∫ θ, likelihood θ x ∂ρ
    exact integral_prod_mul (fun θ => likelihood θ x) (fun θ => likelihood θ x)
  have hmix_int :
      Integrable (fun x => mixtureLikelihood π likelihood x * mixtureLikelihood ρ likelihood x) Q :=
    hg_int.integral_prod_right.congr (ae_of_all _ hpoint)
  refine ⟨hmix_int, ?_⟩
  calc
    ∫ x, mixtureLikelihood π likelihood x * mixtureLikelihood ρ likelihood x ∂Q =
        ∫ x, ∫ z : ℝ × ℝ, g (z, x) ∂π.prod ρ ∂Q := by
          exact integral_congr_ae (ae_of_all _ fun x => (hpoint x).symm)
    _ = ∫ z : ℝ × ℝ, ∫ x, g (z, x) ∂Q ∂π.prod ρ :=
      (integral_integral_swap hg_int).symm
    _ = ∫ z : ℝ × ℝ, Real.exp (lambda * z.1 * z.2) ∂π.prod ρ := by
      apply integral_congr_ae
      filter_upwards [hpairs] with z hz
      exact hinner z.1 hz.1 z.2 hz.2
    _ = exponentialPriorEnergy π ρ lambda := by
      rw [exponentialPriorEnergy, integral_prod]
      exact hexp_int

/-- The [product of likelihood averages under two probability priors](hyp:π,ρ,likelihood) is
[integrable under the observation law](goal) when the priors are [supported on the interval of
parameters with absolute value at most the chosen radius](hyp:a,hsuppπ,hsuppρ), the [observation
law is a probability law](hyp:Q), the likelihood is [jointly measurable](hyp:hmeas) and
[nonnegative on that interval](hyp:hnonneg), and its supported fibres have [exponential inner
products at a nonnegative interaction scale](hyp:lambda,hlambda,hinner), with a [nonnegative
support radius](hyp:ha). -/
theorem integrable_mixtureLikelihood_mul_of_supported_exponentialGram
    (π ρ : Measure ℝ) (Q : Measure X) (likelihood : ℝ → X → ℝ)
    [IsProbabilityMeasure π] [IsProbabilityMeasure ρ] [IsProbabilityMeasure Q]
    (lambda a : ℝ) (hlambda : 0 ≤ lambda) (ha : 0 ≤ a)
    (hmeas : Measurable fun p : ℝ × X => likelihood p.1 p.2)
    (hnonneg : ∀ θ, |θ| ≤ a → ∀ x, 0 ≤ likelihood θ x)
    (hinner : ∀ θ, |θ| ≤ a → ∀ θ', |θ'| ≤ a →
      ∫ x, likelihood θ x * likelihood θ' x ∂Q = Real.exp (lambda * θ * θ'))
    (hsuppπ : π {θ | |θ| ≤ a} = 1) (hsuppρ : ρ {θ | |θ| ≤ a} = 1) :
    Integrable
      (fun x => mixtureLikelihood π likelihood x * mixtureLikelihood ρ likelihood x) Q := by
  exact (supported_cross_integrable_and_eq π ρ Q likelihood lambda a hlambda ha hmeas
    hnonneg hinner hsuppπ hsuppρ).1

/-- The [integrated squared difference between likelihood averages under two probability
priors](hyp:π0,π1,likelihood) [equals the alternating sum of their four exponential prior
energies](goal) when the priors are [supported on the interval of parameters with absolute value
at most the chosen radius](hyp:a,hsupp0,hsupp1), the [observation law is a probability
law](hyp:Q), the likelihood is [jointly measurable](hyp:hmeas) and [nonnegative on that
interval](hyp:hnonneg), and supported fibres have [exponential inner products at a nonnegative
interaction scale](hyp:lambda,hlambda,hinner), with a [nonnegative support radius](hyp:ha). -/
theorem integral_sq_mixtureLikelihood_sub_eq_exponentialPriorEnergy_of_supported
    (π0 π1 : Measure ℝ) (Q : Measure X) (likelihood : ℝ → X → ℝ)
    [IsProbabilityMeasure π0] [IsProbabilityMeasure π1] [IsProbabilityMeasure Q]
    (lambda a : ℝ) (hlambda : 0 ≤ lambda) (ha : 0 ≤ a)
    (hmeas : Measurable fun p : ℝ × X => likelihood p.1 p.2)
    (hnonneg : ∀ θ, |θ| ≤ a → ∀ x, 0 ≤ likelihood θ x)
    (hinner : ∀ θ, |θ| ≤ a → ∀ θ', |θ'| ≤ a →
      ∫ x, likelihood θ x * likelihood θ' x ∂Q = Real.exp (lambda * θ * θ'))
    (hsupp0 : π0 {θ | |θ| ≤ a} = 1) (hsupp1 : π1 {θ | |θ| ≤ a} = 1) :
    ∫ x, (mixtureLikelihood π0 likelihood x - mixtureLikelihood π1 likelihood x) ^ 2 ∂Q =
      exponentialPriorEnergy π0 π0 lambda - exponentialPriorEnergy π0 π1 lambda -
        exponentialPriorEnergy π1 π0 lambda + exponentialPriorEnergy π1 π1 lambda := by
  obtain ⟨h00i, h00⟩ := supported_cross_integrable_and_eq π0 π0 Q likelihood lambda a
    hlambda ha hmeas hnonneg hinner hsupp0 hsupp0
  obtain ⟨h01i, h01⟩ := supported_cross_integrable_and_eq π0 π1 Q likelihood lambda a
    hlambda ha hmeas hnonneg hinner hsupp0 hsupp1
  obtain ⟨h10i, h10⟩ := supported_cross_integrable_and_eq π1 π0 Q likelihood lambda a
    hlambda ha hmeas hnonneg hinner hsupp1 hsupp0
  obtain ⟨h11i, h11⟩ := supported_cross_integrable_and_eq π1 π1 Q likelihood lambda a
    hlambda ha hmeas hnonneg hinner hsupp1 hsupp1
  have hsq : (fun x => (mixtureLikelihood π0 likelihood x -
        mixtureLikelihood π1 likelihood x) ^ 2) = fun x =>
      mixtureLikelihood π0 likelihood x * mixtureLikelihood π0 likelihood x -
        mixtureLikelihood π0 likelihood x * mixtureLikelihood π1 likelihood x -
        mixtureLikelihood π1 likelihood x * mixtureLikelihood π0 likelihood x +
        mixtureLikelihood π1 likelihood x * mixtureLikelihood π1 likelihood x := by
    funext x
    ring
  rw [hsq]
  change ∫ x, (((fun x => mixtureLikelihood π0 likelihood x * mixtureLikelihood π0 likelihood x) -
      (fun x => mixtureLikelihood π0 likelihood x * mixtureLikelihood π1 likelihood x) -
      (fun x => mixtureLikelihood π1 likelihood x * mixtureLikelihood π0 likelihood x)) +
      (fun x => mixtureLikelihood π1 likelihood x * mixtureLikelihood π1 likelihood x)) x ∂Q = _
  calc
    _ = (∫ x, ((fun x => mixtureLikelihood π0 likelihood x * mixtureLikelihood π0 likelihood x) -
          (fun x => mixtureLikelihood π0 likelihood x * mixtureLikelihood π1 likelihood x) -
          (fun x => mixtureLikelihood π1 likelihood x * mixtureLikelihood π0 likelihood x)) x ∂Q) +
        ∫ x, mixtureLikelihood π1 likelihood x * mixtureLikelihood π1 likelihood x ∂Q :=
      integral_add ((h00i.sub h01i).sub h10i) h11i
    _ = ((∫ x, ((fun x => mixtureLikelihood π0 likelihood x * mixtureLikelihood π0 likelihood x) -
          (fun x => mixtureLikelihood π0 likelihood x * mixtureLikelihood π1 likelihood x)) x ∂Q) -
          ∫ x, mixtureLikelihood π1 likelihood x * mixtureLikelihood π0 likelihood x ∂Q) +
        ∫ x, mixtureLikelihood π1 likelihood x * mixtureLikelihood π1 likelihood x ∂Q := by
      congr 1
      exact integral_sub (h00i.sub h01i) h10i
    _ = ((∫ x, mixtureLikelihood π0 likelihood x * mixtureLikelihood π0 likelihood x ∂Q) -
          ∫ x, mixtureLikelihood π0 likelihood x * mixtureLikelihood π1 likelihood x ∂Q -
          ∫ x, mixtureLikelihood π1 likelihood x * mixtureLikelihood π0 likelihood x ∂Q) +
        ∫ x, mixtureLikelihood π1 likelihood x * mixtureLikelihood π1 likelihood x ∂Q := by
      congr 2
      exact integral_sub h00i h01i
    _ = _ := by rw [h00, h01, h10, h11]

/-- The [integrated squared difference between likelihood averages under two probability
priors](hyp:π0,π1,likelihood) is [at most four times the unmatched exponential-series tail](goal)
when their [moments agree through the chosen degree](hyp:degree,hmom), the priors are [supported on
the interval of parameters with absolute value at most the chosen radius](hyp:a,hsupp0,hsupp1),
the [observation law is a probability law](hyp:Q), the likelihood is [jointly
measurable](hyp:hmeas) and [nonnegative on that interval](hyp:hnonneg), and supported fibres have
[exponential inner products at a nonnegative interaction scale](hyp:lambda,hlambda,hinner), with
a [nonnegative support radius](hyp:ha). -/
theorem integral_sq_mixtureLikelihood_sub_le_tail_of_supported
    (π0 π1 : Measure ℝ) (Q : Measure X) (likelihood : ℝ → X → ℝ)
    [IsProbabilityMeasure π0] [IsProbabilityMeasure π1] [IsProbabilityMeasure Q]
    (lambda a : ℝ) (degree : ℕ) (hlambda : 0 ≤ lambda) (ha : 0 ≤ a)
    (hmeas : Measurable fun p : ℝ × X => likelihood p.1 p.2)
    (hnonneg : ∀ θ, |θ| ≤ a → ∀ x, 0 ≤ likelihood θ x)
    (hinner : ∀ θ, |θ| ≤ a → ∀ θ', |θ'| ≤ a →
      ∫ x, likelihood θ x * likelihood θ' x ∂Q = Real.exp (lambda * θ * θ'))
    (hsupp0 : π0 {θ | |θ| ≤ a} = 1) (hsupp1 : π1 {θ | |θ| ≤ a} = 1)
    (hmom : ∀ n ≤ degree, ∫ θ, θ ^ n ∂π0 = ∫ θ, θ ^ n ∂π1) :
    ∫ x, (mixtureLikelihood π0 likelihood x - mixtureLikelihood π1 likelihood x) ^ 2 ∂Q
      ≤ 4 * exponentialSeriesTail degree (lambda * a ^ 2) := by
  rw [integral_sq_mixtureLikelihood_sub_eq_exponentialPriorEnergy_of_supported
    π0 π1 Q likelihood lambda a hlambda ha hmeas hnonneg hinner hsupp0 hsupp1]
  exact exponentialPriorEnergy_quadratic_le_tail π0 π1 lambda a degree hlambda ha hsupp0 hsupp1
    hmom

/-- The [predictive laws formed from two probability priors](hyp:π0,π1) and an [experiment kernel
with probability fibres](hyp:K,hK) are [within the square root of the unmatched exponential-series
tail in total variation](goal) when their [moments agree through the chosen degree](hyp:degree,hmom),
the priors are [supported on the interval of parameters with absolute value at most the chosen
radius](hyp:a,hsupp0,hsupp1), the [common dominating observation law is a probability
law](hyp:Q), and the [likelihood family](hyp:likelihood) is [jointly measurable](hyp:hmeas) while
only on that interval it is [nonnegative](hyp:hnonneg), [represents the kernel densities](hyp:hdensity),
and has [exponential inner products at a nonnegative interaction scale](hyp:lambda,hlambda,hinner),
with a [nonnegative support radius](hyp:ha). -/
theorem momentMatchedMixture_tv_le_sqrt_tail_of_supported
    (π0 π1 : Measure ℝ) (K : Kernel ℝ X) (Q : Measure X)
    (likelihood : ℝ → X → ℝ) [IsProbabilityMeasure π0] [IsProbabilityMeasure π1]
    [IsProbabilityMeasure Q] (hK : ∀ θ, IsProbabilityMeasure (K θ))
    (lambda a : ℝ) (degree : ℕ) (hlambda : 0 ≤ lambda) (ha : 0 ≤ a)
    (hmeas : Measurable fun p : ℝ × X => likelihood p.1 p.2)
    (hnonneg : ∀ θ, |θ| ≤ a → ∀ x, 0 ≤ likelihood θ x)
    (hdensity : ∀ θ, |θ| ≤ a →
      K θ = Q.withDensity fun x => ENNReal.ofReal (likelihood θ x))
    (hinner : ∀ θ, |θ| ≤ a → ∀ θ', |θ'| ≤ a →
      ∫ x, likelihood θ x * likelihood θ' x ∂Q = Real.exp (lambda * θ * θ'))
    (hsupp0 : π0 {θ | |θ| ≤ a} = 1) (hsupp1 : π1 {θ | |θ| ≤ a} = 1)
    (hmom : ∀ n ≤ degree, ∫ θ, θ ^ n ∂π0 = ∫ θ, θ ^ n ∂π1) :
    Causalean.Stat.tvDist (priorPredictive π0 K) (priorPredictive π1 K) ≤
      Real.sqrt (exponentialSeriesTail degree (lambda * a ^ 2)) := by
  have hpred (π : Measure ℝ) [IsProbabilityMeasure π]
      (hsupp : π {θ | |θ| ≤ a} = 1) :
      priorPredictive π K =
        Q.withDensity fun x => ENNReal.ofReal (mixtureLikelihood π likelihood x) :=
    priorPredictive_eq_withDensity_mixtureLikelihood_of_supported
      π K Q likelihood hK a hsupp hmeas hnonneg hdensity
  have hmix_meas (π : Measure ℝ) [IsProbabilityMeasure π] :
      Measurable (mixtureLikelihood π likelihood) :=
    measurable_mixtureLikelihood π likelihood hmeas
  have hmix_nonneg (π : Measure ℝ) [IsProbabilityMeasure π]
      (hsupp : π {θ | |θ| ≤ a} = 1) (x : X) :
      0 ≤ mixtureLikelihood π likelihood x :=
    mixtureLikelihood_nonnegative_of_supported π likelihood a hsupp hnonneg x
  have hsq0 : Integrable (fun x =>
      mixtureLikelihood π0 likelihood x * mixtureLikelihood π0 likelihood x) Q :=
    integrable_mixtureLikelihood_mul_of_supported_exponentialGram
      π0 π0 Q likelihood lambda a hlambda ha hmeas hnonneg hinner hsupp0 hsupp0
  have hsq1 : Integrable (fun x =>
      mixtureLikelihood π1 likelihood x * mixtureLikelihood π1 likelihood x) Q :=
    integrable_mixtureLikelihood_mul_of_supported_exponentialGram
      π1 π1 Q likelihood lambda a hlambda ha hmeas hnonneg hinner hsupp1 hsupp1
  have hmajorant : Integrable (fun x => 2 *
      (mixtureLikelihood π0 likelihood x * mixtureLikelihood π0 likelihood x +
        mixtureLikelihood π1 likelihood x * mixtureLikelihood π1 likelihood x)) Q :=
    (hsq0.add hsq1).const_mul 2
  have hdiff_sq : Integrable (fun x =>
      (mixtureLikelihood π0 likelihood x - mixtureLikelihood π1 likelihood x) ^ 2) Q := by
    apply hmajorant.mono'
      ((hmix_meas π0).sub (hmix_meas π1) |>.pow_const 2).aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [Pi.sub_apply]
    nlinarith [sq_nonneg (mixtureLikelihood π0 likelihood x +
      mixtureLikelihood π1 likelihood x)]
  let t := exponentialSeriesTail degree (lambda * a ^ 2)
  have ht : 0 ≤ t := by
    unfold t exponentialSeriesTail
    apply tsum_nonneg
    intro n
    by_cases hn : degree < n
    · simp only [if_pos hn]
      positivity
    · simp only [if_neg hn]
      exact le_rfl
  letI : IsProbabilityMeasure (priorPredictive π0 K) :=
    priorPredictive_isProbability π0 K hK
  letI : IsProbabilityMeasure (priorPredictive π1 K) :=
    priorPredictive_isProbability π1 K hK
  have htv := tvDist_le_half_sqrt_integral_sq_density_sub
    (priorPredictive π0 K) (priorPredictive π1 K) Q
    (mixtureLikelihood π0 likelihood) (mixtureLikelihood π1 likelihood)
    (hmix_meas π0) (hmix_meas π1) (hmix_nonneg π0 hsupp0) (hmix_nonneg π1 hsupp1)
    (hpred π0 hsupp0) (hpred π1 hsupp1) hdiff_sq
  have htail := integral_sq_mixtureLikelihood_sub_le_tail_of_supported
    π0 π1 Q likelihood lambda a degree hlambda ha hmeas hnonneg hinner hsupp0 hsupp1 hmom
  change _ ≤ Real.sqrt t
  calc
    Causalean.Stat.tvDist (priorPredictive π0 K) (priorPredictive π1 K) ≤
        (1 / 2 : ℝ) * Real.sqrt
          (∫ x, (mixtureLikelihood π0 likelihood x -
            mixtureLikelihood π1 likelihood x) ^ 2 ∂Q) := htv
    _ ≤ (1 / 2 : ℝ) * Real.sqrt (4 * t) := by
      gcongr
    _ = Real.sqrt t := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      rw [show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      ring

/-- The [finite products over the chosen number of independent coordinates](hyp:d) of predictive
laws formed from [two probability priors](hyp:π0,π1) and an [experiment kernel with probability
fibres](hyp:K,hK) are [within the dimension times the square root of the unmatched exponential-series
tail in total variation](goal) when their [moments agree through the chosen degree](hyp:degree,hmom),
the priors are [supported on the interval of parameters with absolute value at most the chosen
radius](hyp:a,hsupp0,hsupp1), the [common dominating observation law is a probability
law](hyp:Q), and the [likelihood family](hyp:likelihood) is [jointly measurable](hyp:hmeas) while
only on that interval it is [nonnegative](hyp:hnonneg), [represents the kernel densities](hyp:hdensity),
and has [exponential inner products at a nonnegative interaction scale](hyp:lambda,hlambda,hinner),
with a [nonnegative support radius](hyp:ha). -/
theorem momentMatchedProductMixture_tv_le_of_supported
    (d : ℕ) (π0 π1 : Measure ℝ) (K : Kernel ℝ X) (Q : Measure X)
    (likelihood : ℝ → X → ℝ) [IsProbabilityMeasure π0] [IsProbabilityMeasure π1]
    [IsProbabilityMeasure Q] (hK : ∀ θ, IsProbabilityMeasure (K θ))
    (lambda a : ℝ) (degree : ℕ) (hlambda : 0 ≤ lambda) (ha : 0 ≤ a)
    (hmeas : Measurable fun p : ℝ × X => likelihood p.1 p.2)
    (hnonneg : ∀ θ, |θ| ≤ a → ∀ x, 0 ≤ likelihood θ x)
    (hdensity : ∀ θ, |θ| ≤ a →
      K θ = Q.withDensity fun x => ENNReal.ofReal (likelihood θ x))
    (hinner : ∀ θ, |θ| ≤ a → ∀ θ', |θ'| ≤ a →
      ∫ x, likelihood θ x * likelihood θ' x ∂Q = Real.exp (lambda * θ * θ'))
    (hsupp0 : π0 {θ | |θ| ≤ a} = 1) (hsupp1 : π1 {θ | |θ| ≤ a} = 1)
    (hmom : ∀ n ≤ degree, ∫ θ, θ ^ n ∂π0 = ∫ θ, θ ^ n ∂π1) :
    Causalean.Stat.tvDist (productPriorPredictive d π0 K) (productPriorPredictive d π1 K) ≤
      d * Real.sqrt (exponentialSeriesTail degree (lambda * a ^ 2)) := by
  letI : IsProbabilityMeasure (priorPredictive π0 K) :=
    priorPredictive_isProbability π0 K hK
  letI : IsProbabilityMeasure (priorPredictive π1 K) :=
    priorPredictive_isProbability π1 K hK
  unfold productPriorPredictive
  calc
    Causalean.Stat.tvDist (Measure.pi fun _ : Fin d => priorPredictive π0 K)
        (Measure.pi fun _ : Fin d => priorPredictive π1 K) ≤
        d * Causalean.Stat.tvDist (priorPredictive π0 K) (priorPredictive π1 K) :=
      tvDist_pi_iid_le d _ _
    _ ≤ d * Real.sqrt (exponentialSeriesTail degree (lambda * a ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (momentMatchedMixture_tv_le_sqrt_tail_of_supported
          π0 π1 K Q likelihood hK lambda a degree hlambda ha hmeas hnonneg hdensity hinner
          hsupp0 hsupp1 hmom)
        (Nat.cast_nonneg d)


end Causalean.Stat.Minimax.MomentMatchedMixture

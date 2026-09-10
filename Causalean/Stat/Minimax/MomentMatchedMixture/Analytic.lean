import Causalean.Stat.Minimax.Mixture
import Causalean.Stat.Minimax.MomentMatchedMixture.ExponentialEnergy
import Causalean.Stat.Minimax.ChiSquared
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Moment matching and likelihood inner products

This module turns an exponential likelihood inner-product identity and agreement of bounded
prior moments into an explicit total-variation bound for the corresponding predictive mixtures.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Causalean.Stat.Minimax.MomentMatchedMixture

variable {X : Type*} [MeasurableSpace X]

/-- Given [a real-valued prior](hyp:π), [a parameter-indexed likelihood family](hyp:likelihood),
and [an observation](hyp:x), the [mixture likelihood](goal) is the prior average of the component
likelihoods at that observation. -/
noncomputable def mixtureLikelihood (π : Measure ℝ) (likelihood : ℝ → X → ℝ) (x : X) : ℝ :=
  ∫ θ, likelihood θ x ∂π

/-- Given [a probability prior](hyp:π), [an experiment kernel](hyp:K), [a σ-finite dominating
measure](hyp:Q), and [a jointly measurable nonnegative likelihood family](hyp:likelihood,hmeas,hnonneg),
if [every experiment law is a probability law](hyp:hK) and [has the stated density against the
dominating measure](hyp:hdensity), then [the prior-predictive law has density equal to the prior
average of the component likelihoods](goal). -/
theorem priorPredictive_eq_withDensity_mixtureLikelihood
    (π : Measure ℝ) (K : Kernel ℝ X) (Q : Measure X) (likelihood : ℝ → X → ℝ)
    [IsProbabilityMeasure π] [SigmaFinite Q]
    (hK : ∀ θ, IsProbabilityMeasure (K θ))
    (hmeas : Measurable fun p : ℝ × X => likelihood p.1 p.2)
    (hnonneg : ∀ θ x, 0 ≤ likelihood θ x)
    (hdensity : ∀ θ, K θ = Q.withDensity fun x => ENNReal.ofReal (likelihood θ x)) :
    priorPredictive π K =
      Q.withDensity fun x => ENNReal.ofReal (mixtureLikelihood π likelihood x) := by
  -- Sigma-finiteness of the dominator is essential for swapping the two lower
  -- integrals.  Without it the claim is false: for counting measure on an
  -- uncountable Borel space, Dirac fibres have singleton-indicator likelihoods,
  -- whose pointwise prior averages vanish under a nonatomic prior even though the
  -- predictive measure is that prior.  Here the probability-fibre hypothesis makes
  -- the nonnegative joint likelihood integrable under `π.prod Q`, so the Bochner
  -- prior average agrees a.e. with its Tonelli lower-integral version.
  have hfiber (θ : ℝ) :
      ∫⁻ x, ENNReal.ofReal (likelihood θ x) ∂Q = 1 := by
    calc
      ∫⁻ x, ENNReal.ofReal (likelihood θ x) ∂Q =
          (Q.withDensity fun x => ENNReal.ofReal (likelihood θ x)) Set.univ := by
            rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      _ = K θ Set.univ := by rw [hdensity θ]
      _ = 1 := isProbabilityMeasure_iff.mp (hK θ)
  have hjoint : Integrable (fun p : ℝ × X => likelihood p.1 p.2) (π.prod Q) := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal
      (ae_of_all _ fun p : ℝ × X => hnonneg p.1 p.2)).2
    rw [lintegral_prod _ hmeas.ennreal_ofReal.aemeasurable]
    simp_rw [hfiber]
    simp
  have hsections : ∀ᵐ x ∂Q, Integrable (fun θ => likelihood θ x) π :=
    hjoint.prod_left_ae
  have haverage : ∀ᵐ x ∂Q,
      ENNReal.ofReal (mixtureLikelihood π likelihood x) =
        ∫⁻ θ, ENNReal.ofReal (likelihood θ x) ∂π := by
    filter_upwards [hsections] with x hx
    exact ofReal_integral_eq_lintegral_ofReal hx
      (ae_of_all _ fun θ => hnonneg θ x)
  refine Measure.ext fun A hA => ?_
  rw [priorPredictive_apply π K hA, withDensity_apply _ hA]
  simp_rw [hdensity, withDensity_apply _ hA]
  calc
    ∫⁻ θ, ∫⁻ x in A, ENNReal.ofReal (likelihood θ x) ∂Q ∂π =
        ∫⁻ x in A, ∫⁻ θ, ENNReal.ofReal (likelihood θ x) ∂π ∂Q := by
          apply lintegral_lintegral_swap
          exact hmeas.ennreal_ofReal.aemeasurable
    _ = ∫⁻ x in A, ENNReal.ofReal (mixtureLikelihood π likelihood x) ∂Q := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae haverage] with x hx
      exact hx.symm

/-- Given [two probability priors](hyp:π0,π1), [a probability dominating measure](hyp:Q),
[a jointly measurable nonnegative likelihood family](hyp:likelihood,hmeas,hnonneg),
[a nonnegative interaction scale](hyp:lambda,hlambda), and [a nonnegative support radius](hyp:a,ha),
if [likelihood inner products have the exponential product form](hyp:hinner) and [both priors are
supported within the radius](hyp:hsupp0,hsupp1), then [the squared distance between their mixture
likelihoods equals the alternating sum of the four exponential prior energies](goal). -/
theorem integral_sq_mixtureLikelihood_sub_eq_exponentialPriorEnergy
    (π0 π1 : Measure ℝ) (Q : Measure X) (likelihood : ℝ → X → ℝ)
    [IsProbabilityMeasure π0] [IsProbabilityMeasure π1] [IsProbabilityMeasure Q]
    (lambda a : ℝ) (hlambda : 0 ≤ lambda) (ha : 0 ≤ a)
    (hmeas : Measurable fun p : ℝ × X => likelihood p.1 p.2)
    (hnonneg : ∀ θ x, 0 ≤ likelihood θ x)
    (hinner : ∀ θ θ',
      ∫ x, likelihood θ x * likelihood θ' x ∂Q = Real.exp (lambda * θ * θ'))
    (hsupp0 : π0 {θ | |θ| ≤ a} = 1) (hsupp1 : π1 {θ | |θ| ≤ a} = 1) :
    ∫ x, (mixtureLikelihood π0 likelihood x - mixtureLikelihood π1 likelihood x) ^ 2 ∂Q =
      exponentialPriorEnergy π0 π0 lambda - exponentialPriorEnergy π0 π1 lambda -
        exponentialPriorEnergy π1 π0 lambda + exponentialPriorEnergy π1 π1 lambda := by
  -- Prove the four cross-term identities before expanding the square.  For priors
  -- `π,ρ`, Tonelli applied to the nonnegative jointly measurable likelihood product
  -- identifies
  --   `∫ (∫ Lθ dπ) (∫ Lθ' dρ) dQ`
  -- with the iterated prior integral of `∫ Lθ Lθ' dQ`; `hinner` then gives the
  -- corresponding `exponentialPriorEnergy`.  The support bounds make every such
  -- energy finite (bounded by `exp (lambda * a^2)`), which supplies the Bochner
  -- integrability needed to pass back from `lintegral` and expand the signed square.
  have hset : MeasurableSet {θ : ℝ | |θ| ≤ a} :=
    measurableSet_le continuous_abs.measurable measurable_const
  have hsupp_ae (π : Measure ℝ) [IsProbabilityMeasure π]
      (hsupp : π {θ | |θ| ≤ a} = 1) : ∀ᵐ θ ∂π, |θ| ≤ a := by
    change {θ : ℝ | |θ| ≤ a} ∈ ae π
    rw [mem_ae_iff, measure_compl hset (measure_ne_top π _), measure_univ, hsupp,
      tsub_self]
  have hprod_int (θ θ' : ℝ) :
      Integrable (fun x => likelihood θ x * likelihood θ' x) Q := by
    by_contra h
    have heq := hinner θ θ'
    rw [integral_undef h] at heq
    exact (Real.exp_ne_zero _ heq.symm)
  have hcross (π ρ : Measure ℝ) [IsProbabilityMeasure π] [IsProbabilityMeasure ρ]
      (hsuppπ : π {θ | |θ| ≤ a} = 1) (hsuppρ : ρ {θ | |θ| ≤ a} = 1) :
      Integrable (fun x => mixtureLikelihood π likelihood x * mixtureLikelihood ρ likelihood x) Q ∧
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
      filter_upwards [hsupp_ae π hsuppπ] with θ hθ
      filter_upwards [hsupp_ae ρ hsuppρ] with θ' hθ'
      exact ⟨hθ, hθ'⟩
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
      · filter_upwards with z
        simpa [g] using hprod_int z.1 z.2
      · convert hexp_int using 1
        funext z
        calc
          ∫ x, ‖g (z, x)‖ ∂Q =
              ∫ x, likelihood z.1 x * likelihood z.2 x ∂Q := by
                apply integral_congr_ae
                filter_upwards with x
                simp only [g, Real.norm_eq_abs,
                  abs_of_nonneg (mul_nonneg (hnonneg _ _) (hnonneg _ _))]
          _ = Real.exp (lambda * z.1 * z.2) := hinner z.1 z.2
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
        filter_upwards with z
        exact hinner z.1 z.2
      _ = exponentialPriorEnergy π ρ lambda := by
        rw [exponentialPriorEnergy, integral_prod]
        exact hexp_int
  obtain ⟨h00i, h00⟩ := hcross π0 π0 hsupp0 hsupp0
  obtain ⟨h01i, h01⟩ := hcross π0 π1 hsupp0 hsupp1
  obtain ⟨h10i, h10⟩ := hcross π1 π0 hsupp1 hsupp0
  obtain ⟨h11i, h11⟩ := hcross π1 π1 hsupp1 hsupp1
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

/-- Given [two probability priors](hyp:π0,π1), [a probability dominating measure](hyp:Q),
[a jointly measurable nonnegative likelihood family](hyp:likelihood,hmeas,hnonneg),
[a nonnegative interaction scale](hyp:lambda,hlambda), [a nonnegative support radius](hyp:a,ha),
and [a matching degree](hyp:degree), if [likelihood inner products have the exponential product
form](hyp:hinner), [both priors are supported within the radius](hyp:hsupp0,hsupp1), and [their
moments agree through that degree](hyp:hmom), then [the squared distance between their mixture
likelihoods is at most four times the unmatched exponential-series tail](goal). -/
theorem integral_sq_mixtureLikelihood_sub_le_tail
    (π0 π1 : Measure ℝ) (Q : Measure X) (likelihood : ℝ → X → ℝ)
    [IsProbabilityMeasure π0] [IsProbabilityMeasure π1] [IsProbabilityMeasure Q]
    (lambda a : ℝ) (degree : ℕ)
    (hlambda : 0 ≤ lambda) (ha : 0 ≤ a)
    (hmeas : Measurable fun p : ℝ × X => likelihood p.1 p.2)
    (hnonneg : ∀ θ x, 0 ≤ likelihood θ x)
    (hinner : ∀ θ θ',
      ∫ x, likelihood θ x * likelihood θ' x ∂Q = Real.exp (lambda * θ * θ'))
    (hsupp0 : π0 {θ | |θ| ≤ a} = 1) (hsupp1 : π1 {θ | |θ| ≤ a} = 1)
    (hmom : ∀ n ≤ degree, ∫ θ, θ ^ n ∂π0 = ∫ θ, θ ^ n ∂π1) :
    ∫ x, (mixtureLikelihood π0 likelihood x - mixtureLikelihood π1 likelihood x) ^ 2 ∂Q
      ≤ 4 * exponentialSeriesTail degree (lambda * a ^ 2) := by
  rw [integral_sq_mixtureLikelihood_sub_eq_exponentialPriorEnergy π0 π1 Q likelihood
    lambda a hlambda ha hmeas hnonneg hinner hsupp0 hsupp1]
  exact exponentialPriorEnergy_quadratic_le_tail π0 π1 lambda a degree hlambda ha hsupp0 hsupp1
    hmom

/-- Given [a probability prior](hyp:π), [an experiment kernel](hyp:K), [a dominating measure](hyp:Q),
and [a jointly measurable nonnegative likelihood family](hyp:likelihood,hmeas,hnonneg), if
[each experiment law has the stated density](hyp:hdensity), then [the prior-predictive mixture is
absolutely continuous with respect to the dominating measure](goal). -/
theorem priorPredictive_absolutelyContinuous
    (π : Measure ℝ) (K : Kernel ℝ X) (Q : Measure X) (likelihood : ℝ → X → ℝ)
    [IsProbabilityMeasure π]
    (hmeas : Measurable fun p : ℝ × X => likelihood p.1 p.2)
    (hnonneg : ∀ θ x, 0 ≤ likelihood θ x)
    (hdensity : ∀ θ, K θ = Q.withDensity fun x => ENNReal.ofReal (likelihood θ x)) :
    priorPredictive π K ≪ Q := by
  refine Measure.AbsolutelyContinuous.mk fun A hA hQA => ?_
  rw [priorPredictive_apply π K hA]
  rw [lintegral_eq_zero_iff (Kernel.measurable_coe K hA)]
  refine ae_of_all π fun θ => ?_
  change K θ A = 0
  rw [hdensity θ]
  exact withDensity_absolutelyContinuous Q _ hQA

/-- Given [two probability laws](hyp:μ,ν), [a probability dominating law](hyp:Q), and
[two measurable nonnegative densities](hyp:p,q,hpmeas,hqmeas,hpnonneg,hqnonneg), if [the laws have
those densities](hyp:hμ,hν) and [their squared difference is integrable](hyp:hint), then [their
total variation distance is at most half the square root of the integrated squared density
difference](goal). -/
theorem tvDist_le_half_sqrt_integral_sq_density_sub
    (μ ν Q : Measure X) (p q : X → ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure Q]
    (hpmeas : Measurable p) (hqmeas : Measurable q)
    (hpnonneg : ∀ x, 0 ≤ p x) (hqnonneg : ∀ x, 0 ≤ q x)
    (hμ : μ = Q.withDensity fun x => ENNReal.ofReal (p x))
    (hν : ν = Q.withDensity fun x => ENNReal.ofReal (q x))
    (hint : Integrable (fun x => (p x - q x) ^ 2) Q) :
    Causalean.Stat.tvDist μ ν ≤ (1 / 2 : ℝ) * Real.sqrt (∫ x, (p x - q x) ^ 2 ∂Q) := by
  have hμac : μ ≪ Q := by
    rw [hμ]
    exact withDensity_absolutelyContinuous Q _
  have hνac : ν ≪ Q := by
    rw [hν]
    exact withDensity_absolutelyContinuous Q _
  have hrnp_enn : μ.rnDeriv Q =ᵐ[Q] fun x => ENNReal.ofReal (p x) := by
    rw [hμ]
    exact Measure.rnDeriv_withDensity Q hpmeas.ennreal_ofReal
  have hrnq_enn : ν.rnDeriv Q =ᵐ[Q] fun x => ENNReal.ofReal (q x) := by
    rw [hν]
    exact Measure.rnDeriv_withDensity Q hqmeas.ennreal_ofReal
  have hrnp : (fun x => (μ.rnDeriv Q x).toReal) =ᵐ[Q] p := by
    filter_upwards [hrnp_enn] with x hx
    rw [hx, ENNReal.toReal_ofReal (hpnonneg x)]
  have hrnq : (fun x => (ν.rnDeriv Q x).toReal) =ᵐ[Q] q := by
    filter_upwards [hrnq_enn] with x hx
    rw [hx, ENNReal.toReal_ofReal (hqnonneg x)]
  have hpint : Integrable p Q := Measure.integrable_toReal_rnDeriv.congr hrnp
  have hqint : Integrable q Q := Measure.integrable_toReal_rnDeriv.congr hrnq
  have hdiff : Integrable (fun x => p x - q x) Q := hpint.sub hqint
  have hp_one : ∫ x, p x ∂Q = 1 := by
    calc
      ∫ x, p x ∂Q = ∫ x, (μ.rnDeriv Q x).toReal ∂Q := integral_congr_ae hrnp.symm
      _ = μ.real Set.univ := Measure.integral_toReal_rnDeriv hμac
      _ = 1 := by simp
  have hq_one : ∫ x, q x ∂Q = 1 := by
    calc
      ∫ x, q x ∂Q = ∫ x, (ν.rnDeriv Q x).toReal ∂Q := integral_congr_ae hrnq.symm
      _ = ν.real Set.univ := Measure.integral_toReal_rnDeriv hνac
      _ = 1 := by simp
  have hdiff_zero : ∫ x, (p x - q x) ∂Q = 0 := by
    rw [integral_sub hpint hqint, hp_one, hq_one, sub_self]
  have hscheffe :
      Causalean.Stat.tvDist μ ν ≤ (1 / 2 : ℝ) * ∫ x, |p x - q x| ∂Q := by
    refine ciSup_le fun A => ?_
    obtain ⟨A, hA⟩ := A
    have hgap : μ.real A - ν.real A = ∫ x in A, (p x - q x) ∂Q := by
      calc
        μ.real A - ν.real A =
            (∫ x in A, (μ.rnDeriv Q x).toReal ∂Q) -
              ∫ x in A, (ν.rnDeriv Q x).toReal ∂Q := by
                rw [Measure.setIntegral_toReal_rnDeriv hμac,
                  Measure.setIntegral_toReal_rnDeriv hνac]
        _ = (∫ x in A, p x ∂Q) - ∫ x in A, q x ∂Q := by
              rw [integral_congr_ae (ae_restrict_of_ae hrnp),
                integral_congr_ae (ae_restrict_of_ae hrnq)]
        _ = ∫ x in A, (p x - q x) ∂Q :=
              (integral_sub hpint.integrableOn hqint.integrableOn).symm
    rw [hgap]
    exact Causalean.Stat.abs_setIntegral_le_half_integral_abs_of_integral_eq_zero
      hdiff hdiff_zero hA
  have hmeasdiff : AEStronglyMeasurable (fun x => p x - q x) Q :=
    (hpmeas.sub hqmeas).aestronglyMeasurable
  have hdiffL2 : MemLp (fun x => p x - q x) 2 Q :=
    (memLp_two_iff_integrable_sq hmeasdiff).2 hint
  have habsL2 : MemLp (fun x => |p x - q x|) (ENNReal.ofReal 2) Q := by
    have h := hdiffL2.norm
    simp only [Real.norm_eq_abs] at h
    simpa using h
  have honeL2 : MemLp (fun _ : X => (1 : ℝ)) (ENNReal.ofReal 2) Q := by
    simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : X => (1 : ℝ)) 2 Q)
  have hholder :
      ∫ x, |p x - q x| * (1 : ℝ) ∂Q
        ≤ (∫ x, |p x - q x| ^ (2 : ℝ) ∂Q) ^ (1 / (2 : ℝ))
          * (∫ _x : X, (1 : ℝ) ^ (2 : ℝ) ∂Q) ^ (1 / (2 : ℝ)) :=
    integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall fun x => abs_nonneg _)
      (Filter.Eventually.of_forall fun _ => zero_le_one) habsL2 honeL2
  have hL1 : ∫ x, |p x - q x| ∂Q ≤ Real.sqrt (∫ x, (p x - q x) ^ 2 ∂Q) := by
    have hsquare :
        ∫ x, |p x - q x| ^ (2 : ℝ) ∂Q = ∫ x, (p x - q x) ^ 2 ∂Q := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Real.rpow_two, sq_abs]
    rw [show (∫ _x : X, (1 : ℝ) ^ (2 : ℝ) ∂Q) ^ (1 / (2 : ℝ)) = 1 by simp,
      mul_one, hsquare] at hholder
    simpa [Real.sqrt_eq_rpow] using hholder
  exact hscheffe.trans (mul_le_mul_of_nonneg_left hL1 (by norm_num))

/-- Given [two probability priors](hyp:π0,π1), [a probability experiment kernel](hyp:K,hK),
[a probability dominating law](hyp:Q), [a jointly measurable nonnegative likelihood
family](hyp:likelihood,hmeas,hnonneg), [a nonnegative interaction scale](hyp:lambda,hlambda),
[a nonnegative support radius](hyp:a,ha), and [a matching degree](hyp:degree), if [each experiment
law has the stated density](hyp:hdensity), [likelihood inner products have the exponential product
form](hyp:hinner), [both priors are supported within the radius](hyp:hsupp0,hsupp1), and [their
moments agree through that degree](hyp:hmom), then [the two one-coordinate prior-predictive
mixtures are within the square root of the explicit unmatched series tail in total variation](goal). -/
theorem momentMatchedMixture_tv_le_sqrt_tail
    (π0 π1 : Measure ℝ) (K : Kernel ℝ X) (Q : Measure X)
    (likelihood : ℝ → X → ℝ) [IsProbabilityMeasure π0] [IsProbabilityMeasure π1]
    [IsProbabilityMeasure Q] (hK : ∀ θ, IsProbabilityMeasure (K θ))
    (lambda a : ℝ) (degree : ℕ)
    (hlambda : 0 ≤ lambda) (ha : 0 ≤ a)
    (hmeas : Measurable fun p : ℝ × X => likelihood p.1 p.2)
    (hnonneg : ∀ θ x, 0 ≤ likelihood θ x)
    (hdensity : ∀ θ, K θ = Q.withDensity fun x => ENNReal.ofReal (likelihood θ x))
    (hinner : ∀ θ θ',
      ∫ x, likelihood θ x * likelihood θ' x ∂Q = Real.exp (lambda * θ * θ'))
    (hsupp0 : π0 {θ | |θ| ≤ a} = 1) (hsupp1 : π1 {θ | |θ| ≤ a} = 1)
    (hmom : ∀ n ≤ degree, ∫ θ, θ ^ n ∂π0 = ∫ θ, θ ^ n ∂π1) :
    Causalean.Stat.tvDist (priorPredictive π0 K) (priorPredictive π1 K) ≤
      Real.sqrt (exponentialSeriesTail degree (lambda * a ^ 2)) := by
  -- Rewrite both predictive measures with `priorPredictive_eq_withDensity_mixtureLikelihood`.
  -- Establish integrability of the squared density difference using the same four
  -- nonnegative cross terms as the energy identity (or an integrable pointwise upper
  -- bound by the sum of the two squared mixture likelihoods).  Then combine
  -- `tvDist_le_half_sqrt_integral_sq_density_sub` with
  -- `integral_sq_mixtureLikelihood_sub_le_tail`; monotonicity of `sqrt` and
  -- `sqrt (4 * t) = 2 * sqrt t` finish, using nonnegativity of the series tail.
  have hpred (π : Measure ℝ) [IsProbabilityMeasure π] :
      priorPredictive π K =
        Q.withDensity fun x => ENNReal.ofReal (mixtureLikelihood π likelihood x) := by
    have hfiber (θ : ℝ) :
        ∫⁻ x, ENNReal.ofReal (likelihood θ x) ∂Q = 1 := by
      calc
        ∫⁻ x, ENNReal.ofReal (likelihood θ x) ∂Q =
            (Q.withDensity fun x => ENNReal.ofReal (likelihood θ x)) Set.univ := by
              rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
        _ = K θ Set.univ := by rw [hdensity θ]
        _ = 1 := isProbabilityMeasure_iff.mp (hK θ)
    have hjoint : Integrable (fun p : ℝ × X => likelihood p.1 p.2) (π.prod Q) := by
      refine ⟨hmeas.aestronglyMeasurable, ?_⟩
      apply (hasFiniteIntegral_iff_ofReal
        (ae_of_all _ fun p : ℝ × X => hnonneg p.1 p.2)).2
      rw [lintegral_prod _ hmeas.ennreal_ofReal.aemeasurable]
      simp_rw [hfiber]
      simp
    have hsections : ∀ᵐ x ∂Q, Integrable (fun θ => likelihood θ x) π :=
      hjoint.prod_left_ae
    have haverage : ∀ᵐ x ∂Q,
        ENNReal.ofReal (mixtureLikelihood π likelihood x) =
          ∫⁻ θ, ENNReal.ofReal (likelihood θ x) ∂π := by
      filter_upwards [hsections] with x hx
      exact ofReal_integral_eq_lintegral_ofReal hx
        (ae_of_all _ fun θ => hnonneg θ x)
    refine Measure.ext fun A hA => ?_
    rw [priorPredictive_apply π K hA, withDensity_apply _ hA]
    simp_rw [hdensity, withDensity_apply _ hA]
    calc
      ∫⁻ θ, ∫⁻ x in A, ENNReal.ofReal (likelihood θ x) ∂Q ∂π =
          ∫⁻ x in A, ∫⁻ θ, ENNReal.ofReal (likelihood θ x) ∂π ∂Q := by
            apply lintegral_lintegral_swap
            exact hmeas.ennreal_ofReal.aemeasurable
      _ = ∫⁻ x in A, ENNReal.ofReal (mixtureLikelihood π likelihood x) ∂Q := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_of_ae haverage] with x hx
        exact hx.symm
  have hmix_meas (π : Measure ℝ) [IsProbabilityMeasure π] :
      Measurable (mixtureLikelihood π likelihood) := by
    exact hmeas.stronglyMeasurable.integral_prod_left'.measurable
  have hmix_nonneg (π : Measure ℝ) (x : X) : 0 ≤ mixtureLikelihood π likelihood x :=
    integral_nonneg fun θ => hnonneg θ x
  have hset : MeasurableSet {θ : ℝ | |θ| ≤ a} :=
    measurableSet_le continuous_abs.measurable measurable_const
  have hsupp_ae (π : Measure ℝ) [IsProbabilityMeasure π]
      (hsupp : π {θ | |θ| ≤ a} = 1) : ∀ᵐ θ ∂π, |θ| ≤ a := by
    change {θ : ℝ | |θ| ≤ a} ∈ ae π
    rw [mem_ae_iff, measure_compl hset (measure_ne_top π _), measure_univ, hsupp,
      tsub_self]
  have hprod_int (θ θ' : ℝ) :
      Integrable (fun x => likelihood θ x * likelihood θ' x) Q := by
    by_contra h
    have heq := hinner θ θ'
    rw [integral_undef h] at heq
    exact Real.exp_ne_zero _ heq.symm
  have hmix_sq_int (π : Measure ℝ) [IsProbabilityMeasure π]
      (hsupp : π {θ | |θ| ≤ a} = 1) :
      Integrable (fun x => mixtureLikelihood π likelihood x * mixtureLikelihood π likelihood x) Q := by
    let g : (ℝ × ℝ) × X → ℝ := fun z =>
      likelihood z.1.1 z.2 * likelihood z.1.2 z.2
    have hgmeas : Measurable g := by
      unfold g
      fun_prop
    have hpairs : ∀ᵐ z ∂π.prod π, |z.1| ≤ a ∧ |z.2| ≤ a := by
      apply (Measure.ae_prod_iff_ae_ae
        ((measurableSet_le (continuous_abs.measurable.comp measurable_fst) measurable_const).inter
          (measurableSet_le (continuous_abs.measurable.comp measurable_snd) measurable_const))).2
      filter_upwards [hsupp_ae π hsupp] with θ hθ
      filter_upwards [hsupp_ae π hsupp] with θ' hθ'
      exact ⟨hθ, hθ'⟩
    have hexp_int :
        Integrable (fun z : ℝ × ℝ => Real.exp (lambda * z.1 * z.2)) (π.prod π) := by
      apply (integrable_const (μ := π.prod π) (Real.exp (lambda * a ^ 2))).mono'
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
    have hg_int : Integrable g ((π.prod π).prod Q) := by
      rw [integrable_prod_iff hgmeas.aestronglyMeasurable]
      constructor
      · filter_upwards with z
        simpa [g] using hprod_int z.1 z.2
      · convert hexp_int using 1
        funext z
        calc
          ∫ x, ‖g (z, x)‖ ∂Q =
              ∫ x, likelihood z.1 x * likelihood z.2 x ∂Q := by
                apply integral_congr_ae
                filter_upwards with x
                simp only [g, Real.norm_eq_abs,
                  abs_of_nonneg (mul_nonneg (hnonneg _ _) (hnonneg _ _))]
          _ = Real.exp (lambda * z.1 * z.2) := hinner z.1 z.2
    apply hg_int.integral_prod_right.congr
    filter_upwards with x
    change (∫ z : ℝ × ℝ, likelihood z.1 x * likelihood z.2 x ∂π.prod π) = _
    exact integral_prod_mul (fun θ => likelihood θ x) (fun θ => likelihood θ x)
  have hsq0 := hmix_sq_int π0 hsupp0
  have hsq1 := hmix_sq_int π1 hsupp1
  have hmajorant : Integrable (fun x => 2 *
      (mixtureLikelihood π0 likelihood x * mixtureLikelihood π0 likelihood x +
        mixtureLikelihood π1 likelihood x * mixtureLikelihood π1 likelihood x)) Q :=
    (hsq0.add hsq1).const_mul 2
  have hdiff_sq : Integrable (fun x =>
      (mixtureLikelihood π0 likelihood x - mixtureLikelihood π1 likelihood x) ^ 2) Q := by
    apply hmajorant.mono' ((hmix_meas π0).sub (hmix_meas π1) |>.pow_const 2).aestronglyMeasurable
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
    (hmix_meas π0) (hmix_meas π1) (hmix_nonneg π0) (hmix_nonneg π1)
    (hpred π0) (hpred π1) hdiff_sq
  have htail := integral_sq_mixtureLikelihood_sub_le_tail π0 π1 Q likelihood
    lambda a degree hlambda ha hmeas hnonneg hinner hsupp0 hsupp1 hmom
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

end Causalean.Stat.Minimax.MomentMatchedMixture

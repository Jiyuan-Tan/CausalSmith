module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Basic
public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# KL identities for restricted recurrence intensities

This module evaluates the finite-measure KL divergence of positive densities
and specializes the result to recurrence intensities stopped at a fixed exit.
-/

public section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The scalar Poisson intensity cost is continuous, including at zero. -/
lemma continuous_poissonIntensityCost (b : ℝ) (hb : 0 < b) :
    Continuous (fun x : ℝ => x * Real.log (x / b) - x + b) := by
  have hid : (fun x : ℝ => x * Real.log (x / b) - x + b) =
      fun x => x * Real.log x - x * Real.log b - x + b := by
    funext x
    by_cases hx : x = 0
    · simp [hx]
    · rw [Real.log_div hx hb.ne']
      ring
  rw [hid]
  fun_prop

/-- Away from zero, the derivative of the scalar Poisson cost is the log
intensity ratio. -/
lemma hasDerivAt_poissonIntensityCost (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (fun x : ℝ => x * Real.log (x / b) - x + b)
      (Real.log (a / b)) a := by
  have hid : (fun x : ℝ => x * Real.log (x / b) - x + b) =
      fun x => x * Real.log x - x * Real.log b - x + b := by
    funext x
    by_cases hx : x = 0
    · simp [hx]
    · rw [Real.log_div hx hb.ne']
      ring
  rw [hid]
  have h := (((Real.hasDerivAt_mul_log ha.ne').sub
    ((hasDerivAt_id a).const_mul (Real.log b))).sub
      (hasDerivAt_id a)).add_const b
  have heq : Real.log a + 1 - Real.log b * 1 - 1 = Real.log (a / b) := by
    rw [Real.log_div ha.ne' hb.ne']
    ring
  rw [heq] at h
  simpa only [Pi.sub_apply, Pi.add_apply, id_eq, mul_comm] using h

/-- Below the reference intensity, the scalar Poisson cost is strictly
decreasing. -/
lemma poissonIntensityCost_strictAntiOn (b : ℝ) (hb : 0 < b) :
    StrictAntiOn (fun x : ℝ => x * Real.log (x / b) - x + b)
      (Set.Icc 0 b) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 b)
    (continuous_poissonIntensityCost b hb).continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_poissonIntensityCost x b hx.1 hb).deriv]
  exact Real.log_neg (div_pos hx.1 hb) ((div_lt_one hb).2 hx.2)

/-- Above the reference intensity, the scalar Poisson cost is strictly
increasing. -/
lemma poissonIntensityCost_strictMonoOn (b : ℝ) (hb : 0 < b) :
    StrictMonoOn (fun x : ℝ => x * Real.log (x / b) - x + b)
      (Set.Ici b) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici b)
    (continuous_poissonIntensityCost b hb).continuousOn
  intro x hx
  rw [interior_Ici] at hx
  rw [(hasDerivAt_poissonIntensityCost x b (lt_trans hb hx) hb).deriv]
  exact Real.log_pos ((one_lt_div hb).2 hx)

/-- The lower branch of the scalar Poisson cost has a measurable inverse on
its image. -/
lemma poissonIntensityCost_lower_measurableEmbedding (b : ℝ) (hb : 0 < b) :
    MeasurableEmbedding (fun x : Set.Icc (0 : ℝ) b =>
      (x : ℝ) * Real.log ((x : ℝ) / b) - (x : ℝ) + b) :=
  ContinuousOn.measurableEmbedding measurableSet_Icc
    (continuous_poissonIntensityCost b hb).continuousOn
    (poissonIntensityCost_strictAntiOn b hb).injOn

/-- The upper branch of the scalar Poisson cost has a measurable inverse on
its image. -/
lemma poissonIntensityCost_upper_measurableEmbedding (b : ℝ) (hb : 0 < b) :
    MeasurableEmbedding (fun x : Set.Ici b =>
      (x : ℝ) * Real.log ((x : ℝ) / b) - (x : ℝ) + b) :=
  ContinuousOn.measurableEmbedding measurableSet_Ici
    (continuous_poissonIntensityCost b hb).continuousOn
    (poissonIntensityCost_strictMonoOn b hb).injOn

private lemma poissonIntensityCost_lower_invFun_apply
    (b : ℝ) (hb : 0 < b) [Nonempty (Set.Icc (0 : ℝ) b)]
    (y : Set.Icc (0 : ℝ) b) :
    (poissonIntensityCost_lower_measurableEmbedding b hb).invFun
      ((y : ℝ) * Real.log ((y : ℝ) / b) - (y : ℝ) + b) = y := by
  unfold MeasurableEmbedding.invFun
  simp

private lemma poissonIntensityCost_upper_invFun_apply
    (b : ℝ) (hb : 0 < b) [Nonempty (Set.Ici b)]
    (y : Set.Ici b) :
    (poissonIntensityCost_upper_measurableEmbedding b hb).invFun
      ((y : ℝ) * Real.log ((y : ℝ) / b) - (y : ℝ) + b) = y := by
  unfold MeasurableEmbedding.invFun
  simp

/-- The explicit treatment perturbation leaves the control-arm recurrence
intensity equal to the constant baseline intensity. -/
lemma treatmentPerturbIntensity_baseline_false
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0)
    (lam1 : ℝ → ℝ) :
    treatmentPerturbIntensity
        (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 false =
      baselineRecurrenceIntensity lambda0 := by
  rfl

/-- The KL divergence of two finite measures with positive finite target
density is the base-measure integral of the density-ratio KL function. -/
lemma klDiv_withDensity_eq_lintegral_klFun_ratio
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [SigmaFinite mu]
    (f g : X → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    [IsFiniteMeasure (mu.withDensity f)] [IsFiniteMeasure (mu.withDensity g)]
    (hg_zero : ∀ᵐ x ∂mu, g x ≠ 0)
    (hg_top : ∀ᵐ x ∂mu, g x ≠ ∞) :
    InformationTheory.klDiv (mu.withDensity f) (mu.withDensity g) =
      ∫⁻ x, g x * ENNReal.ofReal
        (InformationTheory.klFun ((f x / g x).toReal)) ∂mu := by
  have hac : mu.withDensity f ≪ mu.withDensity g :=
    (withDensity_absolutelyContinuous mu f).trans
      (withDensity_absolutelyContinuous' hg.aemeasurable hg_zero)
  have hrn : (mu.withDensity f).rnDeriv (mu.withDensity g) =ᵐ[mu]
      fun x => f x / g x := by
    have hright := Measure.rnDeriv_withDensity_right (mu.withDensity f) mu
      hg.aemeasurable hg_zero hg_top
    have hleft := Measure.rnDeriv_withDensity mu hf
    filter_upwards [hright, hleft] with x hxright hxleft
    rw [hxright, hxleft]
    simp [div_eq_mul_inv, mul_comm]
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac hac,
    lintegral_withDensity_eq_lintegral_mul mu hg]
  apply lintegral_congr_ae
  filter_upwards [hrn] with x hx
  simp only [Pi.mul_apply, hx]
  all_goals fun_prop

/-- Multiplying the KL function of a positive density ratio by the positive
reference density gives the Poisson intensity integrand. -/
lemma density_klFun_point (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    ENNReal.ofReal b * ENNReal.ofReal
        (InformationTheory.klFun
          ((ENNReal.ofReal a / ENNReal.ofReal b).toReal)) =
      ENNReal.ofReal (a * Real.log (a / b) - a + b) := by
  have hratio : ((ENNReal.ofReal a / ENNReal.ofReal b).toReal) = a / b := by
    rw [ENNReal.toReal_div]
    simp [ha, hb.le]
  rw [hratio, ← ENNReal.ofReal_mul hb.le]
  congr 1
  rw [InformationTheory.klFun_apply]
  field_simp <;> ring

/-- The local Poisson intensity KL cost is nonnegative at positive source and
reference intensities. -/
lemma poissonIntensityCost_nonneg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    0 ≤ a * Real.log (a / b) - a + b := by
  have hident : b * InformationTheory.klFun (a / b) =
      a * Real.log (a / b) - a + b := by
    rw [InformationTheory.klFun_apply]
    field_simp
    ring
  rw [← hident]
  exact mul_nonneg hb.le
      (InformationTheory.klFun_nonneg (div_nonneg ha hb.le))

/-- For a positive real density against a positive constant density, the
finite-measure KL is the integral of `f log (f / b) - f + b`. -/
lemma klDiv_withDensity_ofReal_pos
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [SigmaFinite mu]
    (f : X → ℝ) (b : ℝ) (hf : Measurable f)
    (hf_pos : ∀ᵐ x ∂mu, 0 ≤ f x) (hb : 0 < b)
    [IsFiniteMeasure (mu.withDensity fun x => ENNReal.ofReal (f x))]
    [IsFiniteMeasure (mu.withDensity fun _ => ENNReal.ofReal b)] :
    InformationTheory.klDiv
        (mu.withDensity fun x => ENNReal.ofReal (f x))
        (mu.withDensity fun _ => ENNReal.ofReal b) =
      ∫⁻ x, ENNReal.ofReal
        (f x * Real.log (f x / b) - f x + b) ∂mu := by
  rw [klDiv_withDensity_eq_lintegral_klFun_ratio mu
    (fun x => ENNReal.ofReal (f x)) (fun _ => ENNReal.ofReal b)
    hf.ennreal_ofReal measurable_const
    (ae_of_all mu (fun _ => ne_of_gt (ENNReal.ofReal_pos.mpr hb)))
    (ae_of_all mu (fun _ => ENNReal.ofReal_ne_top))]
  apply lintegral_congr_ae
  filter_upwards [hf_pos] with x hx
  exact density_klFun_point (f x) b hx hb

/-- Restricting positive recurrence intensities to a fixed exit time gives
the cumulative Poisson intensity KL on the observed time window. -/
lemma klDiv_restrict_withDensity_ofReal_pos
    (lam1 : ℝ → ℝ) (lambda0 x : ℝ)
    (hlam1_meas : Measurable lam1)
    (hlam1_pos : ∀ t ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ lam1 t)
    (hlambda0 : 0 < lambda0)
    (hfinite : IsFiniteMeasure
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).withDensity
        (fun t => ENNReal.ofReal (lam1 t)))) :
    InformationTheory.klDiv
        (((volume.restrict (Set.Ioc (0 : ℝ) 1)).withDensity
          (fun t => ENNReal.ofReal (lam1 t))).restrict (Set.Iic x))
        (((volume.restrict (Set.Ioc (0 : ℝ) 1)).withDensity
          (fun _ => ENNReal.ofReal lambda0)).restrict (Set.Iic x)) =
      ∫⁻ t in Set.Iic x, ENNReal.ofReal
        (lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0)
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  let rho := (volume.restrict (Set.Ioc (0 : ℝ) 1)).restrict (Set.Iic x)
  have hsource :
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).withDensity
        (fun t => ENNReal.ofReal (lam1 t))).restrict (Set.Iic x) =
        rho.withDensity (fun t => ENNReal.ofReal (lam1 t)) := by
    rw [restrict_withDensity measurableSet_Iic]
  have htarget :
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).withDensity
        (fun _ => ENNReal.ofReal lambda0)).restrict (Set.Iic x) =
        rho.withDensity (fun _ => ENNReal.ofReal lambda0) := by
    rw [restrict_withDensity measurableSet_Iic]
  letI : IsFiniteMeasure
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).withDensity
        (fun t => ENNReal.ofReal (lam1 t))) := hfinite
  letI : IsFiniteMeasure
      (((volume.restrict (Set.Ioc (0 : ℝ) 1)).withDensity
        (fun t => ENNReal.ofReal (lam1 t))).restrict (Set.Iic x)) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr (measure_ne_top _ _)
  letI : IsFiniteMeasure
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).withDensity
        (fun _ => ENNReal.ofReal lambda0)) :=
    baselineRecurrenceIntensity_isFinite lambda0
  letI : IsFiniteMeasure
      (((volume.restrict (Set.Ioc (0 : ℝ) 1)).withDensity
        (fun _ => ENNReal.ofReal lambda0)).restrict (Set.Iic x)) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr (measure_ne_top _ _)
  letI : IsFiniteMeasure
      (rho.withDensity (fun t => ENNReal.ofReal (lam1 t))) := hsource ▸ inferInstance
  letI : IsFiniteMeasure
      (rho.withDensity (fun _ => ENNReal.ofReal lambda0)) := htarget ▸ inferInstance
  have hmem : ∀ᵐ t ∂rho, t ∈ Set.Ioc (0 : ℝ) 1 :=
    (MeasureTheory.ae_mono Measure.restrict_le_self)
      (ae_restrict_mem measurableSet_Ioc)
  have hpos : ∀ᵐ t ∂rho, 0 ≤ lam1 t := by
    filter_upwards [hmem] with t ht
    exact hlam1_pos t ht
  have hkl := klDiv_withDensity_ofReal_pos rho lam1 lambda0
    hlam1_meas hpos hlambda0
  rw [hsource, htarget, hkl]

/-- For the explicit baseline perturbation, the treatment-arm intensity KL
up to an exit time is the cumulative local Poisson KL integrand. -/
lemma SubjectLaw.baselinePerturb_restrictedIntensity_klDiv
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0)
    (lam1 : ℝ → ℝ) (x : ℝ)
    (hlam1_meas : Measurable lam1)
    (hlam1_pos : ∀ t ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ lam1 t)
    (hlambda0 : 0 < lambda0)
    (hfinite : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity
        (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 a)) :
    InformationTheory.klDiv
        ((treatmentPerturbIntensity
          (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 true).restrict
            (Set.Iic x))
        ((baselineRecurrenceIntensity lambda0).restrict (Set.Iic x)) =
      ∫⁻ t in Set.Iic x, ENNReal.ofReal
        (lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0)
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  simpa only [treatmentPerturbIntensity, baselineRecurrenceIntensity,
    if_true] using klDiv_restrict_withDensity_ofReal_pos
      lam1 lambda0 x hlam1_meas hlam1_pos hlambda0 (hfinite true)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

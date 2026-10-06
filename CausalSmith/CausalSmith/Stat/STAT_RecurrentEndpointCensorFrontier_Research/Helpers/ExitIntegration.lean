module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.StoppedKL
public import Mathlib.Probability.Independence.Integration

/-!
# Assignment and exit-time integration

This module reduces a treated-arm cumulative recurrence cost to its assignment
weight and then applies the exit-time layer-cake identity with the model's
survival and censor-retention tails.
-/

public section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal Interval

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Censoring retention is antitone in the requested follow-up time. -/
lemma retention_antitone (P : SubjectLaw) (a : Arm) :
    Antitone (retention P a) := by
  intro s t hst
  unfold retention
  apply measureReal_mono
  · intro z hz
    exact le_trans (ENNReal.ofReal_le_ofReal hst) hz
  · exact ne_top_of_le_ne_top (by rw [P.prob]; exact ENNReal.one_ne_top)
      (measure_mono (Set.subset_univ _))

/-- Censoring retention is measurable as an antitone tail function. -/
lemma measurable_retention (P : SubjectLaw) (a : Arm) :
    Measurable (retention P a) :=
  (retention_antitone P a).measurable

/-- The constant-hazard baseline survival curve is measurable. -/
lemma SubjectLaw.measurable_baseline_survival
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0)
    (a : Arm) :
    Measurable (survival (SubjectLaw.baseline reference lambda0 d0 hd0) a) := by
  unfold survival SubjectLaw.baseline
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  fun_prop

/-- Positive constant baseline hazard makes survival antitone. -/
lemma SubjectLaw.baseline_survival_antitone
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0)
    (a : Arm) :
    Antitone (survival (SubjectLaw.baseline reference lambda0 d0 hd0) a) := by
  intro s t hst
  unfold survival SubjectLaw.baseline
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- The survival-retention weight appearing in the baseline KL integral is
measurable, including at the vanishing endpoint. -/
lemma SubjectLaw.measurable_baseline_survival_mul_retention
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0)
    (a : Arm) :
    Measurable (fun t =>
      survival (SubjectLaw.baseline reference lambda0 d0 hd0) a t *
        retention (SubjectLaw.baseline reference lambda0 d0 hd0) a t) :=
  (SubjectLaw.measurable_baseline_survival reference lambda0 d0 hd0 a).mul
    (measurable_retention _ _)

/-- The complete baseline observation weight is antitone. -/
lemma SubjectLaw.baseline_survival_mul_retention_antitone
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0)
    (a : Arm) :
    Antitone (fun t =>
      survival (SubjectLaw.baseline reference lambda0 d0 hd0) a t *
        retention (SubjectLaw.baseline reference lambda0 d0 hd0) a t) := by
  intro s t hst
  exact mul_le_mul
    (SubjectLaw.baseline_survival_antitone reference lambda0 d0 hd0 a hst)
    (retention_antitone _ _ hst) measureReal_nonneg (Real.exp_nonneg _)

/-- Model-class retention is strictly positive before the terminal horizon.
The proof joins the interior lower bound to the endpoint expansion. -/
lemma retention_pos_of_modelClass
    (c : ClassConstants) (P : SubjectLaw) (hModel : ModelClass c P)
    (a : Arm) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < retention P a t := by
  by_cases hinterior : t ≤ 1 - c.x0
  · exact lt_of_lt_of_le c.Gint_pos
      (hModel.interiorRetention a t ⟨ht0, hinterior⟩)
  · let x := 1 - t
    have hx : 0 < x := by dsimp [x]; linarith
    have hx0 : x ≤ c.x0 := by dsimp [x]; linarith
    have hg : 0 < P.g a :=
      lt_of_lt_of_le c.gMin_pos (hModel.endpointCoefficientBounds a).1
    have hden : 0 < P.g a * x ^ c.kappa :=
      mul_pos hg (Real.rpow_pos_of_pos hx _)
    have hpow : x ^ c.rho ≤ c.x0 ^ c.rho :=
      Real.rpow_le_rpow hx.le hx0 c.rho_pos.le
    have hsmall : c.LG * x ^ c.rho ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_left hpow c.LG_pos.le).trans
        hModel.tailEnvelopeSmall
    have hbound := hModel.endpointRetention a x hx hx0
    have hquot : 1 / 2 ≤
        retention P a (1 - x) / (P.g a * x ^ c.kappa) := by
      have hlower := (abs_le.mp hbound).1
      linarith
    have hpos : 0 < retention P a (1 - x) := by
      have hmul := (le_div_iff₀ hden).mp hquot
      nlinarith
    simpa [x] using hpos

/-- The baseline survival-retention weight is strictly positive at every
pre-horizon time in the model class. -/
lemma SubjectLaw.baseline_survival_mul_retention_pos
    (c : ClassConstants) (reference : SubjectLaw) (lambda0 d0 : ℝ)
    (hd0 : 0 < d0)
    (hModel : ModelClass c (SubjectLaw.baseline reference lambda0 d0 hd0))
    (a : Arm) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < survival (SubjectLaw.baseline reference lambda0 d0 hd0) a t *
      retention (SubjectLaw.baseline reference lambda0 d0 hd0) a t :=
  mul_pos (Real.exp_pos _)
    (retention_pos_of_modelClass c _ hModel a t ht0 ht1)

/-- A cumulative Lebesgue integral over the moving interval `(-∞, x]` is a
measurable function of its endpoint. -/
lemma measurable_cumulative_Iic (k : ℝ → ℝ≥0∞) (hk : Measurable k) :
    Measurable (fun x : ℝ => ∫⁻ t in Set.Iic x, k t ∂volume) := by
  let f : ℝ → ℝ → ℝ≥0∞ := fun x t => if t ≤ x then k t else 0
  have hf : Measurable (Function.uncurry f) := by
    apply Measurable.ite
    · exact measurableSet_le measurable_snd measurable_fst
    · exact hk.comp measurable_snd
    · exact measurable_const
  have hlin := hf.lintegral_prod_right (ν := volume)
  convert hlin using 1
  funext x
  rw [← lintegral_indicator measurableSet_Iic]
  apply lintegral_congr
  intro t
  simp [f, Set.indicator, Set.mem_Iic]

/-- Random assignment separates a treated-arm cumulative exit cost into the
treatment probability and the unconditional treatment-potential exit cost. -/
lemma lintegral_exitRecordLaw_treatment_factor
    (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P)
    (k : ℝ → ℝ≥0∞) (hk : Measurable k) :
    (∫⁻ e, (if e.1 then ∫⁻ t in Set.Iic e.2.1, k t ∂volume else 0)
        ∂exitRecordLaw P) =
      ENNReal.ofReal (P.p true) *
        ∫⁻ z, ∫⁻ t in Set.Iic
          (min (z.death true) (censorHorizon z true)), k t ∂volume ∂P.latent := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let cumulative : ℝ → ℝ≥0∞ := fun x => ∫⁻ t in Set.Iic x, k t ∂volume
  have hcum : Measurable cumulative := measurable_cumulative_Iic k hk
  let assignWeight : Arm → ℝ≥0∞ := fun a => if a then 1 else 0
  have hassignWeight : Measurable assignWeight := measurable_of_finite _
  let exitTrue : ((Arm → RecurConfig) × (Arm → ℝ) × (Arm → ENNReal)) → ℝ :=
    fun r => min (r.2.1 true) (censorHorizonValue (r.2.2 true))
  have hexitTrue : Measurable exitTrue := by
    unfold exitTrue
    fun_prop
  let latentRest : LatentSubject →
      ((Arm → RecurConfig) × (Arm → ℝ) × (Arm → ENNReal)) :=
    fun z => (z.recur, z.death, z.censor)
  have hrest : Measurable latentRest := by
    unfold latentRest
    fun_prop
  have hfactor := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    (hassignWeight.comp measurable_latentSubject_treatment)
    ((hcum.comp hexitTrue).comp hrest)
    (hRandom.comp hassignWeight (hcum.comp hexitTrue))
  rw [exitRecordLaw, lintegral_map]
  rotate_left
  · exact Measurable.ite
      (measurableSet_eq_fun measurable_fst measurable_const)
      (hcum.comp (measurable_fst.comp measurable_snd)) measurable_const
  · exact measurable_latentExitRecord
  have hweight : (∫⁻ z, assignWeight z.treatment ∂P.latent) =
      ENNReal.ofReal (P.p true) := by
    have hevent : (fun z : LatentSubject => assignWeight z.treatment) =
        {z | z.treatment = true}.indicator 1 := by
      funext z
      simp [assignWeight, Set.indicator]
    rw [hevent, lintegral_indicator_one]
    · rw [← hAssignment true]
      exact (ENNReal.ofReal_toReal (measure_ne_top P.latent _)).symm
    · exact measurableSet_eq_fun measurable_latentSubject_treatment measurable_const
  calc
    _ = ∫⁻ z, assignWeight z.treatment *
        cumulative (exitTrue (latentRest z)) ∂P.latent := by
      apply lintegral_congr
      intro z
      have hexitrec : latentExitRecord z =
          (z.treatment,
            min (z.death z.treatment) (censorHorizon z z.treatment),
            decide (z.death z.treatment ≤ censorHorizon z z.treatment)) := rfl
      rw [hexitrec]
      cases h : z.treatment <;>
        simp [cumulative, assignWeight, exitTrue, latentRest,
          censorHorizon_eq_value, h]
    _ = (∫⁻ z, assignWeight z.treatment ∂P.latent) *
        ∫⁻ z, cumulative (exitTrue (latentRest z)) ∂P.latent := hfactor
    _ = _ := by rw [hweight]; rfl

/-- Layer cake and the death/censor model atoms turn a treatment-potential
cumulative cost into a survival-times-retention weighted local cost. -/
lemma lintegral_exit_cumulative_eq_survival_retention
    (P : SubjectLaw) (hdeath : DeathHazard P)
    (hcensor : IndependentCensoring P)
    (k : ℝ → ℝ≥0∞) (hk : Measurable k)
    (hsupp : ∀ t, t ∉ Set.Ioc (0 : ℝ) 1 → k t = 0) :
    (∫⁻ z, ∫⁻ t in Set.Iic
      (min (z.death true) (censorHorizon z true)), k t ∂volume ∂P.latent) =
      ∫⁻ t, ENNReal.ofReal (survival P true t * retention P true t) * k t
        ∂volume := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let exitTrue : LatentSubject → ℝ := fun z =>
    min (z.death true) (censorHorizon z true)
  have hexit : Measurable exitTrue := by
    unfold exitTrue
    fun_prop
  let mu := P.latent.map exitTrue
  let cumulative : ℝ → ℝ≥0∞ := fun x => ∫⁻ t in Set.Iic x, k t ∂volume
  have hcum : Measurable cumulative := measurable_cumulative_Iic k hk
  calc
    _ = ∫⁻ x, cumulative x ∂mu := by
      rw [lintegral_map hcum hexit]
    _ = ∫⁻ t, mu (Set.Ici t) * k t ∂volume :=
      lintegral_setLIntegral_Iic_eq_tail mu k hk
    _ = _ := by
      apply lintegral_congr
      intro t
      by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
      · have htail : mu (Set.Ici t) =
            ENNReal.ofReal (survival P true t * retention P true t) := by
          rw [Measure.map_apply hexit measurableSet_Ici]
          have hreal := exitTail_eq_survival_mul_retention P hdeath hcensor true t
            ⟨le_of_lt ht.1, ht.2⟩
          rw [← hreal]
          exact (ENNReal.ofReal_toReal (measure_ne_top P.latent _)).symm
        rw [htail]
      · rw [hsupp t ht, mul_zero, mul_zero]

/-- Combining assignment separation with the exit-time calculation gives the
treated-arm survival-retention integral under the observed exit law. -/
lemma lintegral_exitRecordLaw_treatment_eq_survival_retention
    (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hdeath : DeathHazard P)
    (hcensor : IndependentCensoring P)
    (k : ℝ → ℝ≥0∞) (hk : Measurable k)
    (hsupp : ∀ t, t ∉ Set.Ioc (0 : ℝ) 1 → k t = 0) :
    (∫⁻ e, (if e.1 then ∫⁻ t in Set.Iic e.2.1, k t ∂volume else 0)
        ∂exitRecordLaw P) =
      ENNReal.ofReal (P.p true) *
        ∫⁻ t, ENNReal.ofReal (survival P true t * retention P true t) * k t
          ∂volume := by
  rw [lintegral_exitRecordLaw_treatment_factor P hRandom hAssignment k hk,
    lintegral_exit_cumulative_eq_survival_retention P hdeath hcensor k hk hsupp]

/-- A finite nonnegative local cost converts the extended-real assignment
weighted set integral exactly to the paper's real interval integral. -/
lemma toReal_ofReal_mul_setLIntegral_ofReal
    (p : ℝ) (hp : 0 ≤ p) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume 0 1)
    (hnonneg : ∀ t ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ f t) :
    (ENNReal.ofReal p *
      ∫⁻ t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (f t) ∂volume).toReal =
      p * ∫ t in (0 : ℝ)..1, f t := by
  have hfint : Integrable f (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    rw [← IntegrableOn]
    rw [← uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact intervalIntegrable_iff.mp hf
  have hnonneg_ae : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] f :=
    ae_restrict_of_forall_mem measurableSet_Ioc hnonneg
  rw [← ofReal_integral_eq_lintegral_ofReal hfint hnonneg_ae,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hp,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hnonneg_ae),
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

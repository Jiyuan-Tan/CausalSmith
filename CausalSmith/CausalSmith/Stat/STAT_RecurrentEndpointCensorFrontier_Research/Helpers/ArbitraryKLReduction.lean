module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ArbitraryExitStoppedLaw

@[expose] public section

open MeasureTheory Set ProbabilityTheory

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- A measurable, everywhere nonnegative representative of an a.e. measurable
nonnegative intensity on the study interval. -/
@[no_expose]
noncomputable def nonnegativeMeasurableVersion (f : ℝ → ℝ)
    (hf : AEMeasurable f (volume.restrict (Set.Ioc (0 : ℝ) 1))) : ℝ → ℝ :=
  fun t => max (hf.mk f t) 0

lemma measurable_nonnegativeMeasurableVersion (f : ℝ → ℝ)
    (hf : AEMeasurable f (volume.restrict (Set.Ioc (0 : ℝ) 1))) :
    Measurable (nonnegativeMeasurableVersion f hf) := by
  exact hf.measurable_mk.max measurable_const

lemma nonnegativeMeasurableVersion_nonneg (f : ℝ → ℝ)
    (hf : AEMeasurable f (volume.restrict (Set.Ioc (0 : ℝ) 1))) (t : ℝ) :
    0 ≤ nonnegativeMeasurableVersion f hf t := le_max_right _ _

lemma nonnegativeMeasurableVersion_ae_eq (f : ℝ → ℝ)
    (hf : AEMeasurable f (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hnonneg : ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1), 0 ≤ f t) :
    nonnegativeMeasurableVersion f hf =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] f := by
  filter_upwards [hf.ae_eq_mk, hnonneg] with t ht hpos
  simp [nonnegativeMeasurableVersion, ← ht, hpos]

/-- Replacing an intensity by an a.e.-equal version does not change its
finite study-window intensity measure. -/
lemma recurrenceIntensity_eq_of_ae_eq (P Q : SubjectLaw) (a : Arm)
    (h : P.lam a =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] Q.lam a) :
    recurrenceIntensity P a = recurrenceIntensity Q a := by
  unfold recurrenceIntensity
  apply withDensity_congr_ae
  filter_upwards [h] with t ht
  rw [ht]

/-- Poisson finiteness of an arbitrary admissible perturbation supplies the
finiteness witnesses needed by the explicit product constructor after passing
to an a.e.-equal treated intensity. -/
lemma explicitPerturb_finite_of_poisson
    (P base : SubjectLaw) (f g : ℝ → ℝ)
    (hPoisson : PoissonRecurrence P)
    (hFalse : P.lam false = base.lam false)
    (hTrue : P.lam true = f)
    (hfg : f =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] g) :
    ∀ a : Arm, IsFiniteMeasure (treatmentPerturbIntensity base g a) := by
  intro a
  rcases (hPoisson a).2.2 with ⟨hfin, _⟩
  have hi : recurrenceIntensity P a = treatmentPerturbIntensity base g a := by
    cases a
    · simp only [recurrenceIntensity, treatmentPerturbIntensity, Bool.false_eq_true,
        ↓reduceIte, hFalse]
    · unfold recurrenceIntensity treatmentPerturbIntensity
      simp only [↓reduceIte]
      apply withDensity_congr_ae
      filter_upwards [hfg] with t ht
      rw [hTrue, ht]
  rw [← hi]
  exact hfin

/-- Weighted finiteness is enough for the common-exit KL chain rule: only
almost-everywhere, rather than pointwise, finiteness of the stopped fibre KL
is required. -/
lemma SubjectLaw.baselinePerturb_observedKL_eq_exitIntegral_of_finite
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0)
    (lam1 : ℝ → ℝ) (hlam1_meas : Measurable lam1)
    (hlam1_pos : ∀ t ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ lam1 t)
    (hlambda0 : 0 < lambda0)
    (hfinite : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity
        (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 a))
    (htotal : (∫⁻ e, (if e.1 then
      ∫⁻ t in Set.Iic e.2.1, ENNReal.ofReal
        (lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0)
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) else 0)
      ∂SubjectLaw.baselineExitRecordLaw reference d0) < ⊤) :
    InformationTheory.klDiv
        (observedLaw (SubjectLaw.perturbTreatment
          (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 hfinite))
        (observedLaw (SubjectLaw.baseline reference lambda0 d0 hd0)) =
      ∫⁻ e, (if e.1 then
        ∫⁻ t in Set.Iic e.2.1, ENNReal.ofReal
          (lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0)
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) else 0)
        ∂SubjectLaw.baselineExitRecordLaw reference d0 := by
  let cost : ℝ → ℝ := fun t =>
    lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0
  let k : ℝ → ENNReal :=
    (Set.Ioc (0 : ℝ) 1).indicator (fun t => ENNReal.ofReal (cost t))
  have hk : Measurable k := by
    exact (by unfold cost; fun_prop : Measurable fun t => ENNReal.ofReal (cost t))
      |>.indicator measurableSet_Ioc
  let F : ExitRecord → ENNReal := fun e =>
    if e.1 then ∫⁻ t in Set.Iic e.2.1, k t ∂volume else 0
  have hF : Measurable F := by
    unfold F
    exact Measurable.ite
      (measurableSet_eq_fun measurable_fst measurable_const)
      ((measurable_cumulative_Iic k hk).comp
        (measurable_fst.comp measurable_snd)) measurable_const
  have hinner (x : ℝ) :
      (∫⁻ t in Set.Iic x, ENNReal.ofReal (cost t)
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) =
        ∫⁻ t in Set.Iic x, k t ∂volume := by
    symm
    unfold k
    rw [lintegral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Iic,
      Measure.restrict_restrict measurableSet_Ioc]
    congr 2
    exact inter_comm _ _
  have htotalF : (∫⁻ e, F e
      ∂SubjectLaw.baselineExitRecordLaw reference d0) < ⊤ := by
    convert htotal using 1
    apply lintegral_congr
    intro e
    by_cases hb : e.1 = true
    · simp only [F, hb, ↓reduceIte]
      exact (hinner e.2.1).symm
    · simp [F, hb]
  have hfiniteAe : ∀ᵐ e ∂SubjectLaw.baselineExitRecordLaw reference d0,
      F e ≠ ⊤ := (ae_lt_top hF htotalF.ne).mono (fun _ h => ne_of_lt h)
  have hac : ∀ᵐ e ∂SubjectLaw.baselineExitRecordLaw reference d0,
      stoppedRecurrenceKernel
          (fun a => treatmentPerturbIntensity
            (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 a)
          hfinite e ≪
        stoppedRecurrenceKernel
          (fun _ : Arm => baselineRecurrenceIntensity lambda0)
          (fun _ => baselineRecurrenceIntensity_isFinite lambda0) e := by
    filter_upwards [hfiniteAe] with e he
    change (if e.1 then ∫⁻ t in Set.Iic e.2.1, k t ∂volume else 0) ≠ ⊤ at he
    apply (InformationTheory.klDiv_ne_top_iff.mp ?_).1
    rw [stoppedRecurrenceKernel_apply, stoppedRecurrenceKernel_apply,
      SubjectLaw.baselinePerturb_fixedExit_stoppedKL reference lambda0 d0 hd0
        lam1 e hlam1_meas hlam1_pos hlambda0 hfinite]
    cases harm : e.1
    · simp [harm]
    · simp only [harm, ↓reduceIte] at he ⊢
      rw [hinner]
      exact he
  rw [SubjectLaw.baselinePerturb_observedKL_eq_fixedExitIntegral
    reference lambda0 d0 hd0 lam1 hfinite hac]
  apply lintegral_congr
  intro e
  simpa only [stoppedRecurrenceKernel_apply] using
    SubjectLaw.baselinePerturb_fixedExit_stoppedKL
      reference lambda0 d0 hd0 lam1 e hlam1_meas hlam1_pos hlambda0 hfinite

/-- Weighted integrability alone gives finiteness and the real-valued observed
KL identity for the explicit perturbation. -/
lemma SubjectLaw.baselinePerturb_observedKL_weighted
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0)
    (hAssignment : AssignmentLaw reference)
    (lam1 : ℝ → ℝ) (hlam1_meas : Measurable lam1)
    (hlam1_pos : ∀ t ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ lam1 t)
    (hlambda0 : 0 < lambda0)
    (hfinite : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity
        (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 a))
    (hweighted : IntervalIntegrable (fun t : ℝ =>
      survival (SubjectLaw.baseline reference lambda0 d0 hd0) true t *
        retention (SubjectLaw.baseline reference lambda0 d0 hd0) true t *
        (lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0))
      volume 0 1) :
    InformationTheory.klDiv
        (observedLaw (SubjectLaw.perturbTreatment
          (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 hfinite))
        (observedLaw (SubjectLaw.baseline reference lambda0 d0 hd0)) ≠ ⊤ ∧
      (InformationTheory.klDiv
        (observedLaw (SubjectLaw.perturbTreatment
          (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 hfinite))
        (observedLaw (SubjectLaw.baseline reference lambda0 d0 hd0))).toReal =
      (SubjectLaw.baseline reference lambda0 d0 hd0).p true *
        ∫ t in (0 : ℝ)..1,
          survival (SubjectLaw.baseline reference lambda0 d0 hd0) true t *
            retention (SubjectLaw.baseline reference lambda0 d0 hd0) true t *
            (lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0) := by
  let Pbase := SubjectLaw.baseline reference lambda0 d0 hd0
  let cost : ℝ → ℝ := fun t =>
    lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0
  let weighted : ℝ → ℝ := fun t =>
    survival Pbase true t * retention Pbase true t * cost t
  have hp : 0 ≤ Pbase.p true := by
    rw [← SubjectLaw.baseline_assignmentLaw reference lambda0 d0 hd0
      hAssignment true]
    exact measureReal_nonneg
  have hw0 (t : ℝ) : 0 ≤ survival Pbase true t * retention Pbase true t :=
    mul_nonneg (Real.exp_nonneg _) measureReal_nonneg
  have hweighted0 : ∀ t ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ weighted t := by
    intro t ht
    exact mul_nonneg (hw0 t) (poissonIntensityCost_nonneg (lam1 t) lambda0
      (hlam1_pos t ht) hlambda0)
  have hrewrite :
      (∫⁻ t, ENNReal.ofReal (survival Pbase true t * retention Pbase true t) *
        (Set.Ioc (0 : ℝ) 1).indicator
          (fun s => ENNReal.ofReal (cost s)) t ∂volume) =
        ∫⁻ t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (weighted t) ∂volume := by
    rw [← lintegral_indicator measurableSet_Ioc]
    apply lintegral_congr
    intro t
    simp only [Set.indicator_apply]
    split_ifs with ht
    · rw [← ENNReal.ofReal_mul (hw0 t)]
    · simp
  have hwint : Integrable weighted (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    rw [← IntegrableOn, ← uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact intervalIntegrable_iff.mp hweighted
  have htotal : (∫⁻ e, (if e.1 then
      ∫⁻ t in Set.Iic e.2.1, ENNReal.ofReal (cost t)
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) else 0)
      ∂SubjectLaw.baselineExitRecordLaw reference d0) < ⊤ := by
    rw [SubjectLaw.baselineExitIntegral_eq_survivalRetention
      reference lambda0 d0 hd0 hAssignment lam1 hlam1_meas, hrewrite]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hwint.lintegral_lt_top
  have hkl := SubjectLaw.baselinePerturb_observedKL_eq_exitIntegral_of_finite
    reference lambda0 d0 hd0 lam1 hlam1_meas hlam1_pos hlambda0 hfinite htotal
  constructor
  · rw [hkl]
    exact htotal.ne
  · rw [hkl, SubjectLaw.baselineExitIntegral_eq_survivalRetention
      reference lambda0 d0 hd0 hAssignment lam1 hlam1_meas, hrewrite]
    exact toReal_ofReal_mul_setLIntegral_ofReal
      (Pbase.p true) hp weighted hweighted hweighted0

/-- Finite-sample weighted KL identity for the explicit perturbation. -/
lemma SubjectLaw.baselinePerturb_sampleKL_weighted
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0)
    (hAssignment : AssignmentLaw reference)
    (lam1 : ℝ → ℝ) (hlam1_meas : Measurable lam1)
    (hlam1_pos : ∀ t ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ lam1 t)
    (hlambda0 : 0 < lambda0)
    (hfinite : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity
        (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 a))
    (hweighted : IntervalIntegrable (fun t : ℝ =>
      survival (SubjectLaw.baseline reference lambda0 d0 hd0) true t *
        retention (SubjectLaw.baseline reference lambda0 d0 hd0) true t *
        (lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0))
      volume 0 1) (n : ℕ) :
    InformationTheory.klDiv
      (sampleLaw (SubjectLaw.perturbTreatment
        (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 hfinite) n)
      (sampleLaw (SubjectLaw.baseline reference lambda0 d0 hd0) n) < ⊤ ∧
    (InformationTheory.klDiv
      (sampleLaw (SubjectLaw.perturbTreatment
        (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 hfinite) n)
      (sampleLaw (SubjectLaw.baseline reference lambda0 d0 hd0) n)).toReal =
      (n : ℝ) * (SubjectLaw.baseline reference lambda0 d0 hd0).p true *
        ∫ t in (0 : ℝ)..1,
          survival (SubjectLaw.baseline reference lambda0 d0 hd0) true t *
            retention (SubjectLaw.baseline reference lambda0 d0 hd0) true t *
            (lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0) := by
  let P := SubjectLaw.perturbTreatment
    (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 hfinite
  let Q := SubjectLaw.baseline reference lambda0 d0 hd0
  have hobs := SubjectLaw.baselinePerturb_observedKL_weighted reference lambda0 d0
    hd0 hAssignment lam1 hlam1_meas hlam1_pos hlambda0 hfinite hweighted
  have hdata := InformationTheory.klDiv_ne_top_iff.mp hobs.1
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure Q.latent := ⟨Q.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map P.observe_aemeasurable
  letI : IsProbabilityMeasure (observedLaw Q) :=
    Measure.isProbabilityMeasure_map Q.observe_aemeasurable
  have hprod := Causalean.Mathlib.InformationTheory.productKL_tensorization
    n (observedLaw P) (observedLaw Q) hdata.1 hdata.2
  constructor
  · exact lt_top_iff_ne_top.mpr hprod.product_ne_top
  · rw [show sampleLaw P n = Measure.pi (fun _ : Fin n => observedLaw P) from rfl,
      show sampleLaw Q n = Measure.pi (fun _ : Fin n => observedLaw Q) from rfl]
    rw [Causalean.Mathlib.InformationTheory.productKL_tensorization_of_finite
      n (observedLaw P) (observedLaw Q) hdata.1 hdata.2, hobs.2]
    ring

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

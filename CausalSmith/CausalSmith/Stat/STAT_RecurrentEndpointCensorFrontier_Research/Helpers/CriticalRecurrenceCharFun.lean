module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalPoissonExponent
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SelectedRecurrenceCharFun

/-!
# Critical recurrence characteristic-function identification

The selected-arm Poisson exponent equals the actual two-arm critical exponent.
Transport through the selected joint law and integrate its assignment cells to
identify the observed characteristic function without cross-arm independence.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The critical exponent reads only the assigned exposure coordinates. -/
-- @node: criticalPoissonExponent_eq_selectedExposureHistory
lemma criticalPoissonExponent_eq_selectedExposureHistory (c : ClassConstants)
    (P : SubjectLaw) {n : ℕ} (z : Fin n → LatentSubject) (u : ℝ) :
    criticalPoissonExponent c P n (fun i => observe (z i)) u =
      criticalPoissonExponent c P n
        (fun i => recurrenceExposureHistory (selectedArmExposure (z i))) u := by
  unfold criticalPoissonExponent criticalSignedRecurrenceWeight
  simp_rw [recurrenceSubjectWeight_eq_selectedExposureHistory]

/-- The unassigned arm contributes zero to the compensated exponential kernel,
so the two-arm exponent is exactly the sum of assigned-arm exponents. -/
-- @node: criticalPoissonExponent_eq_selected_sum
lemma criticalPoissonExponent_eq_selected_sum (c : ClassConstants)
    (P : SubjectLaw) (n : ℕ) (e : Fin n → Arm × (ℝ × ENNReal)) (u : ℝ) :
    criticalPoissonExponent c P n (fun j => recurrenceExposureHistory (e j)) u =
    ∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - bandwidth c n),
      (Complex.exp (Complex.I *
        ((u * (Real.sqrt ((n : ℝ) / Real.log n) / Real.sqrt (criticalVariance c P))) *
          ((if (e i).1 then (1 : ℝ) else -1) *
            recurrenceSubjectWeight c (bandwidth c n) (e i).1
              (fun j => recurrenceExposureHistory (e j)) i t) : ℝ)) - 1 -
       Complex.I *
        ((u * (Real.sqrt ((n : ℝ) / Real.log n) / Real.sqrt (criticalVariance c P))) *
          ((if (e i).1 then (1 : ℝ) else -1) *
            recurrenceSubjectWeight c (bandwidth c n) (e i).1
              (fun j => recurrenceExposureHistory (e j)) i t) : ℝ)) *
        (P.lam (e i).1 t : ℂ) := by
  classical
  unfold criticalPoissonExponent
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hz (a : Arm) (ha : (e i).1 ≠ a) (t : ℝ) :
      criticalSignedRecurrenceWeight c P a
        (fun j => recurrenceExposureHistory (e j)) i t = 0 := by
    unfold criticalSignedRecurrenceWeight
    rw [recurrenceSubjectWeight_zero_off_assignment c _ a _ i ha]
    ring
  have hw (a : Arm) (t : ℝ) :
      u * criticalSignedRecurrenceWeight c P a
        (fun j => recurrenceExposureHistory (e j)) i t =
      (u * (Real.sqrt ((n : ℝ) / Real.log n) / Real.sqrt (criticalVariance c P))) *
        ((if a then (1 : ℝ) else -1) * recurrenceSubjectWeight c (bandwidth c n) a
          (fun j => recurrenceExposureHistory (e j)) i t) := by
    unfold criticalSignedRecurrenceWeight
    ring
  cases hi : (e i).1
  · have ht := hz true (by simp [hi])
    simp only [Fintype.sum_bool, ht, mul_zero, Complex.ofReal_zero,
      Complex.exp_zero, sub_self, zero_sub, zero_mul, intervalIntegral.integral_zero,
      zero_add, add_zero]
    simp_rw [hw]
  · have hf := hz false (by simp [hi])
    simp only [Fintype.sum_bool, hf, mul_zero, Complex.ofReal_zero,
      Complex.exp_zero, sub_self, zero_sub, zero_mul, intervalIntegral.integral_zero,
      zero_add, add_zero]
    simp_rw [hw]

/-- The genuine critical exponential expectation disintegrates over the same
assignment cells as the recurrence characteristic function. -/
-- @node: criticalPoissonExponent_expectation_eq_assignment_integrals
lemma criticalPoissonExponent_expectation_eq_assignment_integrals
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    {n : ℕ} (hn : 3 ≤ n) (u : ℝ) :
    (∫ s, Complex.exp (criticalPoissonExponent c P n s u) ∂sampleLaw P n) =
    ∑ b : Fin n → Arm, ∫ e, Complex.exp (criticalPoissonExponent c P n
      (fun j => recurrenceExposureHistory (e j)) u)
      ∂Measure.pi (fun i : Fin n =>
        (P.latent.map (fun z : LatentSubject =>
          (z.treatment, (z.death (b i), z.censor (b i))))).restrict
            {e | e.1 = b i}) := by
  classical
  obtain ⟨hν, hmix⟩ := iid_selectedArm_exposure_recurrence_map_eq_pi_mixture
    P hP.randomAssignment hP.recurrenceDeathIndependence hP.independentCensoring
    hP.poissonRecurrence n
  letI (a : Arm) : IsFiniteMeasure (recurrenceIntensity P a) := hν a
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let E : Arm → Measure (Arm × (ℝ × ENNReal)) := fun a =>
    (P.latent.map (fun z : LatentSubject =>
      (z.treatment, (z.death a, z.censor a)))).restrict {e | e.1 = a}
  let R : Arm → Measure RecurConfig := fun a => canonicalRecurrenceLaw P a
  letI (a : Arm) : IsProbabilityMeasure
      (P.latent.map (fun z : LatentSubject =>
        (z.treatment, (z.death a, z.censor a)))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI (a : Arm) : IsFiniteMeasure (E a) := by dsimp [E]; infer_instance
  letI (a : Arm) : IsProbabilityMeasure (R a) := by
    dsimp [R]
    unfold canonicalRecurrenceLaw canonicalRecurrenceLawOf
    infer_instance
  let F : (Fin n → (Arm × (ℝ × ENNReal)) × RecurConfig) → ℂ := fun p =>
    Complex.exp (criticalPoissonExponent c P n
      (fun i => recurrenceExposureHistory (p i).1) u)
  have hF : Measurable F := by
    apply Complex.measurable_exp.comp
    apply (measurable_criticalPoissonExponent c P hP hn u).comp
    fun_prop
  have hb (p) : ‖F p‖ ≤ 1 :=
    critical_poisson_exponential_norm_le_one c P hP hn _ u
  have ho : Measurable (fun z : Fin n → LatentSubject => fun i => observe (z i)) := by
    fun_prop
  have hp : Measurable (fun z : Fin n → LatentSubject =>
      fun i => (selectedArmExposure (z i), selectedArmRecurrence (z i))) := by
    fun_prop
  rw [recurrence_sampleLaw_eq_latent_map,
    integral_map ho.aemeasurable (by fun_prop)]
  simp_rw [criticalPoissonExponent_eq_selectedExposureHistory]
  change (∫ z, F (fun i => (selectedArmExposure (z i), selectedArmRecurrence (z i)))
    ∂Measure.pi (fun _ : Fin n => P.latent)) = _
  rw [← integral_map hp.aemeasurable hF.aestronglyMeasurable, hmix]
  change (∫ p, F p ∂Measure.pi (fun _ : Fin n =>
    (E false).prod (R false) + (E true).prod (R true))) = _
  rw [selected_mixture_integral_eq_sum_assignment_integrals n E R F hF hb]
  simp only [F, integral_const, probReal_univ, one_smul]
  rfl

/-- The observed standardized recurrence contrast has the expectation of the
actual compensated Poisson exponent as its characteristic function. -/
-- @node: critical_recurrence_charFun_eq_exponential_expectation
lemma critical_recurrence_charFun_eq_exponential_expectation
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    {n : ℕ} (hn : 3 ≤ n) (u : ℝ) :
    (∫ s : Fin n → ObsHistory, Complex.exp (Complex.I * (u *
      (Real.sqrt ((n : ℝ) / Real.log n) *
        (recurrenceError c P true s (bandwidth c n) -
          recurrenceError c P false s (bandwidth c n)) /
        Real.sqrt (criticalVariance c P)) : ℝ)) ∂sampleLaw P n) =
    ∫ s, Complex.exp (criticalPoissonExponent c P n s u) ∂sampleLaw P n := by
  have hh := bandwidth_pos_and_le_cap c (show 0 < n by omega)
  have hh1 : bandwidth c n ≤ 1 := by linarith [c.x0_le]
  rw [criticalPoissonExponent_expectation_eq_assignment_integrals c P hP hn u]
  simp_rw [criticalPoissonExponent_eq_selected_sum]
  have he := recurrenceContrast_charFun_eq_assignment_exponents c P hP n
    hh.1 hh1 (u * (Real.sqrt ((n : ℝ) / Real.log n) / Real.sqrt (criticalVariance c P)))
  rw [← he]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro s
  change Complex.exp _ = Complex.exp _
  apply congrArg Complex.exp
  congr 1
  push_cast
  ring

/-- Taking expectations in roadmap (19) gives the standard Gaussian
characteristic-function limit along arbitrary triangular model laws. -/
-- @node: critical_recurrence_charFun_triangular_tendsto
lemma critical_recurrence_charFun_triangular_tendsto
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (u : ℝ) :
    Tendsto (fun n => ∫ s : Fin n → ObsHistory, Complex.exp (Complex.I * (u *
      (Real.sqrt ((n : ℝ) / Real.log n) *
        (recurrenceError c (Pseq n) true s (bandwidth c n) -
          recurrenceError c (Pseq n) false s (bandwidth c n)) /
        Real.sqrt (criticalVariance c (Pseq n))) : ℝ)) ∂sampleLaw (Pseq n) n)
      atTop (nhds (Complex.exp (-((u ^ 2 / 2 : ℝ) : ℂ)))) := by
  apply (critical_poisson_exponential_expectation_tendsto c hk Pseq hP u).congr'
  filter_upwards [eventually_ge_atTop 3] with n hn
  exact (critical_recurrence_charFun_eq_exponential_expectation c (Pseq n) (hP n) hn u).symm

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SelectedRecurrenceContrast

/-!
# Signed selected-arm Poisson characteristic functions

The contrast is a sum of one-hot subject scores. Conditional on a fixed
exposure array, each subject uses the canonical Poisson law of its assigned
arm. The resulting exponent retains the actual exposure-dependent weights.
Finite assignment-vector disintegration and Fubini then identify the observed
contrast characteristic function with the assignment-cell average of these
exponents, without requiring independence between potential arms.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The two-arm contrast equals the signed sum of the selected-arm scores,
including their same-arm compensators. -/
-- @node: recurrenceConcreteExposureContrast_eq_selected_sum
lemma recurrenceConcreteExposureContrast_eq_selected_sum
    (c : ClassConstants) (P : SubjectLaw) (n : ℕ) (h : ℝ)
    (e : Fin n → Arm × (ℝ × ENNReal)) (r : Fin n → RecurConfig) :
    recurrenceConcreteExposureScore c P true n h e r -
      recurrenceConcreteExposureScore c P false n h e r =
    ∑ i : Fin n, (if (e i).1 then (1 : ℝ) else -1) *
      ((∑ k : Fin (r i).1, if ((r i).2 k).1 ≤ 1 - h then
        recurrenceSubjectWeight c h (e i).1
          (fun j => recurrenceExposureHistory (e j)) i ((r i).2 k).1 else 0) -
      ∫ t in (0 : ℝ)..(1 - h), recurrenceSubjectWeight c h (e i).1
        (fun j => recurrenceExposureHistory (e j)) i t * P.lam (e i).1 t) := by
  classical
  unfold recurrenceConcreteExposureScore
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hz (a : Arm) (ha : (e i).1 ≠ a) (t : ℝ) :
      recurrenceSubjectWeight c h a (fun j => recurrenceExposureHistory (e j)) i t = 0 := by
    apply recurrenceSubjectWeight_zero_off_assignment
    exact ha
  cases hi : (e i).1
  · have ht := hz true (by simp [hi])
    simp [hi, ht]
  · have hf := hz false (by simp [hi])
    simp [hi, hf]

/-- Given the exposure array, the signed contrast has the compensated Poisson
exponent with each subject's assigned intensity, without cross-arm independence. -/
-- @node: recurrenceConcreteExposureContrast_conditional_charFun
lemma recurrenceConcreteExposureContrast_conditional_charFun
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    [∀ a : Arm, IsFiniteMeasure (recurrenceIntensity P a)] (n : ℕ)
    (e : Fin n → Arm × (ℝ × ENNReal)) {h : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (u : ℝ) :
    (∫ r : Fin n → RecurConfig, Complex.exp (Complex.I *
      (u * (recurrenceConcreteExposureScore c P true n h e r -
        recurrenceConcreteExposureScore c P false n h e r) : ℝ))
      ∂Measure.pi (fun i : Fin n => canonicalRecurrenceLaw P (e i).1)) =
    Complex.exp (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
      (Complex.exp (Complex.I * (u * ((if (e i).1 then (1 : ℝ) else -1) *
        recurrenceSubjectWeight c h (e i).1
          (fun j => recurrenceExposureHistory (e j)) i t) : ℝ)) - 1 -
       Complex.I * (u * ((if (e i).1 then (1 : ℝ) else -1) *
        recurrenceSubjectWeight c h (e i).1
          (fun j => recurrenceExposureHistory (e j)) i t) : ℝ)) *
        (P.lam (e i).1 t : ℂ)) := by
  let w := fun i t => (if (e i).1 then (1 : ℝ) else -1) *
    recurrenceSubjectWeight c h (e i).1
      (fun j => recurrenceExposureHistory (e j)) i t
  let f := fun i t => if t ≤ 1 - h then w i t else 0
  have hf (i : Fin n) : Measurable (f i) := by
    apply Measurable.ite (measurableSet_le measurable_id measurable_const)
    · exact measurable_const.mul (measurable_recurrenceSubjectWeight c h (e i).1 _ i)
    · exact measurable_const
  have hK (i : Fin n) (t : ℝ) : |f i t| ≤ weightEnvelope c := by
    by_cases ht : t ≤ 1 - h
    · dsimp [f]
      rw [if_pos ht]
      dsimp [w]
      cases ha : (e i).1
      · simpa using recurrenceSubjectWeight_abs_le c hh false
          (fun j => recurrenceExposureHistory (e j)) i t
      · simpa using recurrenceSubjectWeight_abs_le c hh true
          (fun j => recurrenceExposureHistory (e j)) i t
    · simp only [f, if_neg ht, abs_zero]
      unfold weightEnvelope continuationNorm
      positivity
  have hc := recurrence_canonical_independent_charFun n
    (fun i => recurrenceIntensity P (e i).1) f hf hK u
  have hmean (i : Fin n) : (∫ t, f i t ∂recurrenceIntensity P (e i).1) =
      ∫ t in (0 : ℝ)..(1 - h), w i t * P.lam (e i).1 t :=
    recurrenceIntensity_integral_truncated P hP.poissonRecurrence (e i).1 (w i)
      (by linarith) (by linarith)
  have hexp (i : Fin n) : (∫ t,
      (Complex.exp (Complex.I * (u * f i t : ℝ)) - 1 -
        Complex.I * (u * f i t : ℝ)) ∂recurrenceIntensity P (e i).1) =
      ∫ t in (0 : ℝ)..(1 - h),
        (Complex.exp (Complex.I * (u * w i t : ℝ)) - 1 -
          Complex.I * (u * w i t : ℝ)) * (P.lam (e i).1 t : ℂ) := by
    have he : (fun t => Complex.exp (Complex.I * (u * f i t : ℝ)) - 1 -
        Complex.I * (u * f i t : ℝ)) = fun t => if t ≤ 1 - h then
          Complex.exp (Complex.I * (u * w i t : ℝ)) - 1 -
            Complex.I * (u * w i t : ℝ) else 0 := by
      funext t
      dsimp [f]
      split_ifs <;> simp
    rw [he]
    exact recurrenceIntensity_integral_truncated_complex P hP.poissonRecurrence (e i).1 _
      (by linarith) (by linarith)
  simp_rw [hmean, hexp] at hc
  have hscore (r : Fin n → RecurConfig) :
      recurrenceConcreteExposureScore c P true n h e r -
        recurrenceConcreteExposureScore c P false n h e r =
      ∑ i : Fin n, ((∑ k : Fin (r i).1, f i (((r i).2 k).1)) -
        ∫ t in (0 : ℝ)..(1 - h), w i t * P.lam (e i).1 t) := by
    rw [recurrenceConcreteExposureContrast_eq_selected_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [f, w]
    rw [mul_sub, Finset.mul_sum, ← intervalIntegral.integral_const_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> ring
    · congr 1
      funext t
      ring
  simp_rw [hscore]
  exact hc

/-- On a fixed assignment-vector cell, Fubini averages the exact selected-arm
Poisson formula over the finite exposure measure. -/
-- @node: recurrenceConcreteExposureContrast_assignment_product_charFun
lemma recurrenceConcreteExposureContrast_assignment_product_charFun
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    [∀ a : Arm, IsFiniteMeasure (recurrenceIntensity P a)] (n : ℕ)
    (b : Fin n → Arm)
    (Q : Measure (Fin n → Arm × (ℝ × ENNReal))) [IsFiniteMeasure Q]
    (hb : ∀ᵐ e ∂Q, ∀ i, (e i).1 = b i)
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (u : ℝ) :
    (∫ p : (Fin n → Arm × (ℝ × ENNReal)) × (Fin n → RecurConfig),
      Complex.exp (Complex.I *
        (u * (recurrenceConcreteExposureScore c P true n h p.1 p.2 -
          recurrenceConcreteExposureScore c P false n h p.1 p.2) : ℝ))
      ∂Q.prod (Measure.pi (fun i : Fin n => canonicalRecurrenceLaw P (b i)))) =
    ∫ e, Complex.exp (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
      (Complex.exp (Complex.I * (u * ((if (e i).1 then (1 : ℝ) else -1) *
        recurrenceSubjectWeight c h (e i).1
          (fun j => recurrenceExposureHistory (e j)) i t) : ℝ)) - 1 -
       Complex.I * (u * ((if (e i).1 then (1 : ℝ) else -1) *
        recurrenceSubjectWeight c h (e i).1
          (fun j => recurrenceExposureHistory (e j)) i t) : ℝ)) *
        (P.lam (e i).1 t : ℂ)) ∂Q := by
  letI (i : Fin n) : IsProbabilityMeasure (canonicalRecurrenceLaw P (b i)) := by
    unfold canonicalRecurrenceLaw canonicalRecurrenceLawOf
    infer_instance
  have hs (a : Arm) := measurable_recurrenceConcreteExposureScore c P
    hP.poissonRecurrence a n hh.le hh1
  have hi : Integrable (fun p : (Fin n → Arm × (ℝ × ENNReal)) ×
      (Fin n → RecurConfig) => Complex.exp (Complex.I *
      (u * (recurrenceConcreteExposureScore c P true n h p.1 p.2 -
        recurrenceConcreteExposureScore c P false n h p.1 p.2) : ℝ)))
      (Q.prod (Measure.pi (fun i : Fin n => canonicalRecurrenceLaw P (b i)))) := by
    apply Integrable.of_bound (by fun_prop) 1
    exact Filter.Eventually.of_forall (fun p => by
      simp [Complex.norm_exp, Complex.mul_re])
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [hb] with e he
  have hm : (Measure.pi (fun i : Fin n => canonicalRecurrenceLaw P (b i))) =
      Measure.pi (fun i : Fin n => canonicalRecurrenceLaw P (e i).1) := by
    congr 1
    funext i
    rw [he i]
  rw [hm]
  exact recurrenceConcreteExposureContrast_conditional_charFun c P hP n e hh hh1 u

/-- A finite iid two-component measure mixture disintegrates over the full
assignment vector, retaining its component measure in each coordinate. -/
-- @node: selected_mixture_pi_eq_sum_assignments
lemma selected_mixture_pi_eq_sum_assignments {X : Type*} [MeasurableSpace X]
    (n : ℕ) (M : Arm → Measure X) [∀ a, IsFiniteMeasure (M a)] :
    Measure.pi (fun _ : Fin n => M false + M true) =
      ∑ b : Fin n → Arm, Measure.pi (fun i : Fin n => M (b i)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.coe_finset_sum, Finset.sum_apply]
  simp_rw [Measure.pi_pi]
  rw [← Fintype.prod_sum (fun (i : Fin n) (a : Arm) => M a (s i))]
  simp [Measure.add_apply, add_comm]

/-- Integrating an iid two-cell product mixture is a finite sum of exposure
integrals followed by independent, assignment-specific recurrence integrals. -/
-- @node: selected_mixture_integral_eq_sum_assignment_integrals
lemma selected_mixture_integral_eq_sum_assignment_integrals
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (n : ℕ) (E : Arm → Measure X) (R : Arm → Measure Y)
    [∀ a, IsFiniteMeasure (E a)] [∀ a, IsFiniteMeasure (R a)]
    (F : (Fin n → X × Y) → ℂ) (hF : Measurable F)
    (hbound : ∀ p, ‖F p‖ ≤ 1) :
    (∫ p, F p ∂Measure.pi (fun _ : Fin n =>
      (E false).prod (R false) + (E true).prod (R true))) =
    ∑ b : Fin n → Arm, ∫ e, ∫ r, F (fun i => (e i, r i))
      ∂Measure.pi (fun i : Fin n => R (b i))
      ∂Measure.pi (fun i : Fin n => E (b i)) := by
  classical
  rw [selected_mixture_pi_eq_sum_assignments n (fun a => (E a).prod (R a))]
  have hI (b : Fin n → Arm) : Integrable F
      (Measure.pi (fun i : Fin n => (E (b i)).prod (R (b i)))) :=
    Integrable.of_bound hF.aestronglyMeasurable 1
      (Filter.Eventually.of_forall hbound)
  rw [integral_finsetSum_measure (fun b _ => hI b)]
  apply Finset.sum_congr rfl
  intro b _
  let g : (Fin n → X) × (Fin n → Y) → ℂ :=
    fun p => F (fun i => (p.1 i, p.2 i))
  have hg : Measurable g := by
    apply hF.comp
    fun_prop
  have hgi : Integrable g
      ((Measure.pi (fun i : Fin n => E (b i))).prod
        (Measure.pi (fun i : Fin n => R (b i)))) :=
    Integrable.of_bound hg.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun p => hbound _))
  have hp := measurePreserving_arrowProdEquivProdArrow X Y (Fin n)
    (fun i => E (b i)) (fun i => R (b i))
  calc
    _ = ∫ p, g p ∂(Measure.pi (fun i : Fin n => E (b i))).prod
        (Measure.pi (fun i : Fin n => R (b i))) := by
      simpa [g, MeasurableEquiv.arrowProdEquivProdArrow,
        Equiv.arrowProdEquivProdArrow] using hp.integral_comp' g
    _ = _ := integral_prod g hgi

set_option maxHeartbeats 1000000 in
/-- The observed contrast characteristic function is the finite
assignment-vector average of its actual same-arm Poisson exponents. -/
-- @node: recurrenceContrast_charFun_eq_assignment_exponents
lemma recurrenceContrast_charFun_eq_assignment_exponents
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (n : ℕ)
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (u : ℝ) :
    (∫ s : Fin n → ObsHistory, Complex.exp (Complex.I *
      (u * (recurrenceError c P true s h - recurrenceError c P false s h) : ℝ))
      ∂sampleLaw P n) =
    ∑ b : Fin n → Arm, ∫ e, Complex.exp (∑ i : Fin n,
      ∫ t in (0 : ℝ)..(1 - h),
        (Complex.exp (Complex.I * (u * ((if (e i).1 then (1 : ℝ) else -1) *
          recurrenceSubjectWeight c h (e i).1
            (fun j => recurrenceExposureHistory (e j)) i t) : ℝ)) - 1 -
         Complex.I * (u * ((if (e i).1 then (1 : ℝ) else -1) *
          recurrenceSubjectWeight c h (e i).1
            (fun j => recurrenceExposureHistory (e j)) i t) : ℝ)) *
          (P.lam (e i).1 t : ℂ))
      ∂Measure.pi (fun i : Fin n =>
        (P.latent.map (fun z : LatentSubject =>
          (z.treatment, (z.death (b i), z.censor (b i))))).restrict
            {e | e.1 = b i}) := by
  classical
  obtain ⟨hν, hmix⟩ := recurrenceContrast_charFun_eq_selected_mixture c P hP n hh hh1 u
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
    Complex.exp (Complex.I * (u *
      (recurrenceConcreteExposureScore c P true n h (fun i => (p i).1)
        (fun i => (p i).2) -
       recurrenceConcreteExposureScore c P false n h (fun i => (p i).1)
        (fun i => (p i).2)) : ℝ))
  have hs (a : Arm) := measurable_recurrenceConcreteExposureScore c P
    hP.poissonRecurrence a n hh.le hh1
  have hm : Measurable (fun p : Fin n → (Arm × (ℝ × ENNReal)) × RecurConfig =>
      ((fun i => (p i).1), (fun i => (p i).2))) := by fun_prop
  have hscore (a : Arm) : Measurable (fun p : Fin n →
      (Arm × (ℝ × ENNReal)) × RecurConfig =>
      recurrenceConcreteExposureScore c P a n h (fun i => (p i).1)
        (fun i => (p i).2)) := (hs a).comp hm
  have hF : Measurable F := by
    exact Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp (measurable_const.mul
        ((hscore true).sub (hscore false)))))
  have hbound (p) : ‖F p‖ ≤ 1 := by
    simp [F, Complex.norm_exp, Complex.mul_re]
  rw [hmix]
  change (∫ p, F p ∂Measure.pi (fun _ : Fin n =>
    (E false).prod (R false) + (E true).prod (R true))) = _
  rw [selected_mixture_integral_eq_sum_assignment_integrals n E R F hF hbound]
  apply Finset.sum_congr rfl
  intro b _
  have hb : ∀ᵐ e ∂Measure.pi (fun i : Fin n => E (b i)), ∀ i, (e i).1 = b i := by
    rw [ae_all_iff]
    intro i
    have hcell : ∀ᵐ x ∂E (b i), x.1 = b i :=
      ae_restrict_mem (measurable_fst (measurableSet_singleton (b i)))
    exact (Measure.tendsto_eval_ae_ae (μ := fun i : Fin n => E (b i))
      (i := i)).eventually hcell
  apply integral_congr_ae
  filter_upwards [hb] with e he
  have hmR : Measure.pi (fun i : Fin n => R (b i)) =
      Measure.pi (fun i : Fin n => canonicalRecurrenceLaw P (e i).1) := by
    congr 1
    funext i
    dsimp [R]
    rw [he i]
  rw [hmR]
  exact recurrenceConcreteExposureContrast_conditional_charFun c P hP n e hh hh1 u

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

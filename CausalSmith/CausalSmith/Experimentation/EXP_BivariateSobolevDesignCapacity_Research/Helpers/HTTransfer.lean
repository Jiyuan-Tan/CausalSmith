module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.HTConditionalMoments

/-! # Gaussian HT joint-experiment variance transfer

The conditional moments integrate over the original covariates to give the actual
HT mean, finite second moment, and exact excess-variance identity.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ The sample-average treatment effect has a finite second moment.](goal) Under [the stated conditions](hyp:hd). -/
-- @node: tauFn_sampleMean_memLp
lemma tauFn_sampleMean_memLp {n d : ℕ} (hd : 0 < d) :
    MemLp (fun x : Covariates n d => (n : ℝ)⁻¹ * ∑ i, tauFn hd (x i))
      2 (covLaw n d) := by
  letI : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  letI : IsProbabilityMeasure (cubeMeasure d) := by unfold cubeMeasure; infer_instance
  have hi (i : Fin n) : MemLp (fun x : Covariates n d => tauFn hd (x i))
      2 (covLaw n d) :=
    (tauFn_memLp hd).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => cubeMeasure d) i)
  simpa only [Finset.sum_apply] using
    (memLp_finsetSum' Finset.univ (fun i _ => hi i)).const_mul (n : ℝ)⁻¹

/-- [ Averaging the independent uniform units preserves the population treatment mean.](goal) Under [the stated conditions](hyp:hn,hd). -/
-- @node: tauFn_sampleMean_mean
lemma tauFn_sampleMean_mean {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    (∫ x : Covariates n d, (n : ℝ)⁻¹ * ∑ i, tauFn hd (x i)
      ∂covLaw n d) = tau0 := by
  letI : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  letI : IsProbabilityMeasure (cubeMeasure d) := by unfold cubeMeasure; infer_instance
  have hi (i : Fin n) : Integrable (fun x : Covariates n d => tauFn hd (x i))
      (covLaw n d) :=
    (measurePreserving_eval (fun _ : Fin n => cubeMeasure d) i).integrable_comp_of_integrable (tauFn_integrable hd)
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hi i)]
  have heval (i : Fin n) :
      (∫ x : Covariates n d, tauFn hd (x i) ∂covLaw n d) = tau0 := by
    unfold covLaw
    rw [integral_comp_eval (μ := fun _ : Fin n => cubeMeasure d)
      (i := i) (tauFn_integrable hd).aestronglyMeasurable, tauFn_mean hd]
  simp only [heval, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- [ The centered sample treatment-effect square contributes delta squared over n.](goal) Under [the stated conditions](hyp:hn,hd). -/
-- @node: tauFn_sampleMean_centered_second_moment
lemma tauFn_sampleMean_centered_second_moment {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    (∫ x : Covariates n d, ((n : ℝ)⁻¹ * ∑ i, tauFn hd (x i) - tau0) ^ 2
      ∂covLaw n d) = delta ^ 2 / n := by
  have h := tauFn_sampleMean_variance (n := n) hd
  rw [variance_eq_integral (tauFn_sampleMean_memLp hd).aemeasurable,
    tauFn_sampleMean_mean hn hd] at h
  exact h

/-- The conditional imbalance second moment is integrable over original samples. [The asserted mathematical result follows](goal). -/
-- @node: imbalance_kernel_second_moment_integrable
lemma imbalance_kernel_second_moment_integrable {n d : ℕ}
    (π : Design n d) (m : CenteredL2Fn d) :
    Integrable (fun x : Covariates n d =>
      ∫ z, (∑ i, sgn (z i) * m.val (x i)) ^ 2 ∂π.val x) (covLaw n d) := by
  letI : IsMarkovKernel π.val := π.property
  letI : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  letI : IsProbabilityMeasure (cubeMeasure d) := by unfold cubeMeasure; infer_instance
  have hm : Measurable m.val := m.property.1
  have hi (i : Fin n) : Integrable (fun x : Covariates n d => m.val (x i) ^ 2)
      (covLaw n d) :=
    (m.property.2.1.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => cubeMeasure d) i)).integrable_sq
  have hb : Integrable (fun x : Covariates n d =>
      (n : ℝ) * ∑ i, m.val (x i) ^ 2) (covLaw n d) :=
    (integrable_finsetSum Finset.univ (fun i _ => hi i)).const_mul _
  have hf : Measurable (fun ω : Covariates n d × Signs n =>
      (∑ i, sgn (ω.2 i) * m.val (ω.1 i)) ^ 2) := by fun_prop
  apply hb.mono' hf.stronglyMeasurable.integral_kernel_prod_right'.aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
  calc
    _ ≤ ∫ _z : Signs n, (n : ℝ) * ∑ i, m.val (x i) ^ 2 ∂π.val x :=
      integral_mono Integrable.of_finite (integrable_const _)
        (fun z => signed_sum_sq_le z _)
    _ = _ := by simp

/-- [ Taking the real value of the loss gives its iterated real second moment.](goal) -/
-- @node: loss_toReal_eq_kernel_second_moment
lemma loss_toReal_eq_kernel_second_moment {n d : ℕ}
    (π : Design n d) (m : CenteredL2Fn d) :
    (loss π m.val).toReal = (4 / (n : ℝ)) *
      ∫ x : Covariates n d, ∫ z,
        (∑ i, sgn (z i) * m.val (x i)) ^ 2 ∂π.val x ∂covLaw n d := by
  letI : IsMarkovKernel π.val := π.property
  have hnonneg (x : Covariates n d) :
      0 ≤ ∫ z, (∑ i, sgn (z i) * m.val (x i)) ^ 2 ∂π.val x :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hinner (x : Covariates n d) :
      (∫⁻ z, ENNReal.ofReal ((∑ i, sgn (z i) * m.val (x i)) ^ 2) ∂π.val x) =
        ENNReal.ofReal (∫ z, (∑ i, sgn (z i) * m.val (x i)) ^ 2 ∂π.val x) :=
    (ofReal_integral_eq_lintegral_ofReal Integrable.of_finite
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).symm
  unfold loss
  simp_rw [hinner]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (imbalance_kernel_second_moment_integrable π m)
    (Filter.Eventually.of_forall hnonneg), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (integral_nonneg hnonneg)]

/-- Integrating the fair conditional Gaussian square over covariates yields exactly
its treatment variation, prognostic loss, and selected-noise contribution. Under [the stated conditions](hyp:hn,hd,hfair), [the asserted mathematical result follows](goal). -/
-- @node: ht_gaussian_outer_centered_second_moment
lemma ht_gaussian_outer_centered_second_moment {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d) (m : CenteredL2Fn d) (π : Design n d)
    (hfair : FairKernel π.val) :
    (∫ x : Covariates n d, ∫ y, ∫ z, (htEstimator y z - tau0) ^ 2
      ∂π.val x ∂gaussianCompletion hd m x ∂covLaw n d) =
      delta ^ 2 / n + (loss π m.val).toReal / n + 4 / n := by
  letI : IsMarkovKernel π.val := π.property
  letI : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  letI : IsProbabilityMeasure (cubeMeasure d) := by unfold cubeMeasure; infer_instance
  letI : IsProbabilityMeasure (covLaw n d) := by unfold covLaw; infer_instance
  have heq : (∫ x : Covariates n d, ∫ y, ∫ z, (htEstimator y z - tau0) ^ 2
      ∂π.val x ∂gaussianCompletion hd m x ∂covLaw n d) =
      ∫ x : Covariates n d,
        (((n : ℝ)⁻¹ * ∑ i, tauFn hd (x i) - tau0) ^ 2 +
          (2 / (n : ℝ)) ^ 2 * (∫ z, (∑ i, sgn (z i) * m.val (x i)) ^ 2 ∂π.val x)) +
          4 / (n : ℝ) ∂covLaw n d := by
    apply integral_congr_ae
    filter_upwards [hfair] with x hx
    exact ht_gaussian_kernel_centered_second_moment hd m x (π.val x) hx tau0
  rw [heq]
  have hA : Integrable (fun x : Covariates n d =>
      ((n : ℝ)⁻¹ * ∑ i, tauFn hd (x i) - tau0) ^ 2) (covLaw n d) :=
    ((tauFn_sampleMean_memLp (n := n) hd).sub (memLp_const tau0)).integrable_sq
  have hS := (imbalance_kernel_second_moment_integrable π m).const_mul ((2 / (n : ℝ)) ^ 2)
  have hAS : Integrable (fun x : Covariates n d =>
      ((n : ℝ)⁻¹ * ∑ i, tauFn hd (x i) - tau0) ^ 2 +
        (2 / (n : ℝ)) ^ 2 * (∫ z, (∑ i, sgn (z i) * m.val (x i)) ^ 2 ∂π.val x))
      (covLaw n d) := hA.add hS
  rw [integral_add hAS (integrable_const _), integral_add hA hS,
    integral_const, integral_const_mul, tauFn_sampleMean_centered_second_moment hn hd,
    loss_toReal_eq_kernel_second_moment]
  simp only [probReal_univ, one_smul]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  <;> ring

/-- [ The finite assignment space makes the actual statistic jointly Borel. This uses [the stated conclusion](goal). -/
-- @node: htEstimator_joint_measurable
@[fun_prop] lemma htEstimator_joint_measurable {n : ℕ} :
    Measurable (fun ω : Sched n × Signs n => htEstimator ω.1 ω.2) := by
  apply measurable_from_prod_countable_left
  intro z
  exact htEstimator_schedule_measurable z

/-- Each fixed assignment has an integrable centered square under its Gaussian schedule.](goal) Under [the stated conditions](hyp:hd). This uses [the stated conclusion](goal). -/
-- @node: ht_gaussian_schedule_centered_square_integrable
lemma ht_gaussian_schedule_centered_square_integrable {n d : ℕ} (hd : 0 < d)
    (m : CenteredL2Fn d) (x : Covariates n d) (z : Signs n) :
    Integrable (fun y => (htEstimator y z - tau0) ^ 2) (gaussianCompletion hd m x) := by
  letI : IsProbabilityMeasure (noiseLaw n) := by unfold noiseLaw; infer_instance
  change Integrable _ ((noiseLaw n).map (completionSchedule hd m.val x))
  have hm : Measurable (completionSchedule hd m.val x) := by
    unfold completionSchedule
    fun_prop
  apply (integrable_map_measure (by fun_prop) hm.aemeasurable).mpr
  exact ((ht_completion_noise_memLp hd m.val x z).sub (memLp_const tau0)).integrable_sq

/-- [ The actual joint experiment has a finite centered HT second moment.](goal) Under [the stated conditions](hyp:hd,hfair). -/
-- @node: ht_gaussian_joint_centered_square_integrable
lemma ht_gaussian_joint_centered_square_integrable {n d : ℕ} (hd : 0 < d)
    (m : CenteredL2Fn d) (π : Design n d) (hfair : FairKernel π.val) :
    Integrable (fun ω => (htEstimator ω.1.2 ω.2 - tau0) ^ 2)
      (experimentLaw (covLaw n d) (gaussianCompletion hd m) π.val) := by
  letI : IsMarkovKernel π.val := π.property
  letI := gaussianCompletion_markov (n := n) hd m
  letI : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  letI : IsProbabilityMeasure (cubeMeasure d) := by unfold cubeMeasure; infer_instance
  letI : IsProbabilityMeasure (covLaw n d) := by unfold covLaw; infer_instance
  have hF : Measurable (fun ω : (Covariates n d × Sched n) × Signs n =>
      (htEstimator ω.1.2 ω.2 - tau0) ^ 2) := by fun_prop
  have hG : Measurable (fun ω : Covariates n d × Sched n =>
      ∫ z, (htEstimator ω.2 z - tau0) ^ 2 ∂π.val ω.1) :=
    hF.stronglyMeasurable.integral_kernel_prod_right'
      (κ := π.val.comap Prod.fst measurable_fst) |>.measurable
  have hpoint (x : Covariates n d) : Integrable
      (fun y => ∫ z, (htEstimator y z - tau0) ^ 2 ∂π.val x)
      (gaussianCompletion hd m x) := by
    simp_rw [integral_fintype (Integrable.of_finite (μ := π.val x))]
    apply integrable_finsetSum
    intro z _
    simpa only [smul_eq_mul] using
      (ht_gaussian_schedule_centered_square_integrable hd m x z).const_mul ((π.val x).real {z})
  have houter : Integrable (fun x : Covariates n d => ∫ y,
      ‖∫ z, (htEstimator y z - tau0) ^ 2 ∂π.val x‖ ∂gaussianCompletion hd m x)
      (covLaw n d) := by
    have hnn (x : Covariates n d) (y : Sched n) :
        0 ≤ ∫ z, (htEstimator y z - tau0) ^ 2 ∂π.val x :=
      integral_nonneg (fun _ => sq_nonneg _)
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (hnn _ _)]
    have hA : Integrable (fun x : Covariates n d =>
        ((n : ℝ)⁻¹ * ∑ i, tauFn hd (x i) - tau0) ^ 2) (covLaw n d) :=
      ((tauFn_sampleMean_memLp (n := n) hd).sub (memLp_const tau0)).integrable_sq
    have hS := (imbalance_kernel_second_moment_integrable π m).const_mul ((2 / (n : ℝ)) ^ 2)
    apply ((hA.add hS).add (integrable_const (4 / (n : ℝ)))).congr
    filter_upwards [hfair] with x hx
    exact (ht_gaussian_kernel_centered_second_moment hd m x (π.val x) hx tau0).symm
  have hinner : Integrable (fun ω : Covariates n d × Sched n =>
      ∫ z, (htEstimator ω.2 z - tau0) ^ 2 ∂π.val ω.1)
      (covLaw n d ⊗ₘ gaussianCompletion hd m) :=
    (Measure.integrable_compProd_iff hG.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hpoint, houter⟩
  unfold experimentLaw
  apply (Measure.integrable_compProd_iff hF.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun _ => Integrable.of_finite), ?_⟩
  simpa only [Kernel.comap_apply, Real.norm_eq_abs, abs_sq] using hinner

/-- [ The fair Gaussian joint experiment is centered at the population treatment effect.](goal) Under [the stated conditions](hyp:hn,hd,hfair). -/
-- @node: ht_gaussian_joint_mean
lemma ht_gaussian_joint_mean {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (m : CenteredL2Fn d) (π : Design n d) (hfair : FairKernel π.val) :
    (∫ ω, htEstimator ω.1.2 ω.2
      ∂experimentLaw (covLaw n d) (gaussianCompletion hd m) π.val) = tau0 := by
  letI : IsMarkovKernel π.val := π.property
  letI := gaussianCompletion_markov (n := n) hd m
  letI : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  letI : IsProbabilityMeasure (cubeMeasure d) := by unfold cubeMeasure; infer_instance
  letI : IsProbabilityMeasure (covLaw n d) := by unfold covLaw; infer_instance
  letI : IsProbabilityMeasure
      (experimentLaw (covLaw n d) (gaussianCompletion hd m) π.val) := by
    unfold experimentLaw
    infer_instance
  have hf : Measurable (fun ω : (Covariates n d × Sched n) × Signs n =>
      htEstimator ω.1.2 ω.2) := by fun_prop
  have hmem : MemLp (fun ω => htEstimator ω.1.2 ω.2 - tau0) 2
      (experimentLaw (covLaw n d) (gaussianCompletion hd m) π.val) :=
    (memLp_two_iff_integrable_sq (hf.sub measurable_const).aestronglyMeasurable).mpr
      (ht_gaussian_joint_centered_square_integrable hd m π hfair)
  have hint : Integrable (fun ω => htEstimator ω.1.2 ω.2)
      (experimentLaw (covLaw n d) (gaussianCompletion hd m) π.val) := by
    have hc : Integrable (fun ω => htEstimator ω.1.2 ω.2 - tau0)
        (experimentLaw (covLaw n d) (gaussianCompletion hd m) π.val) :=
      hmem.integrable (by norm_num)
    convert hc.add (integrable_const tau0) using 1
    · rfl
    · ext ω
      exact (sub_add_cancel _ _).symm
  unfold experimentLaw at hint ⊢
  rw [Measure.integral_compProd hint]
  have hinner := (Measure.integrable_compProd_iff hint.aestronglyMeasurable).mp hint
  have hi : Integrable (fun ω : Covariates n d × Sched n =>
      ∫ z, htEstimator ω.2 z ∂π.val ω.1) (covLaw n d ⊗ₘ gaussianCompletion hd m) := by
    exact hinner.2.mono' (hf.stronglyMeasurable.integral_kernel_prod_right'
      (κ := π.val.comap Prod.fst measurable_fst)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun _ => norm_integral_le_integral_norm _))
  change (∫ ω : Covariates n d × Sched n, ∫ z, htEstimator ω.2 z ∂π.val ω.1
    ∂(covLaw n d ⊗ₘ gaussianCompletion hd m)) = tau0
  rw [Measure.integral_compProd hi]
  calc
    _ = ∫ x : Covariates n d, (n : ℝ)⁻¹ * ∑ i, tauFn hd (x i) ∂covLaw n d := by
      apply integral_congr_ae
      filter_upwards [hfair] with x hx
      exact ht_gaussian_kernel_mean hd m x (π.val x) hx
    _ = tau0 := tauFn_sampleMean_mean hn hd

/-- Fair outcome-independent assignment is conditionally unbiased and, for any centered
square-integrable prognosis, its Gaussian actual HT excess above 4.01 equals the expected
prognostic imbalance loss. This uses [the hContraction_of_gate hypothesis](hyp:hContraction_of_gate), [the hn hypothesis](hyp:hn), [the hd hypothesis](hyp:hd), [the hfair hypothesis](hyp:hfair), [the hindep hypothesis](hyp:hindep), [the stated conclusion](goal). -/
lemma ht_transfer_centeredL2 (hContraction_of_gate : ClassicalRademacherContraction)
    (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d) (m : CenteredL2Fn d)
    (π : Design n d) (hfair : FairKernel π.val) (hindep : OutcomeIndependentKernel π.val) :
    (∀ᵐ x ∂covLaw n d, ∀ y : Sched n,
      (∫ z, htEstimator y z ∂π.val x) = finiteATE y ∧
      (n : ℝ) * variance (htEstimator y) (π.val x) =
        (4 / (n : ℝ)) * ∑ i, ∑ j, prognosis y i * assignCov π x i j * prognosis y j) ∧
    gaussianTheta (n := n) (lt_of_lt_of_le (Nat.zero_lt_succ 1) hd) m = tau0 ∧ Vstar = 4.01 ∧
    loss π m.val < ⊤ ∧
    (n : ℝ) * variance (fun ω => htEstimator ω.1.2 ω.2)
      (experimentLaw (covLaw n d)
        (gaussianCompletion (lt_of_lt_of_le (Nat.zero_lt_succ 1) hd) m) π.val) - Vstar =
        (loss π m.val).toReal := by
  refine ⟨ht_conditional_transfer (lt_of_lt_of_le (Nat.zero_lt_succ 1) hn) π hfair, ?_⟩
  refine ⟨?_, ?_, loss_lt_top_of_memLp π m, ?_⟩
  · exact gaussianTheta_eq_tau0 (by omega) _ m
  · norm_num [Vstar, delta]
  · let hd0 : 0 < d := lt_of_lt_of_le (Nat.zero_lt_succ 1) hd
    have hn0 : 0 < n := lt_of_lt_of_le (Nat.zero_lt_succ 1) hn
    letI : IsMarkovKernel π.val := π.property
    letI := gaussianCompletion_markov (n := n) hd0 m
    letI : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      ⟨by simp [Real.volume_Icc]⟩
    letI : IsProbabilityMeasure (cubeMeasure d) := by unfold cubeMeasure; infer_instance
    letI : IsProbabilityMeasure (covLaw n d) := by unfold covLaw; infer_instance
    have hf : Measurable (fun ω : (Covariates n d × Sched n) × Signs n =>
        htEstimator ω.1.2 ω.2) := by fun_prop
    rw [variance_eq_integral hf.aemeasurable, ht_gaussian_joint_mean hn0 hd0 m π hfair]
    have hint := ht_gaussian_joint_centered_square_integrable hd0 m π hfair
    unfold experimentLaw at hint ⊢
    rw [Measure.integral_compProd hint]
    have hi : Integrable (fun ω : Covariates n d × Sched n =>
        ∫ z, (htEstimator ω.2 z - tau0) ^ 2 ∂π.val ω.1)
        (covLaw n d ⊗ₘ gaussianCompletion hd0 m) := by
      simpa only [Kernel.comap_apply, Real.norm_eq_abs, abs_sq] using
        ((Measure.integrable_compProd_iff hint.aestronglyMeasurable).mp hint).2
    change (n : ℝ) * (∫ ω : Covariates n d × Sched n,
      ∫ z, (htEstimator ω.2 z - tau0) ^ 2 ∂π.val ω.1
        ∂(covLaw n d ⊗ₘ gaussianCompletion hd0 m)) - Vstar = _
    rw [Measure.integral_compProd hi, ht_gaussian_outer_centered_second_moment hn0 hd0 m π hfair]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
    unfold Vstar
    field_simp
    <;> ring

-- @node: lem:ht-transfer
/-- Fair outcome-independent assignment is conditionally unbiased and, for every prognosis
in the bivariate Sobolev class, its Gaussian actual HT excess above 4.01 equals the expected
prognostic imbalance loss. This uses [the hContraction_of_gate hypothesis](hyp:hContraction_of_gate), [the hn hypothesis](hyp:hn), [the hd hypothesis](hyp:hd), [the hs hypothesis](hyp:hs), [the hs1 hypothesis](hyp:hs1), [the hm hypothesis](hyp:hm), [the hfair hypothesis](hyp:hfair), [the hindep hypothesis](hyp:hindep), [the stated conclusion](goal). -/
lemma ht_transfer (hContraction_of_gate : ClassicalRademacherContraction)
    (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d) (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1)
    (m : CenteredL2Fn d) (hm : SobolevClass d s m)
    (π : Design n d) (hfair : FairKernel π.val) (hindep : OutcomeIndependentKernel π.val) :
    (∀ᵐ x ∂covLaw n d, ∀ y : Sched n,
      (∫ z, htEstimator y z ∂π.val x) = finiteATE y ∧
      (n : ℝ) * variance (htEstimator y) (π.val x) =
        (4 / (n : ℝ)) * ∑ i, ∑ j, prognosis y i * assignCov π x i j * prognosis y j) ∧
    gaussianTheta (n := n) (lt_of_lt_of_le (Nat.zero_lt_succ 1) hd) m = tau0 ∧ Vstar = 4.01 ∧
    loss π m.val < ⊤ ∧
    (n : ℝ) * variance (fun ω => htEstimator ω.1.2 ω.2)
      (experimentLaw (covLaw n d)
        (gaussianCompletion (lt_of_lt_of_le (Nat.zero_lt_succ 1) hd) m) π.val) - Vstar =
        (loss π m.val).toReal := by
  exact ht_transfer_centeredL2 hContraction_of_gate n d hn hd m π hfair hindep

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity

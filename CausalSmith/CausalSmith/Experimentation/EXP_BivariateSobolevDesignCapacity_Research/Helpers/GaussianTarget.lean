module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Mean of the frozen Gaussian causal completion

Uniform sinusoidal effects have mean tau0, and the independent Gaussian contrasts
have mean zero. The calculation uses the actual pre-assignment schedule.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ A full sine period has zero mean under the uniform unit interval.](goal) -/
-- @node: uniform_sine_mean_zero
lemma uniform_sine_mean_zero :
    (∫ u, Real.sin (2 * Real.pi * u) ∂volume.restrict (Icc (0 : ℝ) 1)) = 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [intervalIntegral.integral_comp_mul_left Real.sin (by positivity : 2 * Real.pi ≠ 0)]
  simp [integral_sin, Real.cos_two_pi]

/-- The bounded sinusoidal treatment effect is integrable under cube sampling. Under [the stated conditions](hyp:hd), [the asserted mathematical result follows](goal). -/
-- @node: tauFn_integrable
lemma tauFn_integrable {d : ℕ} (hd : 0 < d) :
    Integrable (tauFn hd) (cubeMeasure d) := by
  letI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  letI : IsProbabilityMeasure (cubeMeasure d) := by unfold cubeMeasure; infer_instance
  have hi : Integrable (fun u : ℝ => Real.sin (2 * Real.pi * u))
      (volume.restrict (Icc (0 : ℝ) 1)) := by
    exact (integrable_const (1 : ℝ)).mono' (by exact (by fun_prop : Measurable _).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun u => by simpa [Real.norm_eq_abs] using Real.abs_sin_le_one _))
  exact (integrable_const tau0).add ((integrable_comp_eval (μ := fun _ : Fin d => volume.restrict (Icc (0 : ℝ) 1)) (i := ⟨0, hd⟩) hi).const_mul (delta * Real.sqrt 2))

/-- [ Uniform covariates give the stipulated average treatment effect.](goal) Under [the stated conditions](hyp:hd). -/
-- @node: tauFn_mean
lemma tauFn_mean {d : ℕ} (hd : 0 < d) :
    (∫ x, tauFn hd x ∂cubeMeasure d) = tau0 := by
  letI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  letI : IsProbabilityMeasure (cubeMeasure d) := by unfold cubeMeasure; infer_instance
  have hi : Integrable (fun x : Cube d => Real.sin (2 * Real.pi * x ⟨0, hd⟩))
      (cubeMeasure d) := by
    exact (integrable_const (1 : ℝ)).mono' (by exact (by fun_prop : Measurable _).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using Real.abs_sin_le_one _))
  unfold tauFn
  rw [integral_add (integrable_const _) (hi.const_mul _), integral_const_mul]
  unfold cubeMeasure
  rw [integral_comp_eval (μ := fun _ : Fin d => volume.restrict (Icc (0 : ℝ) 1)) (i := ⟨0, hd⟩) (by fun_prop : AEStronglyMeasurable
    (fun u : ℝ => Real.sin (2 * Real.pi * u)) (volume.restrict (Icc (0 : ℝ) 1))),
    uniform_sine_mean_zero]
  simp [cubeMeasure]

/-- Both coordinates of each original-unit Gaussian noise have finite first moments. [The asserted mathematical result follows](goal). -/
-- @node: noise_coordinate_integrable
lemma noise_coordinate_integrable (n : ℕ) (i : Fin n) :
    Integrable (fun e : Sched n => (e i).1) (noiseLaw n) ∧
    Integrable (fun e : Sched n => (e i).2) (noiseLaw n) := by
  have hi : Integrable (id : ℝ → ℝ) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  exact ⟨integrable_comp_eval (hi.comp_fst (gaussianReal 0 1)), integrable_comp_eval (hi.comp_snd (gaussianReal 0 1))⟩

/-- [ Independent centered Gaussian noise gives a zero mean unit contrast.](goal) -/
-- @node: noise_contrast_mean_zero
lemma noise_contrast_mean_zero (n : ℕ) (i : Fin n) :
    (∫ e : Sched n, (e i).2 - (e i).1 ∂noiseLaw n) = 0 := by
  rw [integral_sub (noise_coordinate_integrable n i).2 (noise_coordinate_integrable n i).1]
  simp only [noiseLaw, integral_comp_eval (μ := fun _ : Fin n => (gaussianReal 0 1).prod (gaussianReal 0 1)) (i := i) (by fun_prop : AEStronglyMeasurable
    (Prod.snd : ℝ × ℝ → ℝ) ((gaussianReal 0 1).prod (gaussianReal 0 1))),
    integral_comp_eval (μ := fun _ : Fin n => (gaussianReal 0 1).prod (gaussianReal 0 1)) (i := i) (by fun_prop : AEStronglyMeasurable
    (Prod.fst : ℝ × ℝ → ℝ) ((gaussianReal 0 1).prod (gaussianReal 0 1)))]
  have hs := integral_fun_snd (μ := gaussianReal 0 1) (ν := gaussianReal 0 1) (id : ℝ → ℝ)
  have hf := integral_fun_fst (μ := gaussianReal 0 1) (ν := gaussianReal 0 1) (id : ℝ → ℝ)
  simp only [id_eq, integral_id_gaussianReal, smul_zero] at hs hf
  rw [hs, hf, sub_self]

/-- The Gaussian schedule kernel is a probability kernel. Under [the stated conditions](hyp:hd), [the asserted mathematical result follows](goal). -/
-- @node: gaussianCompletion_markov
lemma gaussianCompletion_markov {n d : ℕ} (hd : 0 < d) (m : CenteredL2Fn d) :
    IsMarkovKernel (gaussianCompletion (n := n) hd m) := by
  letI : IsProbabilityMeasure (noiseLaw n) := by unfold noiseLaw; infer_instance
  have hm : Measurable m.val := m.property.1
  constructor
  intro x
  have hmap : Measurable (completionSchedule hd m.val x) := by
    unfold completionSchedule
    fun_prop
  exact Measure.isProbabilityMeasure_map hmap.aemeasurable

/-- [ A noise envelope uniform in covariates gives integrability after Gaussian completion.](goal) Under [the stated conditions](hyp:hd,hf,hg,hbound). -/
-- @node: integrable_gaussianCompletion_of_envelope
lemma integrable_gaussianCompletion_of_envelope {n d : ℕ} (hd : 0 < d)
    (m : CenteredL2Fn d) (f : Covariates n d × Sched n → ℝ)
    (hf : Measurable f) (g : Sched n → ℝ) (hg : Integrable g (noiseLaw n))
    (hbound : ∀ x e, ‖f (x, completionSchedule hd m.val x e)‖ ≤ g e) :
    Integrable f (covLaw n d ⊗ₘ gaussianCompletion hd m) := by
  letI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  letI : IsProbabilityMeasure (cubeMeasure d) := by unfold cubeMeasure; infer_instance
  letI : IsProbabilityMeasure (covLaw n d) := by unfold covLaw; infer_instance
  letI : IsProbabilityMeasure (noiseLaw n) := by unfold noiseLaw; infer_instance
  letI := gaussianCompletion_markov (n := n) hd m
  have hm : Measurable m.val := m.property.1
  have hmap (x : Covariates n d) : Measurable (completionSchedule hd m.val x) := by
    unfold completionSchedule
    fun_prop
  have hint (x : Covariates n d) : Integrable (fun y => f (x, y))
      (gaussianCompletion hd m x) := by
    change Integrable (fun y => f (x, y)) ((noiseLaw n).map (completionSchedule hd m.val x))
    apply (integrable_map_measure (hf.comp measurable_prodMk_left).aestronglyMeasurable
      (hmap x).aemeasurable).mpr
    exact hg.mono' ((hf.comp (measurable_const.prodMk (hmap x))).aestronglyMeasurable)
      (Filter.Eventually.of_forall (hbound x))
  apply (Measure.integrable_compProd_iff hf.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall hint, ?_⟩
  apply (integrable_const (∫ e, g e ∂noiseLaw n)).mono'
    (hf.stronglyMeasurable.norm.integral_kernel_prod_right'.aestronglyMeasurable)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  change (∫ y, ‖f (x, y)‖ ∂(noiseLaw n).map (completionSchedule hd m.val x)) ≤ _
  rw [integral_map (f := fun y => ‖f (x, y)‖) (hmap x).aemeasurable
    (show AEStronglyMeasurable (fun y => ‖f (x, y)‖) _ from
      (hf.comp measurable_prodMk_left).norm.aestronglyMeasurable)]
  exact integral_mono ((integrable_map_measure
    (hf.comp measurable_prodMk_left).norm.aestronglyMeasurable (hmap x).aemeasurable).mp
    (hint x).norm) hg (hbound x)

/-- [ The finite-population contrast cancels the prognostic function pointwise.](goal) Under [the stated conditions](hyp:hd). -/
-- @node: finiteATE_completionSchedule
lemma finiteATE_completionSchedule {n d : ℕ} (hd : 0 < d) (m : Cube d → ℝ)
    (x : Covariates n d) (e : Sched n) :
    finiteATE (completionSchedule hd m x e) =
      (n : ℝ)⁻¹ * ∑ i, (tauFn hd (x i) + ((e i).2 - (e i).1)) := by
  unfold finiteATE completionSchedule
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- [ The actual pre-assignment finite-population target is integrable.](goal) Under [the stated conditions](hyp:hd). -/
-- @node: finiteATE_gaussian_integrable
lemma finiteATE_gaussian_integrable {n d : ℕ} (hd : 0 < d) (m : CenteredL2Fn d) :
    Integrable (fun ω : Covariates n d × Sched n => finiteATE ω.2)
      (covLaw n d ⊗ₘ gaussianCompletion hd m) := by
  letI : IsProbabilityMeasure (noiseLaw n) := by unfold noiseLaw; infer_instance
  let K := |tau0| + |delta * Real.sqrt 2|
  have ht (x : Cube d) : ‖tauFn hd x‖ ≤ K := by
    unfold tauFn K
    calc
      ‖tau0 + delta * Real.sqrt 2 * Real.sin (2 * Real.pi * x ⟨0, hd⟩)‖ ≤
          |tau0| + |delta * Real.sqrt 2| * |Real.sin (2 * Real.pi * x ⟨0, hd⟩)| := by
            simpa [Real.norm_eq_abs, abs_mul] using norm_add_le tau0
              (delta * Real.sqrt 2 * Real.sin (2 * Real.pi * x ⟨0, hd⟩))
      _ ≤ _ := by nlinarith [Real.abs_sin_le_one (2 * Real.pi * x ⟨0, hd⟩),
        abs_nonneg (delta * Real.sqrt 2)]
  let g := fun e : Sched n => (n : ℝ)⁻¹ * ∑ i, (K + ‖(e i).2 - (e i).1‖)
  have hg : Integrable g (noiseLaw n) := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro i hi
    exact (integrable_const K).add
      (((noise_coordinate_integrable n i).2.sub (noise_coordinate_integrable n i).1).norm)
  apply integrable_gaussianCompletion_of_envelope hd m _ (by unfold finiteATE; fun_prop) g hg
  intro x e
  rw [finiteATE_completionSchedule, norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)⁻¹)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi =>
    (norm_add_le _ _).trans (add_le_add (ht (x i)) le_rfl)))

/-- [ Averaging the frozen Gaussian schedule gives the specified target tau0.](goal) Under [the stated conditions](hyp:hn,hd). -/
-- @node: gaussianTheta_eq_tau0
lemma gaussianTheta_eq_tau0 {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (m : CenteredL2Fn d) : gaussianTheta (n := n) hd m = tau0 := by
  letI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  letI : IsProbabilityMeasure (cubeMeasure d) := by unfold cubeMeasure; infer_instance
  letI : IsProbabilityMeasure (covLaw n d) := by unfold covLaw; infer_instance
  letI : IsProbabilityMeasure (noiseLaw n) := by unfold noiseLaw; infer_instance
  letI := gaussianCompletion_markov (n := n) hd m
  have hm : Measurable m.val := m.property.1
  have hmap (x : Covariates n d) : Measurable (completionSchedule hd m.val x) := by
    unfold completionSchedule
    fun_prop
  have hinner (x : Covariates n d) :
      (∫ y, finiteATE y ∂gaussianCompletion hd m x) = (n : ℝ)⁻¹ * ∑ i, tauFn hd (x i) := by
    change (∫ y, finiteATE y ∂(noiseLaw n).map (completionSchedule hd m.val x)) = _
    rw [integral_map (hmap x).aemeasurable (by unfold finiteATE; fun_prop)]
    simp_rw [finiteATE_completionSchedule]
    rw [integral_const_mul, integral_finsetSum Finset.univ (f := fun (i : Fin n) (e : Sched n) => tauFn hd (x i) + ((e i).2 - (e i).1)) (fun i _ =>
      (integrable_const _).add
        ((noise_coordinate_integrable n i).2.sub (noise_coordinate_integrable n i).1))]
    simp_rw [integral_add (f := fun _ => tauFn hd (x _)) (g := fun e : Sched n => (e _).2 - (e _).1) (integrable_const _)
      ((noise_coordinate_integrable n _).2.sub (noise_coordinate_integrable n _).1),
      noise_contrast_mean_zero]
    simp
  unfold gaussianTheta
  rw [Measure.integral_compProd (finiteATE_gaussian_integrable hd m)]
  simp_rw [hinner]
  rw [integral_const_mul]
  unfold covLaw
  rw [integral_finsetSum Finset.univ (f := fun (i : Fin n) (x : Covariates n d) => tauFn hd (x i)) (fun i _ =>
    integrable_comp_eval (μ := fun _ : Fin n => cubeMeasure d) (i := i) (tauFn_integrable hd))]
  have heval (i : Fin n) :
      (∫ x : Covariates n d, tauFn hd (x i) ∂Measure.pi (fun _ : Fin n => cubeMeasure d)) = tau0 := by
    rw [integral_comp_eval (μ := fun _ : Fin n => cubeMeasure d) (i := i)
      (tauFn_integrable hd).aestronglyMeasurable, tauFn_mean]
  simp_rw [heval]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity

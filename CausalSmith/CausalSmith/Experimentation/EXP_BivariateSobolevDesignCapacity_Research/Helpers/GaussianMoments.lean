module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.GaussianTarget
public import Mathlib.Probability.Moments.Variance

/-! # Treatment-effect and selected-noise moments

The sinusoidal treatment effect has variance delta squared. Independent original units
give the sample-mean variance, and selected Gaussian errors have zero mean and variance
four over n for every fixed assignment. These are the moment steps of HT transfer.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ The squared sine integrates to one half over a full uniform period.](goal) -/
-- @node: uniform_sine_second_moment
lemma uniform_sine_second_moment :
    (∫ u, Real.sin (2 * Real.pi * u) ^ 2
      ∂volume.restrict (Icc (0 : ℝ) 1)) = 1 / 2 := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [intervalIntegral.integral_comp_mul_left (fun u => Real.sin u ^ 2)
    (by positivity : 2 * Real.pi ≠ 0)]
  simp only [mul_zero, mul_one, integral_sin_sq, Real.sin_zero, Real.sin_two_pi,
    zero_mul, sub_zero]
  simp only [smul_eq_mul]
  field_simp [Real.pi_ne_zero]
  ring

/-- The treatment effect is square integrable by its uniform bound. Under [the stated conditions](hyp:hd), [the asserted mathematical result follows](goal). -/
-- @node: tauFn_memLp
lemma tauFn_memLp {d : ℕ} (hd : 0 < d) : MemLp (tauFn hd) 2 (cubeMeasure d) := by
  let : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  let : IsProbabilityMeasure (cubeMeasure d) := by unfold cubeMeasure; infer_instance
  have hs : MemLp (fun x : Cube d => Real.sin (2 * Real.pi * x ⟨0, hd⟩))
      2 (cubeMeasure d) := by
    apply (memLp_const (1 : ℝ)).mono ((by fun_prop : Measurable _).aestronglyMeasurable)
    filter_upwards with x
    simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (2 * Real.pi * x ⟨0, hd⟩)
  exact (memLp_const tau0).add (hs.const_mul (delta * Real.sqrt 2))

/-- [ The frozen treatment-effect variance is delta squared.](goal) Under [the stated conditions](hyp:hd). -/
-- @node: tauFn_variance
lemma tauFn_variance {d : ℕ} (hd : 0 < d) :
    variance (tauFn hd) (cubeMeasure d) = delta ^ 2 := by
  let : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  let : IsProbabilityMeasure (cubeMeasure d) := by unfold cubeMeasure; infer_instance
  rw [variance_eq_integral (tauFn_memLp hd).aemeasurable,
    tauFn_mean hd]
  have hcenter (x : Cube d) : (tauFn hd x - tau0) ^ 2 =
      delta ^ 2 * 2 * Real.sin (2 * Real.pi * x ⟨0, hd⟩) ^ 2 := by
    unfold tauFn
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simp_rw [hcenter]
  rw [integral_const_mul]
  unfold cubeMeasure
  rw [integral_comp_eval (μ := fun _ : Fin d => volume.restrict (Icc (0 : ℝ) 1))
    (i := ⟨0, hd⟩) (by fun_prop : AEStronglyMeasurable
      (fun u : ℝ => Real.sin (2 * Real.pi * u) ^ 2)
      (volume.restrict (Icc (0 : ℝ) 1))), uniform_sine_second_moment]
  ring

/-- [ Independence of the original covariates gives the sample-average effect variance.](goal) Under [the stated conditions](hyp:hd). -/
-- @node: tauFn_sampleMean_variance
lemma tauFn_sampleMean_variance {n d : ℕ} (hd : 0 < d) :
    variance (fun x : Covariates n d => (n : ℝ)⁻¹ * ∑ i, tauFn hd (x i))
      (covLaw n d) = delta ^ 2 / n := by
  let : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  let : IsProbabilityMeasure (cubeMeasure d) := by unfold cubeMeasure; infer_instance
  rw [variance_const_mul]
  have hsum := variance_sum_pi (μ := fun _ : Fin n => cubeMeasure d)
    (X := fun _ => tauFn hd) (fun _ => tauFn_memLp hd)
  have hfun : (∑ i : Fin n, fun x : Covariates n d => tauFn hd (x i)) =
      (fun x => ∑ i, tauFn hd (x i)) := by
    ext x
    simp
  rw [hfun] at hsum
  unfold covLaw
  rw [hsum]
  simp only [tauFn_variance, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  by_cases hn : (n : ℝ) = 0
  · simp [hn]
  · field_simp

/-- A fixed selected unit error has a finite second moment. [The asserted mathematical result follows](goal). -/
-- @node: signed_selected_unit_noise_memLp
lemma signed_selected_unit_noise_memLp (b : Bool) :
    MemLp (fun e : ℝ × ℝ => sgn b * (if b then e.2 else e.1)) 2
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have h : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1) := memLp_id_gaussianReal 2
  cases b
  · simpa [sgn] using (h.comp_fst (gaussianReal 0 1)).const_mul (-1)
  · simpa [sgn] using h.comp_snd (gaussianReal 0 1)

/-- [ Each selected standard Gaussian error is centered for either treatment sign.](goal) -/
-- @node: signed_selected_unit_noise_mean
lemma signed_selected_unit_noise_mean (b : Bool) :
    (∫ e : ℝ × ℝ, sgn b * (if b then e.2 else e.1)
      ∂(gaussianReal 0 1).prod (gaussianReal 0 1)) = 0 := by
  have hf := integral_fun_fst (μ := gaussianReal 0 1) (ν := gaussianReal 0 1) (id : ℝ → ℝ)
  have hs := integral_fun_snd (μ := gaussianReal 0 1) (ν := gaussianReal 0 1) (id : ℝ → ℝ)
  simp only [id_eq, integral_id_gaussianReal, smul_zero] at hf hs
  cases b <;> simp [sgn, integral_neg, hf, hs]

/-- [ Selection and the treatment sign preserve the unit noise variance.](goal) -/
-- @node: signed_selected_unit_noise_variance
lemma signed_selected_unit_noise_variance (b : Bool) :
    variance (fun e : ℝ × ℝ => sgn b * (if b then e.2 else e.1))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) = 1 := by
  have hf : variance (Prod.fst : ℝ × ℝ → ℝ)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) = 1 := by
    simpa using (measurePreserving_fst (μ := gaussianReal 0 1)
      (ν := gaussianReal 0 1)).variance_fun_comp (f := id) (by fun_prop)
  have hs : variance (Prod.snd : ℝ × ℝ → ℝ)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) = 1 := by
    simpa using (measurePreserving_snd (μ := gaussianReal 0 1)
      (ν := gaussianReal 0 1)).variance_fun_comp (f := id) (by fun_prop)
  cases b <;> simp [sgn, variance_fun_neg, hf, hs]

/-- [ The selected-noise contribution is centered for every fixed original assignment.](goal) -/
-- @node: selected_noise_mean
lemma selected_noise_mean {n : ℕ} (z : Signs n) :
    (∫ e : Sched n, (2 / (n : ℝ)) *
      ∑ i, sgn (z i) * (if z i then (e i).2 else (e i).1) ∂noiseLaw n) = 0 := by
  rw [integral_const_mul]
  have hint (i : Fin n) : Integrable (fun e : Sched n =>
      sgn (z i) * (if z i then (e i).2 else (e i).1)) (noiseLaw n) :=
    integrable_comp_eval (μ := fun _ : Fin n => (gaussianReal 0 1).prod (gaussianReal 0 1))
      (i := i) ((signed_selected_unit_noise_memLp (z i)).integrable (by norm_num))
  rw [integral_finsetSum _ (fun i _ => hint i)]
  have hi (i : Fin n) :
      (∫ e : Sched n, sgn (z i) * (if z i then (e i).2 else (e i).1)
        ∂noiseLaw n) = 0 := by
    unfold noiseLaw
    rw [integral_comp_eval (μ := fun _ : Fin n => (gaussianReal 0 1).prod (gaussianReal 0 1))
      (i := i) (signed_selected_unit_noise_memLp (z i)).aestronglyMeasurable]
    exact signed_selected_unit_noise_mean (z i)
  change (2 / (n : ℝ)) * ∑ i, (∫ e : Sched n,
    sgn (z i) * (if z i then (e i).2 else (e i).1) ∂noiseLaw n) = 0
  simp only [hi, Finset.sum_const_zero, mul_zero]

/-- [ Independent unit errors yield exactly four over n selected-noise variance.](goal) -/
-- @node: selected_noise_variance
lemma selected_noise_variance {n : ℕ} (z : Signs n) :
    variance (fun e : Sched n => (2 / (n : ℝ)) *
      ∑ i, sgn (z i) * (if z i then (e i).2 else (e i).1))
      (noiseLaw n) = 4 / n := by
  rw [variance_const_mul]
  have hsum := variance_sum_pi
    (μ := fun _ : Fin n => (gaussianReal 0 1).prod (gaussianReal 0 1))
    (X := fun i e => sgn (z i) * (if z i then e.2 else e.1))
    (fun i => signed_selected_unit_noise_memLp (z i))
  have hfun : (∑ i : Fin n, fun e : Sched n =>
      sgn (z i) * (if z i then (e i).2 else (e i).1)) =
      (fun e => ∑ i, sgn (z i) * (if z i then (e i).2 else (e i).1)) := by
    ext e
    simp
  rw [hfun] at hsum
  unfold noiseLaw
  rw [hsum]
  simp only [signed_selected_unit_noise_variance, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  by_cases hn : (n : ℝ) = 0
  · simp [hn]
  · field_simp
    norm_num

/-- [ The entire selected-noise contribution has a finite second moment.](goal) -/
-- @node: selected_noise_memLp
lemma selected_noise_memLp {n : ℕ} (z : Signs n) :
    MemLp (fun e : Sched n => (2 / (n : ℝ)) *
      ∑ i, sgn (z i) * (if z i then (e i).2 else (e i).1)) 2 (noiseLaw n) := by
  have hi (i : Fin n) : MemLp (fun e : Sched n =>
      sgn (z i) * (if z i then (e i).2 else (e i).1)) 2 (noiseLaw n) :=
    (signed_selected_unit_noise_memLp (z i)).comp_measurePreserving
      (measurePreserving_eval
        (fun _ : Fin n => (gaussianReal 0 1).prod (gaussianReal 0 1)) i)
  exact (memLp_finsetSum Finset.univ (fun i _ => hi i)).const_mul _

/-- [ Centering turns the selected-noise variance into its exact second moment.](goal) -/
-- @node: selected_noise_second_moment
lemma selected_noise_second_moment {n : ℕ} (z : Signs n) :
    (∫ e : Sched n, ((2 / (n : ℝ)) *
      ∑ i, sgn (z i) * (if z i then (e i).2 else (e i).1)) ^ 2 ∂noiseLaw n) =
        4 / (n : ℝ) := by
  have h := selected_noise_variance z
  rw [variance_eq_integral (selected_noise_memLp z).aemeasurable,
    selected_noise_mean z] at h
  simpa only [sub_zero] using h

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity

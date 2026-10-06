module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.CitedGates
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.GaussianMoments
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Probability.Moments.Variance

/-! # Conditional Gaussian HT moments

The actual HT statistic decomposes into treatment effects, prognostic imbalance,
and selected Gaussian noise. Fair full-schedule and Gaussian conditional moments
supply the pointwise identities used in the joint-experiment variance calculation.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ Actual Gaussian HT excess for a fixed prognostic function. -/
def gaussianExcessReal {n d : ℕ} (hd : 0 < d) (π : Design n d)
    (m : CenteredL2Fn d) : ℝ :=
  (n : ℝ) * variance (fun ω => htEstimator ω.1.2 ω.2)
    (experimentLaw (covLaw n d) (gaussianCompletion hd m) π.val) - Vstar
/-- Fixed-function Gaussian actual HT worst excess. -/
def gaussianWorst {n d : ℕ} (hd : 0 < d) (π : Design n d) (s : ℝ) : ℝ≥0∞ :=
  ⨆ m : {m : CenteredL2Fn d // SobolevClass d s m},
    ENNReal.ofReal (gaussianExcessReal hd π m.val)
/-- Minimax Gaussian actual HT excess, with the fixed-function supremum outside sampling. -/
def gaussianCapacity (n d : ℕ) (hd : 0 < d) (s : ℝ) : ℝ≥0∞ :=
  Causalean.Stat.minimaxValueENNReal
    (fun (π : {π : Design n d // DesignClass n d π})
      (m : {m : CenteredL2Fn d // SobolevClass d s m}) =>
      ENNReal.ofReal (gaussianExcessReal hd π.val m.val))

/-- The actual HT estimator splits into the realized target and signed midpoints.](goal) This uses [the stated conclusion](goal). -/
-- @node: htEstimator_midpoint_decomposition
lemma htEstimator_midpoint_decomposition {n : ℕ} (y : Sched n) (z : Signs n) :
    htEstimator y z = finiteATE y +
      (2 / (n : ℝ)) * ∑ i, sgn (z i) * prognosis y i := by
  have hunit (i : Fin n) :
      2 * (sgn (z i) * (if z i then (y i).2 else (y i).1)) =
        ((y i).2 - (y i).1) + 2 * (sgn (z i) * prognosis y i) := by
    cases z i <;> simp [sgn, prognosis] <;> ring
  unfold htEstimator finiteATE
  calc
    (2 / (n : ℝ)) * ∑ i, sgn (z i) * (if z i then (y i).2 else (y i).1) =
        (n : ℝ)⁻¹ * ∑ i, 2 * (sgn (z i) *
          (if z i then (y i).2 else (y i).1)) := by
            rw [← Finset.mul_sum]
            ring
    _ = (n : ℝ)⁻¹ * ∑ i, (((y i).2 - (y i).1) +
          2 * (sgn (z i) * prognosis y i)) := by simp_rw [hunit]
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]; ring

/-- Substituting the causal completion gives the sample-average treatment effect,
prognostic imbalance, and selected Gaussian-noise contribution in the roadmap. Under [the stated conditions](hyp:hd), [the asserted mathematical result follows](goal). -/
-- @node: htEstimator_completion_decomposition
lemma htEstimator_completion_decomposition {n d : ℕ} (hd : 0 < d)
    (m : Cube d → ℝ) (x : Covariates n d) (e : Sched n) (z : Signs n) :
    htEstimator (completionSchedule hd m x e) z =
      (n : ℝ)⁻¹ * ∑ i, tauFn hd (x i) +
      (2 / (n : ℝ)) * ∑ i, sgn (z i) * m (x i) +
      (2 / (n : ℝ)) * ∑ i, sgn (z i) * (if z i then (e i).2 else (e i).1) := by
  have hunit (i : Fin n) :
      2 * (sgn (z i) * (if z i then (completionSchedule hd m x e i).2
        else (completionSchedule hd m x e i).1)) =
      tauFn hd (x i) + 2 * (sgn (z i) * m (x i)) +
        2 * (sgn (z i) * (if z i then (e i).2 else (e i).1)) := by
    cases z i <;> simp [sgn, completionSchedule] <;> ring
  unfold htEstimator
  calc
    (2 / (n : ℝ)) * ∑ i, sgn (z i) *
        (if z i then (completionSchedule hd m x e i).2
          else (completionSchedule hd m x e i).1) =
      (n : ℝ)⁻¹ * ∑ i, 2 * (sgn (z i) *
        (if z i then (completionSchedule hd m x e i).2
          else (completionSchedule hd m x e i).1)) := by
            rw [← Finset.mul_sum]
            ring
    _ = _ := by
      simp_rw [hunit]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
      ring

/-- [ Under a fair finite sign law the signed midpoint sum has expectation zero.](goal) Under [the stated conditions](hyp:hfair). -/
-- @node: midpoint_sum_mean_zero
lemma midpoint_sum_mean_zero {n : ℕ} (μ : Measure (Signs n)) [IsProbabilityMeasure μ]
    (hfair : ∀ i, ∫ z, sgn (z i) ∂μ = 0) (y : Sched n) :
    (∫ z, ∑ i, sgn (z i) * prognosis y i ∂μ) = 0 := by
  rw [integral_finsetSum _ (fun i _ => Integrable.of_finite)]
  simp_rw [integral_mul_const, hfair, zero_mul]
  simp

/-- [ Fairness gives fixed-schedule HT unbiasedness for an arbitrary dependent sign law.](goal) Under [the stated conditions](hyp:hfair). -/
-- @node: htEstimator_integral_of_fair
lemma htEstimator_integral_of_fair {n : ℕ} (μ : Measure (Signs n))
    [IsProbabilityMeasure μ] (hfair : ∀ i, ∫ z, sgn (z i) ∂μ = 0) (y : Sched n) :
    (∫ z, htEstimator y z ∂μ) = finiteATE y := by
  simp_rw [htEstimator_midpoint_decomposition]
  rw [integral_add (integrable_const _) (Integrable.of_finite), integral_const,
    integral_const_mul, midpoint_sum_mean_zero μ hfair y]
  simp

/-- Expanding the signed midpoint square yields the full double covariance sum. [The asserted mathematical result follows](goal). -/
-- @node: midpoint_sum_second_moment
lemma midpoint_sum_second_moment {n : ℕ} (μ : Measure (Signs n))
    [IsProbabilityMeasure μ] (y : Sched n) :
    (∫ z, (∑ i, sgn (z i) * prognosis y i) ^ 2 ∂μ) =
      ∑ i, ∑ j, prognosis y i * (∫ z, sgn (z i) * sgn (z j) ∂μ) * prognosis y j := by
  have hexpand (z : Signs n) : (∑ i, sgn (z i) * prognosis y i) ^ 2 =
      ∑ i, ∑ j, prognosis y i * (sgn (z i) * sgn (z j)) * prognosis y j := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [hexpand]
  rw [integral_finsetSum _ (fun i _ => Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j _ => Integrable.of_finite)]
  simp_rw [integral_mul_const, integral_const_mul]

/-- The exact fixed-schedule HT covariance identity uses fairness but no independence
between the assignment coordinates. Under [the stated conditions](hyp:hn,hfair), [the asserted mathematical result follows](goal). -/
-- @node: htEstimator_variance_of_fair
lemma htEstimator_variance_of_fair {n d : ℕ} (hn : 0 < n) (π : Design n d)
    (x : Covariates n d) (hfair : ∀ i, ∫ z, sgn (z i) ∂π.val x = 0)
    (y : Sched n) :
    (n : ℝ) * variance (htEstimator y) (π.val x) =
      (4 / (n : ℝ)) * ∑ i, ∑ j, prognosis y i * assignCov π x i j * prognosis y j := by
  let : IsMarkovKernel π.val := π.property
  have hmeas : Measurable (htEstimator y) := by fun_prop
  rw [variance_eq_integral hmeas.aemeasurable, htEstimator_integral_of_fair _ hfair y]
  have hcenter (z : Signs n) : (htEstimator y z - finiteATE y) ^ 2 =
      (2 / (n : ℝ)) ^ 2 * (∑ i, sgn (z i) * prognosis y i) ^ 2 := by
    rw [htEstimator_midpoint_decomposition]
    ring
  simp_rw [hcenter]
  rw [integral_const_mul, midpoint_sum_second_moment]
  simp only [assignCov, hfair, zero_mul, sub_zero]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

/-- [ Conditional on any realized schedule, a fair original-sample design is unbiased
and has the exact midpoint covariance quadratic form.](goal) Under [the stated conditions](hyp:hn,hfair). -/
-- @node: ht_conditional_transfer
lemma ht_conditional_transfer {n d : ℕ} (hn : 0 < n) (π : Design n d)
    (hfair : FairKernel π.val) :
    ∀ᵐ x ∂covLaw n d, ∀ y : Sched n,
      (∫ z, htEstimator y z ∂π.val x) = finiteATE y ∧
      (n : ℝ) * variance (htEstimator y) (π.val x) =
        (4 / (n : ℝ)) * ∑ i, ∑ j, prognosis y i * assignCov π x i j * prognosis y j := by
  let : IsMarkovKernel π.val := π.property
  filter_upwards [hfair] with x hx
  intro y
  exact ⟨htEstimator_integral_of_fair (π.val x) hx y,
    htEstimator_variance_of_fair hn π x hx y⟩

/-- Cauchy–Schwarz bounds every signed sum by the sum of the unitwise squares. [The asserted mathematical result follows](goal). -/
-- @node: signed_sum_sq_le
lemma signed_sum_sq_le {n : ℕ} (z : Signs n) (u : Fin n → ℝ) :
    (∑ i, sgn (z i) * u i) ^ 2 ≤ (n : ℝ) * ∑ i, (u i) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ) (f := fun i => sgn (z i) * u i)
  have hs (i : Fin n) : (sgn (z i) * u i) ^ 2 = (u i) ^ 2 := by
    cases z i <;> simp [sgn]
  simpa only [hs, Finset.card_univ, Fintype.card_fin] using h

/-- [ Square-integrable prognosis has finite imbalance loss for every Markov design.
The bound is uniform over all sign laws and does not require fairness.](goal) -/
-- @node: loss_lt_top_of_memLp
lemma loss_lt_top_of_memLp {n d : ℕ} (π : Design n d) (m : CenteredL2Fn d) :
    loss π m.val < ⊤ := by
  let : IsMarkovKernel π.val := π.property
  let : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  let : IsProbabilityMeasure (cubeMeasure d) := by unfold cubeMeasure; infer_instance
  have hi (i : Fin n) : Integrable (fun x : Covariates n d => m.val (x i) ^ 2)
      (covLaw n d) :=
    (m.property.2.1.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => cubeMeasure d) i)).integrable_sq
  have hb : Integrable (fun x : Covariates n d =>
      (n : ℝ) * ∑ i, m.val (x i) ^ 2) (covLaw n d) :=
    (integrable_finsetSum Finset.univ (fun i _ => hi i)).const_mul _
  have hfinite : (∫⁻ x : Covariates n d,
      ENNReal.ofReal ((n : ℝ) * ∑ i, m.val (x i) ^ 2) ∂covLaw n d) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
      (fun x => by positivity))).mp hb.2
  unfold loss
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  apply lt_of_le_of_lt _ hfinite
  apply lintegral_mono
  intro x
  calc
    (∫⁻ z, ENNReal.ofReal ((∑ i, sgn (z i) * m.val (x i)) ^ 2) ∂π.val x) ≤
        ∫⁻ _z, ENNReal.ofReal ((n : ℝ) * ∑ i, m.val (x i) ^ 2) ∂π.val x :=
      lintegral_mono (fun z => ENNReal.ofReal_le_ofReal (signed_sum_sq_le z _))
    _ = _ := by simp

/-- For a fixed covariate array and assignment, the completed HT statistic has
finite second moment over the pre-assignment Gaussian noise. Under [the stated conditions](hyp:hd), [the asserted mathematical result follows](goal). -/
-- @node: ht_completion_noise_memLp
lemma ht_completion_noise_memLp {n d : ℕ} (hd : 0 < d)
    (m : Cube d → ℝ) (x : Covariates n d) (z : Signs n) :
    MemLp (fun e => htEstimator (completionSchedule hd m x e) z) 2 (noiseLaw n) := by
  letI : IsProbabilityMeasure (noiseLaw n) := by unfold noiseLaw; infer_instance
  simp_rw [htEstimator_completion_decomposition]
  exact (memLp_const ((n : ℝ)⁻¹ * ∑ i, tauFn hd (x i) +
    (2 / (n : ℝ)) * ∑ i, sgn (z i) * m (x i))).add (selected_noise_memLp z)

/-- [ Averaging the actual completed HT statistic over noise leaves precisely the
sample treatment effect and the signed prognostic imbalance.](goal) Under [the stated conditions](hyp:hd). -/
-- @node: ht_completion_noise_mean
lemma ht_completion_noise_mean {n d : ℕ} (hd : 0 < d)
    (m : Cube d → ℝ) (x : Covariates n d) (z : Signs n) :
    (∫ e, htEstimator (completionSchedule hd m x e) z ∂noiseLaw n) =
      (n : ℝ)⁻¹ * ∑ i, tauFn hd (x i) +
        (2 / (n : ℝ)) * ∑ i, sgn (z i) * m (x i) := by
  letI : IsProbabilityMeasure (noiseLaw n) := by unfold noiseLaw; infer_instance
  simp_rw [htEstimator_completion_decomposition]
  rw [integral_add (integrable_const _) ((selected_noise_memLp z).integrable (by norm_num)),
    integral_const, selected_noise_mean]
  simp

/-- [ Conditional on the original covariates and signs, the only remaining variance
of the completed HT statistic is the selected-noise variance, four over n.](goal) Under [the stated conditions](hyp:hd). -/
-- @node: ht_completion_noise_variance
lemma ht_completion_noise_variance {n d : ℕ} (hd : 0 < d)
    (m : Cube d → ℝ) (x : Covariates n d) (z : Signs n) :
    variance (fun e => htEstimator (completionSchedule hd m x e) z)
      (noiseLaw n) = 4 / (n : ℝ) := by
  letI : IsProbabilityMeasure (noiseLaw n) := by unfold noiseLaw; infer_instance
  simp_rw [htEstimator_completion_decomposition]
  rw [variance_const_add (selected_noise_memLp z).aestronglyMeasurable,
    selected_noise_variance]

/-- [ Centering by any deterministic target, the conditional Gaussian second moment
is the squared conditional bias plus four over n. This directly removes both
noise cross terms in the HT roadmap.](goal) Under [the stated conditions](hyp:hd). -/
-- @node: ht_completion_noise_centered_second_moment
lemma ht_completion_noise_centered_second_moment {n d : ℕ} (hd : 0 < d)
    (m : Cube d → ℝ) (x : Covariates n d) (z : Signs n) (c : ℝ) :
    (∫ e, (htEstimator (completionSchedule hd m x e) z - c) ^ 2 ∂noiseLaw n) =
      ((n : ℝ)⁻¹ * ∑ i, tauFn hd (x i) +
        (2 / (n : ℝ)) * ∑ i, sgn (z i) * m (x i) - c) ^ 2 + 4 / (n : ℝ) := by
  letI : IsProbabilityMeasure (noiseLaw n) := by unfold noiseLaw; infer_instance
  let A := (n : ℝ)⁻¹ * ∑ i, tauFn hd (x i) +
    (2 / (n : ℝ)) * ∑ i, sgn (z i) * m (x i) - c
  let U := fun e : Sched n => (2 / (n : ℝ)) *
    ∑ i, sgn (z i) * (if z i then (e i).2 else (e i).1)
  have hU : MemLp U 2 (noiseLaw n) := selected_noise_memLp z
  have hexpand (e : Sched n) :
      (htEstimator (completionSchedule hd m x e) z - c) ^ 2 =
        A ^ 2 + 2 * A * U e + (U e) ^ 2 := by
    rw [htEstimator_completion_decomposition]
    dsimp [A, U]
    ring
  simp_rw [hexpand]
  have hlin : Integrable (fun e => 2 * A * U e) (noiseLaw n) :=
    (hU.integrable (by norm_num)).const_mul (2 * A)
  have hadd : Integrable (fun e => A ^ 2 + 2 * A * U e) (noiseLaw n) :=
    (integrable_const (A ^ 2)).add hlin
  rw [integral_add hadd hU.integrable_sq,
    integral_add (integrable_const (A ^ 2)) hlin,
    integral_const, integral_const_mul]
  change _ + 2 * A * (∫ e, U e ∂noiseLaw n) +
    (∫ e, (U e) ^ 2 ∂noiseLaw n) = _
  rw [show (∫ e, U e ∂noiseLaw n) = 0 from selected_noise_mean z,
    show (∫ e, (U e) ^ 2 ∂noiseLaw n) = 4 / (n : ℝ) from selected_noise_second_moment z]
  simp [A]

/-- [ Fair assignment removes the covariance between any fixed covariate statistic
and its signed prognostic imbalance. No independence between signs is needed.](goal) Under [the stated conditions](hyp:hfair). -/
-- @node: signed_prognosis_mean_zero
lemma signed_prognosis_mean_zero {n : ℕ} (μ : Measure (Signs n))
    [IsProbabilityMeasure μ] (hfair : ∀ i, ∫ z, sgn (z i) ∂μ = 0)
    (u : Fin n → ℝ) : (∫ z, ∑ i, sgn (z i) * u i ∂μ) = 0 := by
  rw [integral_finsetSum _ (fun i _ => Integrable.of_finite)]
  simp_rw [integral_mul_const, hfair, zero_mul]
  simp

/-- [ Integrating the conditional noise second moment against a fair assignment
law leaves the treatment-effect square, the imbalance square, and four over n.](goal) Under [the stated conditions](hyp:hd,hfair). -/
-- @node: ht_completion_fair_centered_second_moment
lemma ht_completion_fair_centered_second_moment {n d : ℕ} (hd : 0 < d)
    (m : Cube d → ℝ) (x : Covariates n d) (μ : Measure (Signs n))
    [IsProbabilityMeasure μ] (hfair : ∀ i, ∫ z, sgn (z i) ∂μ = 0) (c : ℝ) :
    (∫ z, ∫ e, (htEstimator (completionSchedule hd m x e) z - c) ^ 2
      ∂noiseLaw n ∂μ) =
      ((n : ℝ)⁻¹ * ∑ i, tauFn hd (x i) - c) ^ 2 +
        (2 / (n : ℝ)) ^ 2 * (∫ z, (∑ i, sgn (z i) * m (x i)) ^ 2 ∂μ) +
        4 / (n : ℝ) := by
  simp_rw [ht_completion_noise_centered_second_moment]
  let A := (n : ℝ)⁻¹ * ∑ i, tauFn hd (x i) - c
  let S := fun z : Signs n => ∑ i, sgn (z i) * m (x i)
  have hexpand (z : Signs n) :
      ((n : ℝ)⁻¹ * ∑ i, tauFn hd (x i) +
        (2 / (n : ℝ)) * S z - c) ^ 2 + 4 / (n : ℝ) =
      (A ^ 2 + (2 * A * (2 / (n : ℝ))) * S z +
        (2 / (n : ℝ)) ^ 2 * (S z) ^ 2) + 4 / (n : ℝ) := by
    dsimp [A]
    ring
  change (∫ z, ((n : ℝ)⁻¹ * ∑ i, tauFn hd (x i) +
    (2 / (n : ℝ)) * S z - c) ^ 2 + 4 / (n : ℝ) ∂μ) = _
  simp_rw [hexpand]
  rw [integral_add Integrable.of_finite (integrable_const _),
    integral_add Integrable.of_finite Integrable.of_finite,
    integral_add (integrable_const _) Integrable.of_finite,
    integral_const, integral_const, integral_const_mul, integral_const_mul,
    show (∫ z, S z ∂μ) = 0 from signed_prognosis_mean_zero μ hfair _]
  simp [A, S]

/-- [ The actual HT statistic is Borel in the full schedule for each fixed assignment. This uses [the stated conclusion](goal). -/
-- @node: htEstimator_schedule_measurable
@[fun_prop] lemma htEstimator_schedule_measurable {n : ℕ} (z : Signs n) :
    Measurable (fun y : Sched n => htEstimator y z) := by
  unfold htEstimator
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro i _
  cases hz : z i <;> simp only [hz, Bool.false_eq_true, if_false, if_true]
  all_goals fun_prop

/-- A finite assignment space permits exchanging assignment and noise integrals
once each fixed-assignment noise statistic is integrable.](goal) Under [the stated conditions](hyp:hf). This uses [the stated conclusion](goal). -/
-- @node: finite_sign_integral_swap
lemma finite_sign_integral_swap {n : ℕ} {E : Type*} [MeasurableSpace E]
    (ν : Measure E) (μ : Measure (Signs n)) [IsFiniteMeasure μ]
    (f : E → Signs n → ℝ) (hf : ∀ z, Integrable (fun e => f e z) ν) :
    (∫ e, ∫ z, f e z ∂μ ∂ν) = ∫ z, ∫ e, f e z ∂ν ∂μ := by
  simp_rw [integral_fintype (Integrable.of_finite (μ := μ))]
  have hterm (z : Signs n) : Integrable (fun e => μ.real {z} • f e z) ν :=
    (hf z).smul (μ.real {z})
  rw [integral_finsetSum _ (fun z _ => hterm z)]
  simp_rw [integral_smul]

/-- [ For a realized original sample, integrating the actual pre-assignment schedule
kernel and then any fair assignment kernel gives the sample treatment-effect mean.](goal) Under [the stated conditions](hyp:hd,hfair). -/
-- @node: ht_gaussian_kernel_mean
lemma ht_gaussian_kernel_mean {n d : ℕ} (hd : 0 < d)
    (m : CenteredL2Fn d) (x : Covariates n d) (μ : Measure (Signs n))
    [IsProbabilityMeasure μ] (hfair : ∀ i, ∫ z, sgn (z i) ∂μ = 0) :
    (∫ y, ∫ z, htEstimator y z ∂μ ∂gaussianCompletion hd m x) =
      (n : ℝ)⁻¹ * ∑ i, tauFn hd (x i) := by
  letI : IsProbabilityMeasure (noiseLaw n) := by unfold noiseLaw; infer_instance
  change (∫ y, ∫ z, htEstimator y z ∂μ
    ∂(noiseLaw n).map (completionSchedule hd m.val x)) = _
  have hcompletion : Measurable (completionSchedule hd m.val x) := by
    unfold completionSchedule tauFn
    fun_prop
  have hinner : AEStronglyMeasurable (fun y : Sched n => ∫ z, htEstimator y z ∂μ)
      ((noiseLaw n).map (completionSchedule hd m.val x)) := by
    simp_rw [integral_fintype (Integrable.of_finite (μ := μ))]
    apply Measurable.aestronglyMeasurable
    apply Finset.measurable_sum
    intro z _
    fun_prop
  rw [integral_map hcompletion.aemeasurable hinner]
  rw [finite_sign_integral_swap (noiseLaw n) μ _ (fun z =>
    (ht_completion_noise_memLp hd m.val x z).integrable (by norm_num))]
  simp_rw [ht_completion_noise_mean]
  rw [integral_add (integrable_const _) Integrable.of_finite,
    integral_const, integral_const_mul, signed_prognosis_mean_zero μ hfair]
  simp

/-- [ The conditional full-schedule Gaussian kernel has the exact centered second
moment used by the HT transfer, with no hidden conditional moment assumption.](goal) Under [the stated conditions](hyp:hd,hfair). -/
-- @node: ht_gaussian_kernel_centered_second_moment
lemma ht_gaussian_kernel_centered_second_moment {n d : ℕ} (hd : 0 < d)
    (m : CenteredL2Fn d) (x : Covariates n d) (μ : Measure (Signs n))
    [IsProbabilityMeasure μ] (hfair : ∀ i, ∫ z, sgn (z i) ∂μ = 0) (c : ℝ) :
    (∫ y, ∫ z, (htEstimator y z - c) ^ 2 ∂μ ∂gaussianCompletion hd m x) =
      ((n : ℝ)⁻¹ * ∑ i, tauFn hd (x i) - c) ^ 2 +
        (2 / (n : ℝ)) ^ 2 * (∫ z, (∑ i, sgn (z i) * m.val (x i)) ^ 2 ∂μ) +
        4 / (n : ℝ) := by
  letI : IsProbabilityMeasure (noiseLaw n) := by unfold noiseLaw; infer_instance
  change (∫ y, ∫ z, (htEstimator y z - c) ^ 2 ∂μ
    ∂(noiseLaw n).map (completionSchedule hd m.val x)) = _
  have hcompletion : Measurable (completionSchedule hd m.val x) := by
    unfold completionSchedule tauFn
    fun_prop
  have hinner : AEStronglyMeasurable (fun y : Sched n =>
      ∫ z, (htEstimator y z - c) ^ 2 ∂μ)
      ((noiseLaw n).map (completionSchedule hd m.val x)) := by
    simp_rw [integral_fintype (Integrable.of_finite (μ := μ))]
    apply Measurable.aestronglyMeasurable
    apply Finset.measurable_sum
    intro z _
    fun_prop
  rw [integral_map hcompletion.aemeasurable hinner]
  have hint (z : Signs n) : Integrable
      (fun e => (htEstimator (completionSchedule hd m.val x e) z - c) ^ 2)
      (noiseLaw n) :=
    ((ht_completion_noise_memLp hd m.val x z).sub (memLp_const c)).integrable_sq
  rw [finite_sign_integral_swap (noiseLaw n) μ _ hint]
  exact ht_completion_fair_centered_second_moment hd m.val x μ hfair c

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity

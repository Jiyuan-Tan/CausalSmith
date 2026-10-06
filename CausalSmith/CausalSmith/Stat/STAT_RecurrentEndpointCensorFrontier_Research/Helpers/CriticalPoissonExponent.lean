module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalPoissonTaylor
public import Causalean.Stat.CLT.Martingale.ProbabilityBounds

/-!
# Critical Poisson exponent convergence

The intensity integral of the compensated Poisson exponential kernel in
roadmap (19) splits into the relative quadratic energy and its genuine Taylor
remainder. Its convergence in probability is established here independently
of the still-needed conditional characteristic-function identity.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The intensity integral of the compensated exponential kernel, before
identification with a conditional characteristic function. -/
-- @node: criticalPoissonExponent
noncomputable def criticalPoissonExponent (c : ClassConstants) (P : SubjectLaw)
    (n : ℕ) (s : Fin n → ObsHistory) (u : ℝ) : ℂ :=
  ∑ a : Arm, ∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - bandwidth c n),
    (Complex.exp (Complex.I * (u * criticalSignedRecurrenceWeight c P a s i t : ℝ)) -
      1 - Complex.I * (u * criticalSignedRecurrenceWeight c P a s i t : ℝ)) *
      (P.lam a t : ℂ)

/-- Complex integrability of the Taylor remainder follows from the proved
intensity-weighted norm budget and the construction's measurable weights. -/
-- @node: critical_poisson_complex_remainder_intervalIntegrable
lemma critical_poisson_complex_remainder_intervalIntegrable (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) {n : ℕ} (hn : 3 ≤ n)
    (a : Arm) (s : Fin n → ObsHistory) (i : Fin n) (u : ℝ) :
    IntervalIntegrable (fun t =>
      Causalean.Stat.expQuadraticRemainder (u * criticalSignedRecurrenceWeight c P a s i t) *
        (P.lam a t : ℂ)) volume 0 (1 - bandwidth c n) := by
  have hlam := poissonRecurrence_intervalIntegrable P hP.poissonRecurrence a
  have hh := bandwidth_pos_and_le_cap c (show 0 < n by omega)
  have hT : 0 ≤ 1 - bandwidth c n := by linarith [hh.2, c.x0_le]
  have hl : IntervalIntegrable (P.lam a) volume 0 (1 - bandwidth c n) :=
    hlam.mono_set (by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), uIcc_of_le hT]
      exact Icc_subset_Icc le_rfl (by linarith [hh.1]))
  have hm := hl.def'.aestronglyMeasurable
  have hw := measurable_recurrenceSubjectWeight c (bandwidth c n) a s i
  apply (IntervalIntegrable.intervalIntegrable_norm_iff (by
    unfold Causalean.Stat.expQuadraticRemainder criticalSignedRecurrenceWeight
    fun_prop)).mp
  have hb := critical_poisson_taylor_intervalIntegrable c P hP hn a s i u
  apply hb.congr_ae
  all_goals
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [uIoc_of_le hT] at ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [ht.1, ht.2, hh.1]
    have hp : 0 ≤ P.lam a t := c.lambdaMin_pos.le.trans (hP.recurrenceBounds a t ht').1
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]

/-- The actual compensated exponential intensity integral has exactly the
quadratic variance term and the already controlled complex remainder. -/
-- @node: critical_poisson_exponent_eq
lemma critical_poisson_exponent_eq (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) {n : ℕ} (hn : 3 ≤ n) (s : Fin n → ObsHistory) (u : ℝ) :
    criticalPoissonExponent c P n s u =
      -((u ^ 2 / 2 *
        (((n : ℝ) * criticalPredictableEnergy c P n s / Real.log n) /
          criticalVariance c P) : ℝ) : ℂ) + criticalPoissonTaylorRemainder c P n s u := by
  have hterm : ∀ a : Arm, ∀ i : Fin n,
      (∫ t in (0 : ℝ)..(1 - bandwidth c n),
        (Complex.exp (Complex.I * (u * criticalSignedRecurrenceWeight c P a s i t : ℝ)) -
          1 - Complex.I * (u * criticalSignedRecurrenceWeight c P a s i t : ℝ)) *
          (P.lam a t : ℂ)) =
      (∫ t in (0 : ℝ)..(1 - bandwidth c n),
        Causalean.Stat.expQuadraticRemainder (u * criticalSignedRecurrenceWeight c P a s i t) *
          (P.lam a t : ℂ)) -
      (u ^ 2 / 2 : ℝ) * (∫ t in (0 : ℝ)..(1 - bandwidth c n),
        criticalSignedRecurrenceWeight c P a s i t ^ 2 * P.lam a t : ℝ) := by
    intro a i
    have he := criticalSignedRecurrenceWeight_energy_intervalIntegrable c P hP hn a s i
    have hc : IntervalIntegrable (fun t =>
        (criticalSignedRecurrenceWeight c P a s i t ^ 2 * P.lam a t : ℝ) : ℝ → ℂ)
        volume 0 (1 - bandwidth c n) := ⟨he.1.ofReal, he.2.ofReal⟩
    calc
      _ = ∫ t in (0 : ℝ)..(1 - bandwidth c n),
          Causalean.Stat.expQuadraticRemainder (u * criticalSignedRecurrenceWeight c P a s i t) *
            (P.lam a t : ℂ) - (u ^ 2 / 2 : ℝ) *
              (criticalSignedRecurrenceWeight c P a s i t ^ 2 * P.lam a t : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t _
        unfold Causalean.Stat.expQuadraticRemainder
        push_cast
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub
          (critical_poisson_complex_remainder_intervalIntegrable c P hP hn a s i u)
          (hc.const_mul _), intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
  unfold criticalPoissonExponent criticalPoissonTaylorRemainder
  simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Complex.ofReal_sum]
  rw [critical_signed_recurrence_energy_eq c P hP hn s]
  push_cast
  ring

/-- The distance of the Poisson exponent from the standard Gaussian exponent
is bounded by relative variance error and the genuine remainder. -/
-- @node: critical_poisson_exponent_error_le
lemma critical_poisson_exponent_error_le (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) {n : ℕ} (hn : 3 ≤ n) (s : Fin n → ObsHistory) (u : ℝ) :
    ‖criticalPoissonExponent c P n s u - (-((u ^ 2 / 2 : ℝ) : ℂ))‖ ≤
      u ^ 2 / 2 * |((n : ℝ) * criticalPredictableEnergy c P n s / Real.log n) /
        criticalVariance c P - 1| + ‖criticalPoissonTaylorRemainder c P n s u‖ := by
  rw [critical_poisson_exponent_eq c P hP hn s u]
  have he : -((u ^ 2 / 2 *
        (((n : ℝ) * criticalPredictableEnergy c P n s / Real.log n) /
          criticalVariance c P) : ℝ) : ℂ) + criticalPoissonTaylorRemainder c P n s u -
      (-((u ^ 2 / 2 : ℝ) : ℂ)) =
      (-((u ^ 2 / 2 *
        (((n : ℝ) * criticalPredictableEnergy c P n s / Real.log n) /
          criticalVariance c P - 1) : ℝ) : ℂ)) +
        criticalPoissonTaylorRemainder c P n s u := by push_cast; ring
  rw [he]
  apply (norm_add_le _ _).trans_eq
  simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (show 0 ≤ u ^ 2 / 2 by positivity)]

/-- The compensated exponential kernel is integrable on the actual cutoff
horizon by its exact quadratic-plus-remainder decomposition. -/
-- @node: critical_poisson_kernel_intervalIntegrable
lemma critical_poisson_kernel_intervalIntegrable (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) {n : ℕ} (hn : 3 ≤ n)
    (a : Arm) (s : Fin n → ObsHistory) (i : Fin n) (u : ℝ) :
    IntervalIntegrable (fun t =>
      (Complex.exp (Complex.I * (u * criticalSignedRecurrenceWeight c P a s i t : ℝ)) -
        1 - Complex.I * (u * criticalSignedRecurrenceWeight c P a s i t : ℝ)) *
        (P.lam a t : ℂ)) volume 0 (1 - bandwidth c n) := by
  have he := criticalSignedRecurrenceWeight_energy_intervalIntegrable c P hP hn a s i
  have hc : IntervalIntegrable (fun t =>
      (criticalSignedRecurrenceWeight c P a s i t ^ 2 * P.lam a t : ℝ) : ℝ → ℂ)
      volume 0 (1 - bandwidth c n) := ⟨he.1.ofReal, he.2.ofReal⟩
  convert (critical_poisson_complex_remainder_intervalIntegrable c P hP hn a s i u).sub
    (hc.const_mul ((u ^ 2 / 2 : ℝ) : ℂ)) using 1
  funext t
  unfold Causalean.Stat.expQuadraticRemainder
  push_cast
  ring

/-- The intensity integral is measurable in the observed sample. The
model's almost-everywhere measurable intensity is replaced by its measurable
version only inside the time integral. -/
-- @node: measurable_criticalPoissonExponent
@[fun_prop] lemma measurable_criticalPoissonExponent (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) {n : ℕ} (hn : 3 ≤ n) (u : ℝ) :
    Measurable (fun s : Fin n → ObsHistory => criticalPoissonExponent c P n s u) := by
  have hh := bandwidth_pos_and_le_cap c (show 0 < n by omega)
  have hT : 0 ≤ 1 - bandwidth c n := by linarith [hh.2, c.x0_le]
  unfold criticalPoissonExponent
  apply Finset.measurable_sum
  intro a _
  apply Finset.measurable_sum
  intro i _
  let hm := (hP.poissonRecurrence a).1
  let g := hm.mk (P.lam a)
  have hg : Measurable g := hm.measurable_mk
  have hj : Measurable (fun p : (Fin n → ObsHistory) × ℝ =>
      (Complex.exp (Complex.I * (u * criticalSignedRecurrenceWeight c P a p.1 i p.2 : ℝ)) -
        1 - Complex.I * (u * criticalSignedRecurrenceWeight c P a p.1 i p.2 : ℝ)) *
        (g p.2 : ℂ)) := by
    unfold criticalSignedRecurrenceWeight
    fun_prop
  have hi : Measurable (fun s : Fin n → ObsHistory =>
      ∫ t in Ioc (0 : ℝ) (1 - bandwidth c n),
        (Complex.exp (Complex.I * (u * criticalSignedRecurrenceWeight c P a s i t : ℝ)) -
          1 - Complex.I * (u * criticalSignedRecurrenceWeight c P a s i t : ℝ)) *
          (g t : ℂ)) := hj.stronglyMeasurable.integral_prod_right.measurable
  convert hi using 1
  funext s
  rw [intervalIntegral.integral_of_le hT]
  apply integral_congr_ae
  have ha := ae_restrict_of_ae_restrict_of_subset
    (show Ioc (0 : ℝ) (1 - bandwidth c n) ⊆ Ioc 0 1 from
      Ioc_subset_Ioc le_rfl (by linarith [hh.1])) hm.ae_eq_mk
  filter_upwards [ha] with t ht
  rw [ht]

/-- The real part of the compensated Poisson kernel is nonpositive for
nonnegative intensities; compensation changes only the imaginary part. -/
-- @node: critical_poisson_kernel_re_nonpos
lemma critical_poisson_kernel_re_nonpos (x r : ℝ) (hr : 0 ≤ r) :
    ((Complex.exp (Complex.I * (x : ℂ)) - 1 - Complex.I * (x : ℂ)) *
      (r : ℂ)).re ≤ 0 := by
  simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero,
    sub_zero, one_mul]
  rw [Complex.exp_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
    one_mul, zero_add, Real.exp_zero, one_mul]
  exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (Real.cos_le_one x)) hr

/-- The genuine intensity integral has nonpositive real part on the cutoff
horizon, so its exponential has the modulus bound needed to take expectations. -/
-- @node: critical_poisson_exponent_re_nonpos
lemma critical_poisson_exponent_re_nonpos (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) {n : ℕ} (hn : 3 ≤ n) (s : Fin n → ObsHistory) (u : ℝ) :
    (criticalPoissonExponent c P n s u).re ≤ 0 := by
  have hh := bandwidth_pos_and_le_cap c (show 0 < n by omega)
  have hT : 0 ≤ 1 - bandwidth c n := by linarith [hh.2, c.x0_le]
  unfold criticalPoissonExponent
  simp only [Complex.re_sum]
  apply Finset.sum_nonpos
  intro a _
  apply Finset.sum_nonpos
  intro i _
  rw [intervalIntegral.integral_of_le hT]
  have hi := (critical_poisson_kernel_intervalIntegrable c P hP hn a s i u).1
  have hre := integral_re hi
  simp only [RCLike.re_to_complex] at hre
  rw [← hre]
  apply integral_nonpos_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  apply critical_poisson_kernel_re_nonpos
  exact c.lambdaMin_pos.le.trans (hP.recurrenceBounds a t
    ⟨ht.1.le, ht.2.trans (by linarith [hh.1])⟩).1

/-- The exponential of the conditional intensity integral is bounded by one,
without restricting to the empirical risk event. -/
-- @node: critical_poisson_exponential_norm_le_one
lemma critical_poisson_exponential_norm_le_one (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) {n : ℕ} (hn : 3 ≤ n) (s : Fin n → ObsHistory) (u : ℝ) :
    ‖Complex.exp (criticalPoissonExponent c P n s u)‖ ≤ 1 := by
  rw [Complex.norm_exp]
  exact (Real.exp_le_exp.mpr (critical_poisson_exponent_re_nonpos c P hP hn s u)).trans_eq
    Real.exp_zero

/-- Roadmap (19)'s exponent converges in probability along changing model
laws, using the variance limit (15) and small-jump Taylor estimate (18). -/
-- @node: critical_poisson_exponent_triangular_tendsto
lemma critical_poisson_exponent_triangular_tendsto
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (u : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (sampleLaw (Pseq n) n).real
      {s | ε < ‖criticalPoissonExponent c (Pseq n) n s u -
        (-((u ^ 2 / 2 : ℝ) : ℂ))‖}) atTop (nhds 0) := by
  let δ := ε / (2 * (u ^ 2 / 2 + 1))
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hb : u ^ 2 / 2 * δ ≤ ε / 2 := by
    have hp : 0 < 2 * (u ^ 2 / 2 + 1) := by positivity
    have he : δ * (2 * (u ^ 2 / 2 + 1)) = ε := by
      dsimp [δ]; field_simp
    nlinarith [sq_nonneg u]
  have hv := critical_predictable_relative_variance_triangular_tendsto_zero c hk Pseq hP hd
  have hr := critical_poisson_taylor_remainder_triangular_tendsto_zero c hk Pseq hP u
    (half_pos hε)
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa using hv.add hr)
  filter_upwards [eventually_ge_atTop 3] with n hn
  let : IsProbabilityMeasure (Pseq n).latent := ⟨(Pseq n).prob⟩
  let : IsProbabilityMeasure (observedLaw (Pseq n)) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw (Pseq n) n) := by unfold sampleLaw; infer_instance
  apply (measureReal_mono (s₂ :=
    {s | δ < |((n : ℝ) * criticalPredictableEnergy c (Pseq n) n s / Real.log n) /
      criticalVariance c (Pseq n) - 1|} ∪
    {s | ε / 2 < ‖criticalPoissonTaylorRemainder c (Pseq n) n s u‖})
    ?_ (by finiteness)).trans (measureReal_union_le _ _)
  intro s hs
  by_contra h
  have hh := not_or.mp h
  have hv' : |((n : ℝ) * criticalPredictableEnergy c (Pseq n) n s / Real.log n) /
      criticalVariance c (Pseq n) - 1| ≤ δ := le_of_not_gt hh.1
  have hr' : ‖criticalPoissonTaylorRemainder c (Pseq n) n s u‖ ≤ ε / 2 :=
    le_of_not_gt hh.2
  have he := critical_poisson_exponent_error_le c (Pseq n) (hP n) hn s u
  have hvb := mul_le_mul_of_nonneg_left hv' (show 0 ≤ u ^ 2 / 2 by positivity)
  have : ‖criticalPoissonExponent c (Pseq n) n s u -
      (-((u ^ 2 / 2 : ℝ) : ℂ))‖ ≤ ε := by linarith
  exact not_lt_of_ge this hs

/-- Exponentiating the genuine intensity integral gives the probability
limit on the right of (19). Identifying this random variable with the
conditional recurrence characteristic function is a separate obligation. -/
-- @node: critical_poisson_exponential_triangular_tendsto
lemma critical_poisson_exponential_triangular_tendsto
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (u : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (sampleLaw (Pseq n) n).real
      {s | ε < ‖Complex.exp (criticalPoissonExponent c (Pseq n) n s u) -
        Complex.exp (-((u ^ 2 / 2 : ℝ) : ℂ))‖}) atTop (nhds 0) := by
  have hc : ContinuousAt Complex.exp (-((u ^ 2 / 2 : ℝ) : ℂ)) := by fun_prop
  obtain ⟨δ, hd, hb⟩ := Metric.continuousAt_iff.mp hc ε hε
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (critical_poisson_exponent_triangular_tendsto c hk Pseq hP u (half_pos hd))
  apply Eventually.of_forall
  intro n
  let : IsProbabilityMeasure (Pseq n).latent := ⟨(Pseq n).prob⟩
  let : IsProbabilityMeasure (observedLaw (Pseq n)) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw (Pseq n) n) := by unfold sampleLaw; infer_instance
  apply measureReal_mono _ (by finiteness)
  intro s hs
  by_contra h
  have he : ‖criticalPoissonExponent c (Pseq n) n s u -
      (-((u ^ 2 / 2 : ℝ) : ℂ))‖ ≤ δ / 2 := le_of_not_gt h
  have he' : dist (criticalPoissonExponent c (Pseq n) n s u)
      (-((u ^ 2 / 2 : ℝ) : ℂ)) < δ := by rw [dist_eq_norm]; linarith
  have hx := hb he'
  rw [dist_eq_norm] at hx
  exact (not_lt_of_ge hx.le) hs

/-- Measurability and the unconditional unit modulus bound give
integrability under the genuine sample law. -/
-- @node: critical_poisson_exponential_integrable
lemma critical_poisson_exponential_integrable (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) {n : ℕ} (hn : 3 ≤ n) (u : ℝ) :
    Integrable (fun s => Complex.exp (criticalPoissonExponent c P n s u))
      (sampleLaw P n) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  apply Integrable.of_bound (by fun_prop) 1
  exact Eventually.of_forall (fun s =>
    critical_poisson_exponential_norm_le_one c P hP hn s u)

/-- Boundedness upgrades the genuine exponential probability limit to
convergence of its expected norm error, as required when taking expectations
in roadmap (19). No conditional characteristic-function identity is assumed. -/
-- @node: critical_poisson_exponential_mean_norm_tendsto
lemma critical_poisson_exponential_mean_norm_tendsto
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (u : ℝ) :
    Tendsto (fun n => ∫ s,
      ‖Complex.exp (criticalPoissonExponent c (Pseq n) n s u) -
        Complex.exp (-((u ^ 2 / 2 : ℝ) : ℂ))‖ ∂sampleLaw (Pseq n) n)
      atTop (nhds 0) := by
  let μ := fun n => sampleLaw (Pseq n) n
  let z : ℂ := Complex.exp (-((u ^ 2 / 2 : ℝ) : ℂ))
  let Y : (n : ℕ) → (Fin n → ObsHistory) → ℝ := fun n s =>
    if 3 ≤ n then ‖Complex.exp (criticalPoissonExponent c (Pseq n) n s u) - z‖ else 0
  haveI : ∀ n, IsProbabilityMeasure (μ n) := fun n => by
    let : IsProbabilityMeasure (Pseq n).latent := ⟨(Pseq n).prob⟩
    let : IsProbabilityMeasure (observedLaw (Pseq n)) :=
      Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
    dsimp [μ]; unfold sampleLaw; infer_instance
  have hz : ‖z‖ ≤ 1 := by
    dsimp [z]
    rw [Complex.norm_exp]
    simp only [Complex.neg_re, Complex.ofReal_re]
    exact (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg u])).trans_eq Real.exp_zero
  have hm : ∀ n, AEMeasurable (Y n) (μ n) := by
    intro n
    by_cases hn : 3 ≤ n
    · simp only [Y, if_pos hn]
      exact (((Complex.measurable_exp.comp
        (measurable_criticalPoissonExponent c (Pseq n) (hP n) hn u)).sub
          measurable_const).norm).aemeasurable
    · simpa only [Y, if_neg hn] using (measurable_const (a := (0 : ℝ))).aemeasurable
  have hb : ∀ n, ∀ᵐ s ∂μ n, |Y n s - 0| ≤ 2 := by
    intro n
    apply Eventually.of_forall
    intro s
    by_cases hn : 3 ≤ n
    · simp only [Y, if_pos hn, sub_zero, abs_of_nonneg (norm_nonneg _)]
      have hw := critical_poisson_exponential_norm_le_one c (Pseq n) (hP n) hn s u
      linarith [norm_sub_le (Complex.exp (criticalPoissonExponent c (Pseq n) n s u)) z]
    · simp [Y, hn]
  have hp : Causalean.Stat.Modes.TendstoInProbability μ Y atTop (fun _ _ => 0) := by
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro ε hε
    have ht := critical_poisson_exponential_triangular_tendsto c hk Pseq hP u (half_pos hε)
    have he : Tendsto (fun n => (μ n).real {s | ε ≤ ‖Y n s - 0‖}) atTop (nhds 0) := by
      apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ ht
      filter_upwards [eventually_ge_atTop 3] with n hn
      apply measureReal_mono _ (by finiteness)
      intro s hs
      simp only [Y, if_pos hn, sub_zero, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _)] at hs
      change ε ≤ ‖Complex.exp (criticalPoissonExponent c (Pseq n) n s u) - z‖ at hs
      change ε / 2 < ‖Complex.exp (criticalPoissonExponent c (Pseq n) n s u) - z‖
      linarith
    rw [← ENNReal.tendsto_toReal_zero_iff]
    exact he
  have ht := Causalean.Stat.tendsto_integral_abs_sub_of_tendstoInProbability_of_ae_bound
    Y 0 2 hm (by norm_num) hb hp
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 3] with n hn
  apply integral_congr_ae
  exact Eventually.of_forall (fun s => by
    simp only [Y, if_pos hn, sub_zero, abs_of_nonneg (norm_nonneg _)]; rfl)

/-- Taking expectations in the actual intensity exponential gives the
standard Gaussian characteristic-function value. Identification with the
recurrence contrast characteristic function remains a separate step. -/
-- @node: critical_poisson_exponential_expectation_tendsto
lemma critical_poisson_exponential_expectation_tendsto
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (u : ℝ) :
    Tendsto (fun n => ∫ s, Complex.exp (criticalPoissonExponent c (Pseq n) n s u)
      ∂sampleLaw (Pseq n) n) atTop
      (nhds (Complex.exp (-((u ^ 2 / 2 : ℝ) : ℂ)))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
    (critical_poisson_exponential_mean_norm_tendsto c hk Pseq hP u)
  filter_upwards [eventually_ge_atTop 3] with n hn
  let : IsProbabilityMeasure (Pseq n).latent := ⟨(Pseq n).prob⟩
  let : IsProbabilityMeasure (observedLaw (Pseq n)) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw (Pseq n) n) := by unfold sampleLaw; infer_instance
  have hi := critical_poisson_exponential_integrable c (Pseq n) (hP n) hn u
  have hc := integrable_const (Complex.exp (-((u ^ 2 / 2 : ℝ) : ℂ)))
    (μ := sampleLaw (Pseq n) n)
  have he := integral_sub hi hc
  simp only [integral_const, probReal_univ, one_smul] at he
  rw [← he]
  exact norm_integral_le_integral_norm _

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

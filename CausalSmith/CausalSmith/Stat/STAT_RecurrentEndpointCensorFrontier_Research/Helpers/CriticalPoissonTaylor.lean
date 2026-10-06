module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalEmpiricalRisk
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalRelativeVariance
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalSmallJumps
public import Causalean.Stat.CLT.Martingale.ExponentialBounds

/-!
# Critical conditional Poisson Taylor budget

For roadmap (19), the signed, standardized subject recurrence coefficients
have a quadratic exponential remainder bounded by their energy times the
small-jump envelope. Integrating against the genuine recurrence intensity
preserves this bound. The conditional Poisson exponential identity itself is
separate from these deterministic Taylor estimates.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The signed subject coefficient in the standardized recurrence contrast (17). -/
-- @node: criticalSignedRecurrenceWeight
noncomputable def criticalSignedRecurrenceWeight (c : ClassConstants) (P : SubjectLaw)
    {n : ℕ} (a : Arm) (s : Fin n → ObsHistory) (i : Fin n) (t : ℝ) : ℝ :=
  (if a then 1 else -1) *
    (Real.sqrt ((n : ℝ) / Real.log n) / Real.sqrt (criticalVariance c P) *
      recurrenceSubjectWeight c (bandwidth c n) a s i t)

/-- Treatment signs preserve the normalized coefficient's absolute value. -/
-- @node: criticalSignedRecurrenceWeight_abs
lemma criticalSignedRecurrenceWeight_abs (c : ClassConstants) (P : SubjectLaw)
    {n : ℕ} (a : Arm) (s : Fin n → ObsHistory) (i : Fin n) (t : ℝ) :
    |criticalSignedRecurrenceWeight c P a s i t| =
      |Real.sqrt ((n : ℝ) / Real.log n) / Real.sqrt (criticalVariance c P) *
        recurrenceSubjectWeight c (bandwidth c n) a s i t| := by
  cases a <;> simp [criticalSignedRecurrenceWeight]

/-- A small signed coefficient gives the cubic remainder bound, with the
quadratic energy left intact for integration against the Poisson intensity. -/
-- @node: critical_poisson_taylor_pointwise_le
lemma critical_poisson_taylor_pointwise_le (u x δ : ℝ)
    (hx : |x| ≤ δ) (hu : |u| * δ ≤ 1) :
    ‖Causalean.Stat.expQuadraticRemainder (u * x)‖ ≤ |u| ^ 3 * δ * x ^ 2 := by
  have hux : |u * x| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hx (abs_nonneg u)).trans hu
  calc
    _ ≤ |u * x| ^ 3 := Causalean.Stat.norm_expQuadraticRemainder_le_cube _ hux
    _ = |u| ^ 3 * (|x| * x ^ 2) := by
      rw [abs_mul, mul_pow, show |x| ^ 3 = |x| * x ^ 2 by rw [pow_succ, sq_abs]; ring]
    _ ≤ |u| ^ 3 * (δ * x ^ 2) := by gcongr
    _ = _ := by ring

/-- Every signed normalized coefficient square has an integrable intensity
product on the actual cutoff horizon. -/
-- @node: criticalSignedRecurrenceWeight_energy_intervalIntegrable
lemma criticalSignedRecurrenceWeight_energy_intervalIntegrable (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) {n : ℕ} (hn : 3 ≤ n)
    (a : Arm) (s : Fin n → ObsHistory) (i : Fin n) :
    IntervalIntegrable (fun t => criticalSignedRecurrenceWeight c P a s i t ^ 2 *
      P.lam a t) volume 0 (1 - bandwidth c n) := by
  have hh := bandwidth_pos_and_le_cap c (show 0 < n by omega)
  have he := (recurrenceSubjectWeight_pow_mul_lam_intervalIntegrable c P hP a s i
    hh.1 ((by linarith [hh.2, c.x0_le])) 2).const_mul
      ((Real.sqrt ((n : ℝ) / Real.log n) / Real.sqrt (criticalVariance c P)) ^ 2)
  convert he using 1
  funext t
  cases a <;> simp [criticalSignedRecurrenceWeight] <;> ring

/-- The intensity-weighted norm remainder is integrable; bounded measurable
coefficients and the model's integrable intensity supply all regularity. -/
-- @node: critical_poisson_taylor_intervalIntegrable
lemma critical_poisson_taylor_intervalIntegrable (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) {n : ℕ} (hn : 3 ≤ n)
    (a : Arm) (s : Fin n → ObsHistory) (i : Fin n) (u : ℝ) :
    IntervalIntegrable (fun t =>
      ‖Causalean.Stat.expQuadraticRemainder (u * criticalSignedRecurrenceWeight c P a s i t)‖ *
        P.lam a t) volume 0 (1 - bandwidth c n) := by
  have hh := bandwidth_pos_and_le_cap c (show 0 < n by omega)
  have hh1 : bandwidth c n ≤ 1 := (by linarith [hh.2, c.x0_le])
  have hlam : IntervalIntegrable (P.lam a) volume 0 (1 - bandwidth c n) :=
    (poissonRecurrence_intervalIntegrable P hP.poissonRecurrence a).mono_set (by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
      Set.uIcc_of_le (by linarith : 0 ≤ 1 - bandwidth c n)]
    exact Set.Icc_subset_Icc le_rfl (by linarith))
  let B := |u| * |Real.sqrt ((n : ℝ) / Real.log n) / Real.sqrt (criticalVariance c P)| *
    weightEnvelope c
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : 0 ≤ 1 - bandwidth c n)] at hlam ⊢
  apply hlam.bdd_mul (c := 2 + B + B ^ 2 / 2)
  · have hw := measurable_recurrenceSubjectWeight c (bandwidth c n) a s i
    unfold Causalean.Stat.expQuadraticRemainder criticalSignedRecurrenceWeight
    fun_prop
  · apply Eventually.of_forall
    intro t
    have hW : 0 ≤ weightEnvelope c := by unfold weightEnvelope continuationNorm; positivity
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hx : |u * criticalSignedRecurrenceWeight c P a s i t| ≤ B := by
      rw [abs_mul, criticalSignedRecurrenceWeight_abs, abs_mul]
      simpa only [B, mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (recurrenceSubjectWeight_abs_le c hh.1 a s i t)
          (abs_nonneg (Real.sqrt ((n : ℝ) / Real.log n) / Real.sqrt (criticalVariance c P))))
        (abs_nonneg u)
    have hx2 : (u * criticalSignedRecurrenceWeight c P a s i t) ^ 2 ≤ B ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr hx
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact (Causalean.Stat.norm_expQuadraticRemainder_le_global _).trans (by linarith)

/-- The full conditional Taylor remainder budget, before taking expectation
in the exposure variables. Both arms and all subject intensities are retained. -/
-- @node: criticalPoissonTaylorBudget
noncomputable def criticalPoissonTaylorBudget (c : ClassConstants) (P : SubjectLaw)
    (n : ℕ) (s : Fin n → ObsHistory) (u : ℝ) : ℝ :=
  ∑ a : Arm, ∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - bandwidth c n),
    ‖Causalean.Stat.expQuadraticRemainder (u * criticalSignedRecurrenceWeight c P a s i t)‖ *
      P.lam a t

/-- Squared signed coefficients integrate to the relative predictable variance
in (15), with the exact logarithmic and model-dependent normalization. -/
-- @node: critical_signed_recurrence_energy_eq
lemma critical_signed_recurrence_energy_eq (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) {n : ℕ} (hn : 3 ≤ n) (s : Fin n → ObsHistory) :
    (∑ a : Arm, ∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - bandwidth c n),
      criticalSignedRecurrenceWeight c P a s i t ^ 2 * P.lam a t) =
    ((n : ℝ) * criticalPredictableEnergy c P n s / Real.log n) / criticalVariance c P := by
  have hl : 0 < Real.log (n : ℝ) := lt_of_lt_of_le (by norm_num) (one_le_log_sampleSize hn)
  have hv := criticalVariance_pos c P hP
  have hs : (Real.sqrt ((n : ℝ) / Real.log n) / Real.sqrt (criticalVariance c P)) ^ 2 =
      ((n : ℝ) / Real.log n) / criticalVariance c P := by
    rw [div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hv.le]
  calc
    _ = ∑ a : Arm, ∑ i : Fin n,
        (((n : ℝ) / Real.log n) / criticalVariance c P) *
          ∫ t in (0 : ℝ)..(1 - bandwidth c n),
            recurrenceSubjectWeight c (bandwidth c n) a s i t ^ 2 * P.lam a t := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i _
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      rw [← hs]
      cases a <;> simp [criticalSignedRecurrenceWeight] <;> ring
    _ = _ := by simp only [← Finset.mul_sum]; unfold criticalPredictableEnergy; ring

/-- Integrating the cubic Taylor bound gives maximal jump times the genuine
conditional variance, exactly the remainder estimate used in roadmap (19). -/
-- @node: critical_poisson_taylor_budget_le
lemma critical_poisson_taylor_budget_le (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) {n : ℕ} (hn : 3 ≤ n) (s : Fin n → ObsHistory)
    (u δ : ℝ) (hu : |u| * δ ≤ 1)
    (hj : ∀ a : Arm, ∀ i : Fin n, ∀ t ∈ Icc (0 : ℝ) (1 - bandwidth c n),
      |criticalSignedRecurrenceWeight c P a s i t| ≤ δ) :
    criticalPoissonTaylorBudget c P n s u ≤ |u| ^ 3 * δ *
      (((n : ℝ) * criticalPredictableEnergy c P n s / Real.log n) / criticalVariance c P) := by
  rw [← critical_signed_recurrence_energy_eq c P hP hn s]
  unfold criticalPoissonTaylorBudget
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro i _
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on
    (by linarith [(bandwidth_pos_and_le_cap c (show 0 < n by omega)).2, c.x0_le])
    (critical_poisson_taylor_intervalIntegrable c P hP hn a s i u)
    ((criticalSignedRecurrenceWeight_energy_intervalIntegrable c P hP hn a s i).const_mul _)
  intro t ht
  have hlam : 0 ≤ P.lam a t := c.lambdaMin_pos.le.trans
    (hP.recurrenceBounds a t ⟨ht.1, by
      linarith [(bandwidth_pos_and_le_cap c (show 0 < n by omega)).1, ht.2]⟩).1
  have he := mul_le_mul_of_nonneg_right
    (critical_poisson_taylor_pointwise_le u _ δ (hj a i t ht) hu) hlam
  simpa only [mul_assoc] using he

/-- The actual conditional Poisson Taylor budget tends to zero in probability
along every triangular model sequence. The proof uses the empirical risk floor,
small-jump estimate (18), and relative predictable variance (15), rather than
assuming the Gaussian limit or any characteristic-function convergence. -/
-- @node: critical_poisson_taylor_budget_triangular_tendsto_zero
lemma critical_poisson_taylor_budget_triangular_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (u : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (sampleLaw (Pseq n) n).real
      {s | ε < criticalPoissonTaylorBudget c (Pseq n) n s u}) atTop (nhds 0) := by
  let r := c.pMin * Real.exp (-c.dMax) * min c.Gint (c.gMin / 2) / 2
  have hr : 0 < r := by
    dsimp [r]
    exact div_pos (mul_pos (mul_pos c.pMin_pos (Real.exp_pos _))
      (lt_min c.Gint_pos (div_pos c.gMin_pos (by norm_num)))) (by norm_num)
  let δ := min (1 / (|u| + 1)) (ε / (2 * (|u| ^ 3 + 1)))
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hu : |u| * δ ≤ 1 := by
    have hm := min_le_left (1 / (|u| + 1)) (ε / (2 * (|u| ^ 3 + 1)))
    have hp : 0 < |u| + 1 := by positivity
    have hb : δ * (|u| + 1) ≤ 1 := (le_div_iff₀ hp).mp hm
    nlinarith
  have hεb : |u| ^ 3 * δ * 2 ≤ ε := by
    have hm := min_le_right (1 / (|u| + 1)) (ε / (2 * (|u| ^ 3 + 1)))
    have hp : 0 < 2 * (|u| ^ 3 + 1) := by positivity
    have hb : δ * (2 * (|u| ^ 3 + 1)) ≤ ε := (le_div_iff₀ hp).mp hm
    nlinarith
  let F := fun (n : ℕ) (a : Arm) => {s : Fin n → ObsHistory |
    ¬ ∀ t ∈ Icc (0 : ℝ) (1 - bandwidth c n),
      (n : ℝ) * r * (1 - t) ≤ riskSet a s t}
  let V := fun n => {s : Fin n → ObsHistory |
    1 < |((n : ℝ) * criticalPredictableEnergy c (Pseq n) n s / Real.log n) /
      criticalVariance c (Pseq n) - 1|}
  have hF0 : Tendsto (fun n => (sampleLaw (Pseq n) n).real (F n false)) atTop (nhds 0) :=
    critical_empirical_risk_linear_floor_failure_triangular_tendsto c hk Pseq hP false
  have hF1 : Tendsto (fun n => (sampleLaw (Pseq n) n).real (F n true)) atTop (nhds 0) :=
    critical_empirical_risk_linear_floor_failure_triangular_tendsto c hk Pseq hP true
  have hV : Tendsto (fun n => (sampleLaw (Pseq n) n).real (V n)) atTop (nhds 0) :=
    critical_predictable_relative_variance_triangular_tendsto_zero c hk Pseq hP (by norm_num)
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [add_zero] using (hF0.add hF1).add hV)
  filter_upwards [eventually_ge_atTop 3,
    critical_normalized_recurrence_weight_eventually_small c hk hr hd] with n hn hj
  let : IsProbabilityMeasure (Pseq n).latent := ⟨(Pseq n).prob⟩
  let : IsProbabilityMeasure (observedLaw (Pseq n)) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw (Pseq n) n) := by unfold sampleLaw; infer_instance
  have hs : {s | ε < criticalPoissonTaylorBudget c (Pseq n) n s u} ⊆
      (F n false ∪ F n true) ∪ V n := by
    intro s he
    by_contra hb
    have hb' := not_or.mp hb
    have hf := not_or.mp hb'.1
    have hfloor : ∀ a : Arm, ∀ t ∈ Icc (0 : ℝ) (1 - bandwidth c n),
        (n : ℝ) * r * (1 - t) ≤ riskSet a s t := by
      intro a
      cases a
      · exact not_not.mp hf.1
      · exact not_not.mp hf.2
    have henergy : ((n : ℝ) * criticalPredictableEnergy c (Pseq n) n s / Real.log n) /
        criticalVariance c (Pseq n) ≤ 2 := by
      have hv : |((n : ℝ) * criticalPredictableEnergy c (Pseq n) n s / Real.log n) /
          criticalVariance c (Pseq n) - 1| ≤ 1 := le_of_not_gt hb'.2
      have hv' := (abs_le.mp hv).2
      linarith
    have hbound := critical_poisson_taylor_budget_le c (Pseq n) (hP n) hn s u δ hu (by
      intro a i t ht
      rw [criticalSignedRecurrenceWeight_abs]
      exact (hj (Pseq n) (hP n) a s i t ht (hfloor a t ht)).le)
    have hfinal : criticalPoissonTaylorBudget c (Pseq n) n s u ≤ ε :=
      hbound.trans ((mul_le_mul_of_nonneg_left henergy (by positivity)).trans hεb)
    exact not_lt_of_ge hfinal he
  exact (measureReal_mono hs (by finiteness)).trans
    ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl))

/-- The complex Taylor remainder in the conditional Poisson log characteristic
function, summed over both arms and all subjects with their actual intensities. -/
-- @node: criticalPoissonTaylorRemainder
noncomputable def criticalPoissonTaylorRemainder (c : ClassConstants) (P : SubjectLaw)
    (n : ℕ) (s : Fin n → ObsHistory) (u : ℝ) : ℂ :=
  ∑ a : Arm, ∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - bandwidth c n),
    Causalean.Stat.expQuadraticRemainder (u * criticalSignedRecurrenceWeight c P a s i t) *
      (P.lam a t : ℂ)

/-- The norm of the complex log-characteristic remainder is bounded by its
nonnegative intensity budget. Cancellation is never needed for this estimate. -/
-- @node: critical_poisson_taylor_remainder_norm_le
lemma critical_poisson_taylor_remainder_norm_le (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) {n : ℕ} (hn : 3 ≤ n) (s : Fin n → ObsHistory) (u : ℝ) :
    ‖criticalPoissonTaylorRemainder c P n s u‖ ≤ criticalPoissonTaylorBudget c P n s u := by
  unfold criticalPoissonTaylorRemainder criticalPoissonTaylorBudget
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  have hT : 0 ≤ 1 - bandwidth c n := by
    linarith [(bandwidth_pos_and_le_cap c (show 0 < n by omega)).2, c.x0_le]
  apply (intervalIntegral.norm_integral_le_integral_norm hT).trans_eq
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hT] at ht
  dsimp only
  have hlam : 0 ≤ P.lam a t := c.lambdaMin_pos.le.trans
    (hP.recurrenceBounds a t ⟨ht.1, by
      linarith [(bandwidth_pos_and_le_cap c (show 0 < n by omega)).1, ht.2]⟩).1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlam]

/-- The complex remainder in (19) vanishes in probability for each fixed
frequency, by the genuine intensity budget and no distributional assumption. -/
-- @node: critical_poisson_taylor_remainder_triangular_tendsto_zero
lemma critical_poisson_taylor_remainder_triangular_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (u : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (sampleLaw (Pseq n) n).real
      {s | ε < ‖criticalPoissonTaylorRemainder c (Pseq n) n s u‖}) atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (critical_poisson_taylor_budget_triangular_tendsto_zero c hk Pseq hP u hε)
  filter_upwards [eventually_ge_atTop 3] with n hn
  let : IsProbabilityMeasure (Pseq n).latent := ⟨(Pseq n).prob⟩
  let : IsProbabilityMeasure (observedLaw (Pseq n)) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw (Pseq n) n) := by unfold sampleLaw; infer_instance
  apply measureReal_mono _ (by finiteness)
  intro s hs
  exact hs.trans_le (critical_poisson_taylor_remainder_norm_le c (Pseq n) (hP n) hn s u)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

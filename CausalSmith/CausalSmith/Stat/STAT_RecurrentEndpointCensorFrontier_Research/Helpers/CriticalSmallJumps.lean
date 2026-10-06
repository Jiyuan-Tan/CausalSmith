module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalVarianceBounds
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceScoreEnergy

/-!
# Small critical recurrence coefficients

Roadmap (18): on the linear empirical risk floor, the actual subject recurrence
coefficients have a deterministic vanishing envelope after critical normalization.
This is the small-jump input to the conditional Poisson Taylor argument (19).
The probability of the risk event and the variance limit are separate obligations.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The actual recurrence coefficient retains the inverse empirical risk floor. -/
-- @node: recurrenceSubjectWeight_abs_le_of_risk_floor
lemma recurrenceSubjectWeight_abs_le_of_risk_floor (c : ClassConstants)
    (a : Arm) {n : ℕ} (s : Fin n → ObsHistory) (i : Fin n) {h t b : ℝ}
    (hh : 0 < h) (hb : 0 < b) (hfloor : b ≤ riskSet a s t) :
    |recurrenceSubjectWeight c h a s i t| ≤ weightEnvelope c / b := by
  have hW : 0 ≤ weightEnvelope c := by
    unfold weightEnvelope continuationNorm
    positivity
  have hz : riskSet a s t ≠ 0 := by
    exact_mod_cast (hb.trans_le hfloor).ne'
  have hi : invRisk a s t ≤ b⁻¹ := by
    simp only [invRisk, if_neg hz]
    exact inv_anti₀ hb hfloor
  unfold recurrenceSubjectWeight
  split_ifs
  · rw [abs_mul, abs_mul, abs_of_nonneg (deathKMLeft_mem_Icc a s t).1,
      abs_of_nonneg (recurrence_invRisk_mem_Icc a s t).1]
    calc
      _ ≤ weightEnvelope c * 1 * b⁻¹ := by
        gcongr
        · exact (recurrence_invRisk_mem_Icc a s t).1
        · exact (deathKMLeft_mem_Icc a s t).1
        · exact continuationWeight_abs_le_coeffSum (holderOrder c) hh
        · exact (deathKMLeft_mem_Icc a s t).2
      _ = _ := by simp [div_eq_mul_inv]
  · simpa using div_nonneg hW hb.le

/-- The normalized critical inverse risk floor is exactly a square-root energy. -/
-- @node: critical_small_jump_scale_eq
lemma critical_small_jump_scale_eq (c : ClassConstants) {n : ℕ} (hn : 3 ≤ n) :
    Real.sqrt ((n : ℝ) / Real.log n) / ((n : ℝ) * bandwidth c n) =
      Real.sqrt (1 / ((n : ℝ) * bandwidth c n ^ 2 * Real.log n)) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hh := (bandwidth_pos_and_le_cap c (show 0 < n by omega)).1
  have hl : 0 < Real.log (n : ℝ) :=
    lt_of_lt_of_le (by norm_num) (one_le_log_sampleSize hn)
  have hsq := Real.sq_sqrt (div_nonneg hnR.le hl.le)
  have hsq' := Real.sq_sqrt (show 0 ≤ 1 / ((n : ℝ) * bandwidth c n ^ 2 * Real.log n) by positivity)
  have he : (Real.sqrt ((n : ℝ) / Real.log n) / ((n : ℝ) * bandwidth c n)) ^ 2 =
      1 / ((n : ℝ) * bandwidth c n ^ 2 * Real.log n) := by
    rw [div_pow, hsq]
    field_simp
  nlinarith [Real.sqrt_nonneg (1 / ((n : ℝ) * bandwidth c n ^ 2 * Real.log n)),
    show 0 ≤ Real.sqrt ((n : ℝ) / Real.log n) / ((n : ℝ) * bandwidth c n) by positivity]

/-- Equation (1) implies that the actual critical small-jump scale vanishes. -/
-- @node: critical_small_jump_scale_tendsto_zero
lemma critical_small_jump_scale_tendsto_zero (c : ClassConstants) (hk : c.kappa = 1) :
    Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) / Real.log n) /
      ((n : ℝ) * bandwidth c n)) atTop (nhds 0) := by
  have hi := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).inv_tendsto_atTop
  have ht := (critical_log_div_sample_bandwidth_square_tendsto_zero c hk).mul (hi.pow 2)
  have he : Tendsto (fun n : ℕ => 1 / ((n : ℝ) * bandwidth c n ^ 2 * Real.log n))
      atTop (nhds 0) := by
    apply (show Tendsto (fun n : ℕ => Real.log n / ((n : ℝ) * bandwidth c n ^ 2) *
        (Real.log n)⁻¹ ^ 2) atTop (nhds 0) by simpa using ht).congr'
    filter_upwards [eventually_ge_atTop 3] with n hn
    have hl : Real.log (n : ℝ) ≠ 0 :=
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (one_le_log_sampleSize hn)).ne'
    field_simp
  apply (show Tendsto (fun n : ℕ => Real.sqrt
    (1 / ((n : ℝ) * bandwidth c n ^ 2 * Real.log n))) atTop (nhds 0) by
      simpa using he.sqrt).congr'
  filter_upwards [eventually_ge_atTop 3] with n hn
  exact (critical_small_jump_scale_eq c hn).symm

/-- On the linear risk event the standardized coefficient has a uniform bound;
the variance floor is the one proved from the model, not an added assumption. -/
-- @node: critical_normalized_recurrence_weight_le
lemma critical_normalized_recurrence_weight_le (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {n : ℕ} (hn : 3 ≤ n)
    (s : Fin n → ObsHistory) (i : Fin n) {r t : ℝ} (hr : 0 < r)
    (ht : t ∈ Icc (0 : ℝ) (1 - bandwidth c n))
    (hfloor : (n : ℝ) * r * (1 - t) ≤ riskSet a s t) :
    |Real.sqrt ((n : ℝ) / Real.log n) / Real.sqrt (criticalVariance c P) *
      recurrenceSubjectWeight c (bandwidth c n) a s i t| ≤
      (weightEnvelope c / (r * Real.sqrt
        (2 * criticalCoefficient c * (Real.exp (-c.dMax) * c.lambdaMin / c.gMax)))) *
      (Real.sqrt ((n : ℝ) / Real.log n) / ((n : ℝ) * bandwidth c n)) := by
  let v := 2 * criticalCoefficient c * (Real.exp (-c.dMax) * c.lambdaMin / c.gMax)
  have hv : 0 < v := by
    dsimp [v]
    exact mul_pos (mul_pos (by norm_num) (criticalCoefficient_pos_lt_half c).1)
      (div_pos (mul_pos (Real.exp_pos _) c.lambdaMin_pos)
        (c.gMin_pos.trans c.gMin_lt))
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hh := (bandwidth_pos_and_le_cap c (show 0 < n by omega)).1
  have hb : 0 < (n : ℝ) * r * bandwidth c n := by positivity
  have hf : (n : ℝ) * r * bandwidth c n ≤ riskSet a s t := by
    calc
      _ ≤ (n : ℝ) * r * (1 - t) :=
        mul_le_mul_of_nonneg_left (by linarith [ht.2]) (by positivity)
      _ ≤ _ := hfloor
  have hw := recurrenceSubjectWeight_abs_le_of_risk_floor c a s i hh hb hf
  have hs := Real.sqrt_le_sqrt (criticalVariance_uniform_lower c P hP)
  have hspos := Real.sqrt_pos.mpr hv
  have hW : 0 ≤ weightEnvelope c := by unfold weightEnvelope continuationNorm; positivity
  rw [abs_mul, abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  calc
    _ ≤ (Real.sqrt ((n : ℝ) / Real.log n) / Real.sqrt v) *
        (weightEnvelope c / ((n : ℝ) * r * bandwidth c n)) := by
      apply mul_le_mul
      · exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hspos hs
      · exact hw
      · exact abs_nonneg _
      · positivity
    _ = _ := by dsimp [v]; ring

/-- For every positive tolerance, all actual standardized subject coefficients on
the linear risk event are eventually smaller, uniformly over model laws. -/
-- @node: critical_normalized_recurrence_weight_eventually_small
lemma critical_normalized_recurrence_weight_eventually_small (c : ClassConstants)
    (hk : c.kappa = 1) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ P : SubjectLaw, ModelClass c P →
      ∀ a : Arm, ∀ s : Fin n → ObsHistory, ∀ i : Fin n, ∀ t : ℝ,
        t ∈ Icc (0 : ℝ) (1 - bandwidth c n) →
        (n : ℝ) * r * (1 - t) ≤ riskSet a s t →
        |Real.sqrt ((n : ℝ) / Real.log n) / Real.sqrt (criticalVariance c P) *
          recurrenceSubjectWeight c (bandwidth c n) a s i t| < ε := by
  let C := weightEnvelope c / (r * Real.sqrt
    (2 * criticalCoefficient c * (Real.exp (-c.dMax) * c.lambdaMin / c.gMax)))
  have hlim := (critical_small_jump_scale_tendsto_zero c hk).const_mul C
  have hlim' : Tendsto (fun n : ℕ => C * (Real.sqrt ((n : ℝ) / Real.log n) /
      ((n : ℝ) * bandwidth c n))) atTop (nhds 0) := by simpa using hlim
  filter_upwards [hlim'.eventually (gt_mem_nhds hε), eventually_ge_atTop 3] with n hn hn3
  intro P hP a s i t ht hf
  exact (critical_normalized_recurrence_weight_le c P hP a hn3 s i hr ht hf).trans_lt hn

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

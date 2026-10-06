module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalOracleBand
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalVarianceBounds

/-!
# Normalized critical oracle variance

The deterministic part of roadmap (15) follows from the full weighted
logarithmic expansion (13) and the exact eventual bandwidth logarithm (1).
Both the absolute and relative errors vanish along arbitrary triangular
model laws. This does not assume empirical risk or survival consistency.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The sum of the two genuinely weighted oracle recurrence energies, with
assignment probabilities retained in their denominators. -/
-- @node: criticalOracleEnergy
noncomputable def criticalOracleEnergy (c : ClassConstants) (P : SubjectLaw)
    (n : ℕ) : ℝ :=
  ∑ a : Arm, (∫ t in (0 : ℝ)..(1 - bandwidth c n),
    continuationWeight (holderOrder c) (bandwidth c n) t ^ 2 *
      survival P a t * P.lam a t / retention P a t) / P.p a

/-- Assignment overlap turns the uniform armwise logarithmic remainder into
a uniform two-arm remainder, with the exact critical variance coefficient. -/
-- @node: criticalOracleEnergy_log_remainder_uniform
lemma criticalOracleEnergy_log_remainder_uniform (c : ClassConstants)
    (hk : c.kappa = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ P : SubjectLaw, ModelClass c P →
        |criticalOracleEnergy c P n - criticalVariance c P * Real.log n| ≤ C := by
  obtain ⟨B, hB, hb⟩ := critical_oracle_log_expansion_uniform c hk
  refine ⟨2 * (B / c.pMin), mul_nonneg (by norm_num) (div_nonneg hB c.pMin_pos.le), ?_⟩
  filter_upwards [critical_bandwidth_eventually_log c hk, eventually_ge_atTop 1]
    with n hlog hn
  intro P hP
  have hh := bandwidth_pos_and_le_cap c (show 0 < n by omega)
  have hband : 2 * bandwidth c n ≤ c.x0 := by linarith [hh.2]
  have harm (a : Arm) :
      |(∫ t in (0 : ℝ)..(1 - bandwidth c n),
          continuationWeight (holderOrder c) (bandwidth c n) t ^ 2 *
            survival P a t * P.lam a t / retention P a t) / P.p a -
        criticalCoefficient c * (survival P a 1 * P.lam a 1 / (P.p a * P.g a)) *
          Real.log n| ≤ B / c.pMin := by
    have hp := c.pMin_pos.trans_le (hP.treatmentOverlap a)
    have he := hb P hP a (bandwidth c n) hh.1 hband
    rw [hlog] at he
    calc
      _ = |(∫ t in (0 : ℝ)..(1 - bandwidth c n),
          continuationWeight (holderOrder c) (bandwidth c n) t ^ 2 *
            survival P a t * P.lam a t / retention P a t) -
          (survival P a 1 * P.lam a 1 / P.g a) *
            (criticalCoefficient c * Real.log n)| / P.p a := by
        rw [← abs_of_pos hp, ← abs_div, abs_of_pos hp]
        congr 1
        ring
      _ ≤ B / c.pMin := div_le_div₀ hB he c.pMin_pos (hP.treatmentOverlap a)
  have heq : criticalOracleEnergy c P n - criticalVariance c P * Real.log n =
      ∑ a : Arm, ((∫ t in (0 : ℝ)..(1 - bandwidth c n),
          continuationWeight (holderOrder c) (bandwidth c n) t ^ 2 *
            survival P a t * P.lam a t / retention P a t) / P.p a -
        criticalCoefficient c * (survival P a 1 * P.lam a 1 / (P.p a * P.g a)) *
          Real.log n) := by
    simp only [criticalOracleEnergy, criticalVariance, Finset.sum_sub_distrib,
      Finset.mul_sum, Finset.sum_mul]
  rw [heq]
  calc
    _ ≤ ∑ a : Arm, |(∫ t in (0 : ℝ)..(1 - bandwidth c n),
          continuationWeight (holderOrder c) (bandwidth c n) t ^ 2 *
            survival P a t * P.lam a t / retention P a t) / P.p a -
        criticalCoefficient c * (survival P a 1 * P.lam a 1 / (P.p a * P.g a)) *
          Real.log n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Arm, B / c.pMin := Finset.sum_le_sum (fun a _ => harm a)
    _ = _ := by simp [Arm]

/-- Along arbitrary triangular model laws, the normalized oracle energy has
vanishing absolute error from the law's own critical variance. -/
-- @node: criticalOracleEnergy_triangular_tendsto
lemma criticalOracleEnergy_triangular_tendsto (c : ClassConstants)
    (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) :
    Tendsto (fun n : ℕ => criticalOracleEnergy c (Pseq n) n / Real.log n -
      criticalVariance c (Pseq n)) atTop (nhds 0) := by
  obtain ⟨C, hC, hb⟩ := criticalOracleEnergy_log_remainder_uniform c hk
  have hi := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).inv_tendsto_atTop
  apply squeeze_zero_norm' _ (show Tendsto (fun n : ℕ => C / Real.log n)
      atTop (nhds 0) by simpa [div_eq_mul_inv] using hi.const_mul C)
  filter_upwards [hb, eventually_ge_atTop 3] with n hn hn3
  have hl : 0 < Real.log (n : ℝ) := lt_of_lt_of_le (by norm_num)
    (one_le_log_sampleSize hn3)
  rw [Real.norm_eq_abs, show criticalOracleEnergy c (Pseq n) n / Real.log n -
      criticalVariance c (Pseq n) =
      (criticalOracleEnergy c (Pseq n) n - criticalVariance c (Pseq n) * Real.log n) /
        Real.log n by field_simp, abs_div, abs_of_pos hl]
  exact div_le_div_of_nonneg_right (hn (Pseq n) (hP n)) hl.le

/-- The positive model-derived variance floor also makes the relative oracle
variance converge to one, as needed for conditional Gaussian calibration. -/
-- @node: criticalOracleEnergy_triangular_relative_tendsto
lemma criticalOracleEnergy_triangular_relative_tendsto (c : ClassConstants)
    (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) :
    Tendsto (fun n : ℕ => criticalOracleEnergy c (Pseq n) n /
      (Real.log n * criticalVariance c (Pseq n))) atTop (nhds 1) := by
  let v := 2 * criticalCoefficient c * (Real.exp (-c.dMax) * c.lambdaMin / c.gMax)
  have hv : 0 < v := by
    dsimp [v]
    exact mul_pos (mul_pos (by norm_num) (criticalCoefficient_pos_lt_half c).1)
      (div_pos (mul_pos (Real.exp_pos _) c.lambdaMin_pos) (c.gMin_pos.trans c.gMin_lt))
  have ht := criticalOracleEnergy_triangular_tendsto c hk Pseq hP
  have hz : Tendsto (fun n : ℕ => criticalOracleEnergy c (Pseq n) n /
      (Real.log n * criticalVariance c (Pseq n)) - 1) atTop (nhds 0) := by
    apply squeeze_zero_norm' _ (show Tendsto (fun n : ℕ =>
      |criticalOracleEnergy c (Pseq n) n / Real.log n - criticalVariance c (Pseq n)| / v)
      atTop (nhds 0) by simpa using ht.abs.div_const v)
    filter_upwards [eventually_ge_atTop 3] with n hn
    have hl : Real.log (n : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le
      (by norm_num : (0 : ℝ) < 1) (one_le_log_sampleSize hn))
    have hp := criticalVariance_pos c (Pseq n) (hP n)
    rw [Real.norm_eq_abs, show criticalOracleEnergy c (Pseq n) n /
        (Real.log n * criticalVariance c (Pseq n)) - 1 =
        (criticalOracleEnergy c (Pseq n) n / Real.log n - criticalVariance c (Pseq n)) /
          criticalVariance c (Pseq n) by field_simp, abs_div, abs_of_pos hp]
    exact div_le_div₀ (abs_nonneg _) le_rfl hv
      (criticalVariance_uniform_lower c (Pseq n) (hP n))
  simpa using hz.add_const 1

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

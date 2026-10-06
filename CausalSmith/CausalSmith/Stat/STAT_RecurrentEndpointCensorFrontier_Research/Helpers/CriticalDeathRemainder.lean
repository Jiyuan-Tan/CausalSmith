module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalAsymptotics
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathCountingProcessExplicitRisk
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathErrorIntegrability

/-!
# Negligible critical death remainder

Roadmap (22): the remaining-target terminal distance cancels the critical
inverse-retention singularity, giving a uniform O(1/n) death second moment.
Chebyshev then makes the death term negligible at the critical scale.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The continued remaining target retains its terminal distance factor. -/
-- @node: remainingTarget_abs_le_terminal_distance
lemma remainingTarget_abs_le_terminal_distance (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {h t : ℝ}
    (hh : 0 < h) (ht : t ∈ Set.Icc 0 (1 - h)) :
    |remainingTarget c P a h t| ≤ weightEnvelope c * c.lambdaMax * (1 - t) := by
  have hh1 : h ≤ 1 := by linarith [ht.1, ht.2]
  have hU1 : 1 - h ≤ 1 := by linarith
  have hweight : ∀ u,
      |continuationWeight (holderOrder c) h u| ≤ weightEnvelope c := by
    intro u
    change |continuationWeight (holderOrder c) h u| ≤
      1 + ∑ m : Fin (holderOrder c + 1),
        |((continuationGram (holderOrder c))⁻¹.mulVec
          (continuationRhs (holderOrder c))) m| * (2 : ℝ) ^ m.val
    exact continuationWeight_abs_le_coeffSum (holderOrder c) hh
  have henv0 : 0 ≤ weightEnvelope c := by
    unfold weightEnvelope continuationNorm
    positivity
  have hlam0 : 0 ≤ c.lambdaMax := c.lambdaMin_pos.le.trans c.lambdaMin_lt.le
  have hbound : ∀ u ∈ Set.uIoc t (1 - h),
      ‖continuationWeight (holderOrder c) h u * survival P a u * P.lam a u‖ ≤
        weightEnvelope c * c.lambdaMax := by
    intro u hu
    rw [Set.uIoc_of_le ht.2] at hu
    have hu01 : u ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨ht.1.trans hu.1.le, hu.2.trans hU1⟩
    have hs := (survival_bounds_of_deathBounds c P hP.deathBounds a hu01).2
    have hs0 : 0 ≤ survival P a u := (Real.exp_pos _).le
    have hlam := (hP.recurrenceBounds a u hu01).2
    have hlamPos : 0 ≤ P.lam a u :=
      c.lambdaMin_pos.le.trans (hP.recurrenceBounds a u hu01).1
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hs0,
      abs_of_nonneg hlamPos]
    calc
      _ ≤ weightEnvelope c * 1 * c.lambdaMax := by
        gcongr
        exact hweight u
      _ = weightEnvelope c * c.lambdaMax := by ring
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  unfold remainingTarget
  rw [Real.norm_eq_abs] at hnorm
  rw [abs_of_nonneg (sub_nonneg.mpr ht.2)] at hnorm
  exact hnorm.trans (by nlinarith [mul_nonneg henv0 hlam0])

/-- Critical retention has a linear lower envelope across the full study window. -/
-- @node: critical_retention_ge_linear
lemma critical_retention_ge_linear (c : ClassConstants) (hk : c.kappa = 1)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) 1) :
    min c.Gint (c.gMin / 2) * (1 - t) ≤ retention P a t := by
  by_cases hi : t ≤ 1 - c.x0
  · have hG := hP.interiorRetention a t ⟨ht.1, hi⟩
    have hm : 0 ≤ min c.Gint (c.gMin / 2) :=
      le_min c.Gint_pos.le (div_nonneg c.gMin_pos.le (by norm_num))
    calc
      _ ≤ min c.Gint (c.gMin / 2) := mul_le_of_le_one_right hm (by linarith [ht.1])
      _ ≤ c.Gint := min_le_left _ _
      _ ≤ _ := hG
  · have hG := retention_ge_half_gMin_rpow c P hP a ⟨lt_of_not_ge hi, ht.2⟩
    rw [hk, Real.rpow_one] at hG
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (by linarith [ht.2])).trans hG

/-- The critical death energy density has a law-independent constant envelope. -/
-- @node: critical_deathRateEnergy_density_le
lemma critical_deathRateEnergy_density_le (c : ClassConstants) (hk : c.kappa = 1)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {h t : ℝ}
    (hh : 0 < h) (ht : t ∈ Icc (0 : ℝ) (1 - h)) :
    (deathTargetWeight c P a h t) ^ 2 * P.hazard a t /
      (retention P a t * survival P a t) ≤
    (weightEnvelope c * c.lambdaMax * Real.exp c.dMax) ^ 2 * c.dMax /
      (min c.Gint (c.gMin / 2) * Real.exp (-c.dMax)) := by
  let B := weightEnvelope c * c.lambdaMax * Real.exp c.dMax
  let r := min c.Gint (c.gMin / 2)
  have hr : 0 < r := lt_min c.Gint_pos (half_pos c.gMin_pos)
  have hx : 0 < 1 - t := by linarith [ht.2]
  have hx1 : 1 - t ≤ 1 := by linarith [ht.1]
  have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, by linarith [ht.2]⟩
  have hs0 : 0 < survival P a t := Real.exp_pos _
  have hs := (survival_bounds_of_deathBounds c P hP.deathBounds a ht01).1
  have hG := critical_retention_ge_linear c hk P hP a ⟨ht.1, by linarith [ht.2]⟩
  have hG0 : 0 < retention P a t := (mul_pos hr hx).trans_le hG
  have he : 0 ≤ weightEnvelope c := by unfold weightEnvelope continuationNorm; positivity
  have hl : 0 ≤ c.lambdaMax := c.lambdaMin_pos.le.trans c.lambdaMin_lt.le
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg he hl) (Real.exp_pos _).le
  have hW : |deathTargetWeight c P a h t| ≤ B * (1 - t) := by
    rw [deathTargetWeight, if_pos ht, abs_div, abs_of_pos hs0, div_eq_mul_inv]
    have hi : (survival P a t)⁻¹ ≤ Real.exp c.dMax := by
      have hi := (inv_le_inv₀ hs0 (Real.exp_pos (-c.dMax))).2 hs
      simpa [Real.exp_neg] using hi
    have hb := mul_le_mul (remainingTarget_abs_le_terminal_distance c P hP a hh ht)
      hi (inv_nonneg.mpr hs0.le) (mul_nonneg (mul_nonneg he hl) hx.le)
    dsimp [B]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hb
  have hsq : (deathTargetWeight c P a h t) ^ 2 ≤ B ^ 2 * (1 - t) ^ 2 := by
    have hb := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hB hx.le)).2 hW
    simpa only [sq_abs, mul_pow] using hb
  have hd := (hP.deathBounds a t ht01).2
  have hd0 := c.dMin_pos.le.trans (hP.deathBounds a t ht01).1
  have hdmax : 0 ≤ c.dMax := c.dMin_pos.le.trans c.dMin_lt.le
  have hnum := mul_le_mul hsq hd hd0 (mul_nonneg (sq_nonneg B) (sq_nonneg (1 - t)))
  have hden : r * (1 - t) * Real.exp (-c.dMax) ≤ retention P a t * survival P a t :=
    mul_le_mul hG hs (Real.exp_pos _).le hG0.le
  calc
    _ ≤ (B ^ 2 * (1 - t) ^ 2 * c.dMax) / (r * (1 - t) * Real.exp (-c.dMax)) :=
      div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = (B ^ 2 * c.dMax / (r * Real.exp (-c.dMax))) * (1 - t) := by
      field_simp
    _ ≤ B ^ 2 * c.dMax / (r * Real.exp (-c.dMax)) :=
      mul_le_of_le_one_right (by positivity) hx1

/-- Critical death risk is bounded by C/n uniformly over all model laws and bandwidths. -/
-- @node: critical_deathError_secondMoment_le
lemma critical_deathError_secondMoment_le (c : ClassConstants) (hk : c.kappa = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : SubjectLaw, ModelClass c P → ∀ a : Arm,
      ∀ n : ℕ, 0 < n → ∀ h : ℝ, 0 < h → h ≤ 1 →
        (∫ s, deathError c P a s h ^ 2 ∂sampleLaw P n) ≤ C / n := by
  let K := (weightEnvelope c * c.lambdaMax * Real.exp c.dMax) ^ 2 * c.dMax /
    (min c.Gint (c.gMin / 2) * Real.exp (-c.dMax))
  have hd : 0 ≤ c.dMax := c.dMin_pos.le.trans c.dMin_lt.le
  have hr : 0 < min c.Gint (c.gMin / 2) := lt_min c.Gint_pos (half_pos c.gMin_pos)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨2 * K / c.pMin, div_nonneg (by positivity) c.pMin_pos.le, ?_⟩
  intro P hP a n hn h hh hh1
  have henergy : (∫ t in Icc (0 : ℝ) (1 - h),
      deathTargetWeight c P a h t ^ 2 * P.hazard a t /
        (retention P a t * survival P a t)) ≤ K := by
    have hi := DeathCP.deathRateEnergy_integrableOn c P hP a hh hh1
    have hc : IntegrableOn (fun _ : ℝ => K) (Icc (0 : ℝ) (1 - h)) :=
      integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    have hb := integral_mono_ae hi hc (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact critical_deathRateEnergy_density_le c hk P hP a hh ht)
    have he : (∫ t in Icc (0 : ℝ) (1 - h), K) = (1 - h) * K := by
      simp [integral_const, (show 0 ≤ 1 - h by linarith)]
    rw [he] at hb
    exact hb.trans (mul_le_of_le_one_left hK (by linarith))
  have he := DeathCP.deathError_secondMoment_le_finiteRateEnergy c P hP a hn hh hh1
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  calc
    _ ≤ (2 / ((n : ℝ) * c.pMin)) * K :=
      he.trans (mul_le_mul_of_nonneg_left henergy
        (div_nonneg (by norm_num) (mul_pos hnR c.pMin_pos).le))
    _ = _ := by ring

/-- Chebyshev makes each genuine death remainder negligible at the critical
normalization along arbitrary triangular model sequences. -/
-- @node: critical_deathError_triangular_probability_tendsto_zero
lemma critical_deathError_triangular_probability_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw (Pseq n) n).real
      {s | ε < |Real.sqrt ((n : ℝ) / Real.log n) *
        deathError c (Pseq n) a s (bandwidth c n)|}) atTop (nhds 0) := by
  obtain ⟨C, hC, hb⟩ := critical_deathError_secondMoment_le c hk
  have hl := ((Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).inv_tendsto_atTop).const_mul (C / ε ^ 2)
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [mul_zero] using hl)
  filter_upwards [eventually_ge_atTop 3] with n hn
  let P := Pseq n
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hn0 : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hlog : 0 < Real.log (n : ℝ) := lt_of_lt_of_le (by norm_num) (one_le_log_sampleSize hn)
  have hh := bandwidth_pos_and_le_cap c hn0
  have hh1 : bandwidth c n ≤ 1 := hh.2.trans (by linarith [c.x0_le])
  let q := Real.sqrt ((n : ℝ) / Real.log n)
  have hq : q ^ 2 = (n : ℝ) / Real.log n := Real.sq_sqrt (by positivity)
  have hi := (deathError_sq_integrable c P (hP n) a n hh.1.le hh1).const_mul (q ^ 2)
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun s => mul_nonneg (sq_nonneg q)
      (sq_nonneg (deathError c P a s (bandwidth c n))))) hi (ε ^ 2)
  have hsub : {s : Fin n → ObsHistory | ε < |q * deathError c P a s (bandwidth c n)|} ⊆
      {s | ε ^ 2 ≤ q ^ 2 * deathError c P a s (bandwidth c n) ^ 2} := by
    intro s hs
    change ε < |q * deathError c P a s (bandwidth c n)| at hs
    change ε ^ 2 ≤ q ^ 2 * deathError c P a s (bandwidth c n) ^ 2
    have he := sq_abs (q * deathError c P a s (bandwidth c n))
    rw [mul_pow] at he
    nlinarith [abs_nonneg (q * deathError c P a s (bandwidth c n))]
  have hm2 := ((mul_le_mul_of_nonneg_left (measureReal_mono hsub (by finiteness))
    (sq_nonneg ε)).trans hm)
  rw [integral_const_mul] at hm2
  have hm3 := hm2.trans (mul_le_mul_of_nonneg_left (hb P (hP n) a n hn0 _ hh.1 hh1)
    (sq_nonneg q))
  change (sampleLaw P n).real {s | ε < |q * deathError c P a s (bandwidth c n)|} ≤
    C / ε ^ 2 * (Real.log (n : ℝ))⁻¹
  rw [show C / ε ^ 2 * (Real.log (n : ℝ))⁻¹ = (C / Real.log n) / ε ^ 2 by ring]
  apply (le_div_iff₀ (sq_pos_of_pos hε)).2
  have he : q ^ 2 * (C / (n : ℝ)) = C / Real.log n := by
    rw [hq]; field_simp
  rw [he] at hm3
  simpa only [mul_comm] using hm3

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

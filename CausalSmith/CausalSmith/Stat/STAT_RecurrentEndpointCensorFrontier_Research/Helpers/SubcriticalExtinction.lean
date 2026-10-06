module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ExtinctionSecondMoment
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalDeathPlugin
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Negligibility of the ordinary extinction correction

Roadmap (20)--(22): a shrinking endpoint risk horizon controls the ordinary
extinction remainder. The subcritical retention exponent makes even a horizon
of width proportional to the reciprocal sample size retain growing expected
risk. No inverse-weight moment or independence of estimated coefficients is
assumed.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The ordinary extinction remainder is bounded by its remaining horizon
length, including an empty treatment arm. -/
-- @node: extinctionError_zero_abs_le_remaining_horizon
lemma extinctionError_zero_abs_le_remaining_horizon
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (a : Arm) {n : ℕ} (s : Fin n → ObsHistory)
    (hExit : ∀ i, (s i).treatment = a → 0 ≤ (s i).exit ∧ (s i).exit ≤ 1) :
    |extinctionError c P a s 0| ≤
      (Real.exp c.dMax * c.lambdaMax) * (1 - extinction a s) := by
  have hz0 := extinction_nonneg_of_exit_bounds a s hExit
  have hz1 : extinction a s ≤ 1 := by
    by_cases ha : armSize a s = 0
    · simp [extinction, ha]
    · obtain ⟨i, hi, he, _⟩ :=
        extinction_eq_max_assigned_exit a s (Nat.pos_of_ne_zero ha) hExit
      rw [he]
      exact (hExit i hi).2
  have hL : 0 ≤ c.lambdaMax := c.lambdaMin_pos.le.trans c.lambdaMin_lt.le
  by_cases hz : extinction a s < 1
  · have hs0 : 0 < survival P a (extinction a s) := Real.exp_pos _
    have hs := (survival_bounds_of_deathBounds c P hP.deathBounds a ⟨hz0, hz1⟩).1
    have hinv : (survival P a (extinction a s))⁻¹ ≤ Real.exp c.dMax := by
      simpa only [Real.exp_neg, inv_inv] using
        (inv_le_inv₀ hs0 (Real.exp_pos (-c.dMax))).2 hs
    have hkm := deathKM_mem_Icc a s (extinction a s)
    have hr := remainingTarget_zero_mem_Icc c P hP a ⟨hz0, hz1⟩
    rw [extinctionError, sub_zero, if_pos hz, abs_mul, abs_div,
      abs_of_nonneg hkm.1, abs_of_pos hs0, abs_of_nonneg hr.1, div_eq_mul_inv]
    calc
      _ ≤ (1 * Real.exp c.dMax) * (c.lambdaMax * (1 - extinction a s)) :=
        mul_le_mul (mul_le_mul hkm.2 hinv (inv_nonneg.mpr hs0.le) zero_le_one)
          hr.2 hr.1 (by positivity)
      _ = _ := by ring
  · rw [extinctionError, sub_zero, if_neg hz, abs_zero]
    exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) hL) (sub_nonneg.mpr hz1)

/-- At a reciprocal-sample-size endpoint horizon, the probability of no
subject at risk vanishes under the subcritical retention assumption. -/
-- @node: subcritical_reciprocal_horizon_riskZero_tendsto_zero
lemma subcritical_reciprocal_horizon_riskZero_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | riskSet a s (1 - b / n) = 0}) atTop (nhds 0) := by
  let A := c.pMin * c.gMin * Real.exp (-c.dMax) / 2
  have hA : 0 < A := div_pos
    (mul_pos (mul_pos c.pMin_pos c.gMin_pos) (Real.exp_pos _)) (by norm_num)
  have hx : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - c.kappa)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hk)).comp tendsto_natCast_atTop_atTop
  have he : Tendsto (fun n : ℕ =>
      Real.exp (-(A * b ^ c.kappa * (n : ℝ) ^ (1 - c.kappa)))) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp
        (hx.const_mul_atTop' (mul_pos hA (Real.rpow_pos_of_pos hb c.kappa))))
  have hsmall : ∀ᶠ n : ℕ in atTop, b / (n : ℝ) ≤ c.x0 / 2 := by
    have hlim : Tendsto (fun n : ℕ => b / (n : ℝ)) atTop (nhds 0) := by
      simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply] using
        (tendsto_natCast_atTop_atTop.inv_tendsto_atTop.const_mul b)
    exact (hlim.eventually_lt_const (by linarith [c.x0_pos])).mono (fun _ h => h.le)
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ he
  filter_upwards [hsmall, eventually_ge_atTop 1] with n hncap hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := endpointRiskZero_probability_le_explicit c P hP a n
    (div_pos hb hnR) hncap
  have hid : A * n * (b / (n : ℝ)) ^ c.kappa =
      A * b ^ c.kappa * (n : ℝ) ^ (1 - c.kappa) := by
    rw [Real.div_rpow hb.le hnR.le, Real.rpow_sub hnR, Real.rpow_one]
    ring
  simpa only [A, hid] using h

/-- The ordinary extinction correction is negligible at root-n scale.
The shrinking-risk bound also covers empty treatment arms. -/
-- @node: subcritical_extinctionError_rootn_probability_tendsto_zero
lemma subcritical_extinctionError_rootn_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | ε < |Real.sqrt n * extinctionError c P a s 0|})
      atTop (nhds 0) := by
  let B := Real.exp c.dMax * c.lambdaMax
  have hB : 0 < B := mul_pos (Real.exp_pos _)
    (c.lambdaMin_pos.trans c.lambdaMin_lt)
  let b := ε / B
  have hb : 0 < b := div_pos hε hB
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (subcritical_reciprocal_horizon_riskZero_tendsto_zero c P hP hk a hb)
  have hsmall : ∀ᶠ n : ℕ in atTop, b / (n : ℝ) < 1 := by
    have hlim : Tendsto (fun n : ℕ => b / (n : ℝ)) atTop (nhds 0) := by
      simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply] using
        (tendsto_natCast_atTop_atTop.inv_tendsto_atTop.const_mul b)
    exact hlim.eventually_lt_const zero_lt_one
  filter_upwards [hsmall, eventually_ge_atTop 1] with n hnsmall hn
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsub : ∀ᵐ s ∂sampleLaw P n,
      s ∈ {s | ε < |Real.sqrt n * extinctionError c P a s 0|} →
      s ∈ {s | riskSet a s (1 - b / n) = 0} := by
    filter_upwards [sample_exit_nonneg P hP.deathHazard n,
      sample_exit_le_one P n] with s hs0 hs1
    intro hs
    have he := extinctionError_zero_abs_le_remaining_horizon c P hP a s
      (fun i _ => ⟨hs0 i, hs1 i⟩)
    have hsqrt : Real.sqrt (n : ℝ) ≤ n :=
      Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast hn))
    have hbound : |Real.sqrt n * extinctionError c P a s 0| ≤
        (n : ℝ) * (B * (1 - extinction a s)) := by
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact (mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hsqrt ((abs_nonneg _).trans he))
    have hgap : b / (n : ℝ) < 1 - extinction a s := by
      apply (div_lt_iff₀ hnR).2
      change ε / B < (1 - extinction a s) * (n : ℝ)
      apply (div_lt_iff₀ hB).2
      nlinarith [lt_of_lt_of_le hs hbound]
    exact riskSet_zero_after_extinction a s (1 - b / n)
      (by linarith) (by linarith [div_pos hb hnR])
      (by linarith)
  exact ENNReal.toReal_mono (by finiteness) (measure_mono_ae hsub)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalAsymptotics
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ExtinctionSecondMoment

/-!
# Critical extinction correction

Roadmap (4) and (23): endpoint retention gives a population risk lower bound
through the bandwidth cutoff. The iid empty-risk bound is exponentially small
in n h. Since the extinction correction vanishes outside that event, it is
negligible at the critical normalization along arbitrary triangular laws.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The critical population risk is uniformly bounded below through the cutoff. -/
-- @node: critical_cutoff_population_risk_lower
lemma critical_cutoff_population_risk_lower (c : ClassConstants)
    (hk : c.kappa = 1) (P : SubjectLaw) (hP : ModelClass c P)
    (a : Arm) {h t : ℝ} (hh : 0 < h) (hcap : h ≤ c.x0 / 2)
    (ht : t ∈ Icc (0 : ℝ) (1 - h)) :
    (c.pMin * c.gMin * Real.exp (-c.dMax) / 2) * h ≤
      P.p a * survival P a t * retention P a t := by
  have hr := retention_ge_half_gMin_rpow c P hP a
    (t := 1 - h) (by constructor <;> linarith [c.x0_pos])
  simp only [sub_sub_cancel, hk, Real.rpow_one] at hr
  have hs := (survival_bounds_of_deathBounds c P hP.deathBounds a
    ⟨ht.1, by linarith [ht.2]⟩).1
  have hp := hP.treatmentOverlap a
  have hb := mul_le_mul
    (mul_le_mul hp hs (Real.exp_pos _).le (c.pMin_pos.le.trans hp))
    (hr.trans ((retention_antitone P a) ht.2))
    (mul_nonneg (div_nonneg c.gMin_pos.le (by norm_num)) hh.le)
    (mul_nonneg (c.pMin_pos.le.trans hp) (Real.exp_pos _).le)
  calc
    _ = c.pMin * Real.exp (-c.dMax) * (c.gMin / 2 * h) := by ring
    _ ≤ _ := hb

/-- The finite-sample critical empty-risk bound has exponent proportional to n h. -/
-- @node: critical_endpointRiskZero_probability_le_exp
lemma critical_endpointRiskZero_probability_le_exp (c : ClassConstants)
    (hk : c.kappa = 1) (P : SubjectLaw) (hP : ModelClass c P)
    (a : Arm) {n : ℕ} (hn : 0 < n) :
    (sampleLaw P n).real {s | riskSet a s (1 - bandwidth c n) = 0} ≤
      Real.exp (-((c.pMin * c.gMin * Real.exp (-c.dMax) / 2) *
        n * bandwidth c n)) := by
  have hh := bandwidth_pos_and_le_cap c hn
  simpa only [hk, Real.rpow_one] using
    endpointRiskZero_probability_le_explicit c P hP a n hh.1 hh.2

/-- Expected risk at the critical cutoff diverges because q is below one half. -/
-- @node: critical_sample_bandwidth_tendsto_atTop
lemma critical_sample_bandwidth_tendsto_atTop (c : ClassConstants)
    (hk : c.kappa = 1) :
    Tendsto (fun n : ℕ => (n : ℝ) * bandwidth c n) atTop atTop := by
  have hp : 0 < 1 - criticalCoefficient c := by
    linarith [(criticalCoefficient_pos_lt_half c).2]
  have hl := (tendsto_rpow_atTop hp).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply hl.congr'
  filter_upwards [critical_bandwidth_eventually_eq_power c hk,
    eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  change (n : ℝ) ^ (1 - criticalCoefficient c) = (n : ℝ) * bandwidth c n
  rw [hn]
  symm
  nth_rw 1 [← Real.rpow_one (n : ℝ)]
  rw [← Real.rpow_add hn0]
  congr 1

/-- The law-independent critical extinction envelope tends to zero. -/
-- @node: critical_extinction_exp_tendsto_zero
lemma critical_extinction_exp_tendsto_zero (c : ClassConstants)
    (hk : c.kappa = 1) :
    Tendsto (fun n : ℕ => Real.exp
      (-((c.pMin * c.gMin * Real.exp (-c.dMax) / 2) * n * bandwidth c n)))
      atTop (nhds 0) := by
  have hA : 0 < c.pMin * c.gMin * Real.exp (-c.dMax) / 2 := by
    exact div_pos (mul_pos (mul_pos c.pMin_pos c.gMin_pos) (Real.exp_pos _))
      (by norm_num)
  have hl := (critical_sample_bandwidth_tendsto_atTop c hk).const_mul_atTop hA
  simpa only [Function.comp_def, mul_assoc] using
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hl)

/-- Any nonzero scaled extinction error is supported on the exponentially
unlikely empty-risk event; no moment of the scale is required. -/
-- @node: critical_extinctionError_scaled_probability_le_exp
lemma critical_extinctionError_scaled_probability_le_exp (c : ClassConstants)
    (hk : c.kappa = 1) (P : SubjectLaw) (hP : ModelClass c P)
    (a : Arm) {n : ℕ} (hn : 0 < n) (r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (sampleLaw P n).real {s | ε < |r * extinctionError c P a s (bandwidth c n)|} ≤
      Real.exp (-((c.pMin * c.gMin * Real.exp (-c.dMax) / 2) *
        n * bandwidth c n)) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hsub : ∀ᵐ s ∂sampleLaw P n,
      s ∈ {s | ε < |r * extinctionError c P a s (bandwidth c n)|} →
      s ∈ {s | riskSet a s (1 - bandwidth c n) = 0} := by
    filter_upwards [sample_exit_nonneg P hP.deathHazard n,
      sample_exit_le_one P n] with s hs0 hs1
    intro hs
    by_contra hz
    have hb := extinctionError_abs_le_indicator c P hP a s
      (fun i _ => ⟨hs0 i, hs1 i⟩) (bandwidth_pos_and_le_cap c hn).1
    have he : extinctionError c P a s (bandwidth c n) = 0 :=
      abs_eq_zero.mp (le_antisymm (by simpa only [if_neg hz] using hb) (abs_nonneg _))
    simp only [he, mul_zero, abs_zero] at hs
    exact (not_lt_of_ge hε.le) hs
  exact (ENNReal.toReal_mono (by finiteness) (measure_mono_ae hsub)).trans
    (critical_endpointRiskZero_probability_le_exp c hk P hP a hn)

/-- Roadmap (23) makes the extinction correction negligible at the critical
normalization uniformly along arbitrary triangular model sequences. -/
-- @node: critical_extinctionError_triangular_probability_tendsto_zero
lemma critical_extinctionError_triangular_probability_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw (Pseq n) n).real
      {s | ε < |Real.sqrt ((n : ℝ) / Real.log n) *
        extinctionError c (Pseq n) a s (bandwidth c n)|})
      atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (critical_extinction_exp_tendsto_zero c hk)
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact critical_extinctionError_scaled_probability_le_exp
    c hk (Pseq n) (hP n) a (by omega) _ hε

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

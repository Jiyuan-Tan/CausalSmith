module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathKMOracleControl
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionDeathRegularity
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionHazardDensity

/-!
# Kaplan--Meier oracle control under the benchmark assumptions

Roadmap (19)--(22): joint measurability and deterministic energy envelopes
for the genuine KM oracle integrand require only integrable bounded death
hazards. The measurable hazard representative preserves the source law.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

/-- The reciprocal-survival multiplier is measurable for model-class laws. -/
-- @node: positiveRetention_measurable_kmOracleWeight
@[fun_prop] lemma positiveRetention_measurable_kmOracleWeight (c : ClassConstants) (P : SubjectLaw)
    (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P) (a : Arm) {T : ℝ} (hT0 : 0 ≤ T)
    (hT1 : T ≤ 1) : Measurable (kmOracleWeight P a T) := by
  have hsurv : ContinuousOn (survival P a) (Set.Icc (0 : ℝ) T) :=
    (positiveRetention_survival_continuousOn P hDeath a).mono
      (Set.Icc_subset_Icc le_rfl hT1)
  have hratio : ContinuousOn
      (fun t => survival P a T / survival P a t) (Set.Icc (0 : ℝ) T) :=
    continuousOn_const.div hsurv (fun t _ => (Real.exp_pos _).ne')
  unfold kmOracleWeight
  exact hratio.measurable_piecewise continuousOn_const measurableSet_Icc

/-- The fixed-horizon oracle integrand is jointly measurable. -/
-- @node: positiveRetention_kmOracleIntegrand_jointMeasurable
@[fun_prop] lemma positiveRetention_kmOracleIntegrand_jointMeasurable (c : ClassConstants) (P : SubjectLaw)
    (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P) (a : Arm) {T : ℝ} (hT0 : 0 ≤ T)
    (hT1 : T ≤ 1) {n : ℕ} :
    Measurable (fun p : ℝ × Sample n => kmOracleIntegrand P a T p.1 p.2) := by
  unfold kmOracleIntegrand
  exact (((positiveRetention_measurable_kmOracleWeight c P hDeath hDeathBounds a hT0 hT1).comp measurable_fst).mul
    pairDeathKMLeft_jointMeasurable).mul
    Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk_jointMeasurable

/-- On the fixed study window, the deterministic oracle multiplier is bounded
by the inverse model-class survival floor. -/
-- @node: positiveRetention_kmOracleWeight_abs_le_exp
lemma positiveRetention_kmOracleWeight_abs_le_exp (c : ClassConstants) (P : SubjectLaw)
    (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P) (a : Arm) {T t : ℝ} (hT0 : 0 ≤ T)
    (hT1 : T ≤ 1) : |kmOracleWeight P a T t| ≤ Real.exp c.dMax := by
  by_cases ht : t ∈ Set.Icc (0 : ℝ) T
  · have hsTpos : 0 < survival P a T := Real.exp_pos _
    have hstpos : 0 < survival P a t := Real.exp_pos _
    rw [kmOracleWeight, if_pos ht, abs_div,
      abs_of_pos hsTpos, abs_of_pos hstpos]
    have hsT := (survival_bounds_of_deathBounds c P hDeathBounds a
      ⟨hT0, hT1⟩).2
    have hst := (survival_bounds_of_deathBounds c P hDeathBounds a
      ⟨ht.1, ht.2.trans hT1⟩).1
    have hpos : 0 < survival P a t := Real.exp_pos _
    calc
      survival P a T / survival P a t ≤ 1 / Real.exp (-c.dMax) :=
        div_le_div₀ zero_le_one hsT (Real.exp_pos _) hst
      _ = Real.exp c.dMax := by rw [Real.exp_neg]; simp
  · simp [kmOracleWeight, ht, Real.exp_pos _ |>.le]

/-- The quadratic-energy density is bounded by the deterministic survival
envelope times the zero-safe inverse risk. -/
-- @node: positiveRetention_kmOracle_energyDensity_le
lemma positiveRetention_kmOracle_energyDensity_le (c : ClassConstants) (P : SubjectLaw)
    (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P) (a : Arm) {T : ℝ} (hT0 : 0 ≤ T)
    (hT1 : T ≤ 1) {n : ℕ} (t : ℝ) (x : Sample n) :
    (kmOracleIntegrand P a T t x) ^ 2 * positiveRetention_referenceHazard P hDeath a t *
        (∑ i : Fin n,
          Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x) ≤
      (Real.exp c.dMax) ^ 2 * positiveRetention_referenceHazard P hDeath a t *
        Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x := by
  have hkm := pairDeathKMLeft_mem_Icc t x
  have hrisk :=
    Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk_square_risk t x
  have hweight := positiveRetention_kmOracleWeight_abs_le_exp c P hDeath hDeathBounds a hT0 hT1 (t := t)
  have hwSq : (kmOracleWeight P a T t) ^ 2 ≤ (Real.exp c.dMax) ^ 2 := by
    have hs := (sq_le_sq₀ (abs_nonneg (kmOracleWeight P a T t))
      (Real.exp_pos c.dMax).le).2 hweight
    simpa only [sq_abs] using hs
  have hkmSq : (pairDeathKMLeft t x) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hkm.1 (sub_nonneg.mpr hkm.2)]
  have hhaz : 0 ≤ positiveRetention_referenceHazard P hDeath a t :=
    positiveRetention_referenceHazard_nonneg P hDeath a t
  rw [kmOracleIntegrand]
  calc
    _ = (kmOracleWeight P a T t) ^ 2 * (pairDeathKMLeft t x) ^ 2 *
        positiveRetention_referenceHazard P hDeath a t *
          ((Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x) ^ 2 *
            (∑ i : Fin n,
              Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x)) := by
      ring
    _ = (kmOracleWeight P a T t) ^ 2 * (pairDeathKMLeft t x) ^ 2 *
        positiveRetention_referenceHazard P hDeath a t *
          Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x := by
      rw [hrisk]
    _ ≤ (Real.exp c.dMax) ^ 2 * 1 * positiveRetention_referenceHazard P hDeath a t *
          Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x := by
      gcongr
      exact (pairInverseRisk_mem_Icc t x).1
    _ = _ := by ring

end CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

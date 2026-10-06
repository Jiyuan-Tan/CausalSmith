module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalVariationMean
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalWitnessProbability

/-!
# Uniform expected length of critical intervals

Roadmap (34) combines the proved optional-variation mean bound with genuine
exponential fallback control. The conclusion holds at every sample size at
least three and is independent of the unfinished Gaussian limit proof.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The full critical interval, including its full-range fallback, has
uniform expected length of order square root of log n over n. -/
-- @node: criticalInterval_expected_length_uniform_log_rate
lemma criticalInterval_expected_length_uniform_log_rate (c : ClassConstants)
    (hkappa : c.kappa = 1) (alpha : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n →
      ∀ P : SubjectLaw, ModelClass c P →
        (∫ s, volume.real (criticalInterval c alpha s) ∂sampleLaw P n) ≤
          C * Real.sqrt (Real.log n / n) := by
  obtain ⟨Cf, hCf, hf⟩ := nonFallback_compl_uniform_log_rate_bound c
  let K := 4 * reciprocalRetentionEnvelope c * weightEnvelope c ^ 2 / c.pMin *
    c.lambdaMax * Real.exp c.dMax * varianceRateEnvelope c
  let C := 2 * normalQuantile alpha * Real.sqrt K + 2 * c.lambdaMax * Cf
  have hl := c.lambdaMin_pos.trans c.lambdaMin_lt
  have hz := (normalQuantile_pos halpha0 halpha1).le
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro n hn P hP
  have hb := criticalInterval_expected_length_le_log_rate_fallback
    c hkappa P hP alpha halpha0 halpha1 hn
  have hr : 0 ≤ Real.log (n : ℝ) / n := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact div_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans (one_le_log_sampleSize hn)) hnR.le
  change (∫ s, volume.real (criticalInterval c alpha s) ∂sampleLaw P n) ≤
    2 * normalQuantile alpha * Real.sqrt (K * (Real.log n / n)) +
      2 * c.lambdaMax * (sampleLaw P n).real {s | ¬ nonFallback c s} at hb
  rw [Real.sqrt_mul' K hr] at hb
  calc
    _ ≤ 2 * normalQuantile alpha * (Real.sqrt K * Real.sqrt (Real.log n / n)) +
        2 * c.lambdaMax * (Cf * Real.sqrt (Real.log n / n)) :=
      hb.trans (add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left (hf n hn P hP) (by positivity)))
    _ = _ := by dsimp [C]; ring

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

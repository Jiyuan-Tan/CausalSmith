module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.Fallback
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.Converse.Target
public import Causalean.Mathlib.Probability.IidMeanVariance

/-!
# Sampling risk and the small-log fallback regime

The centered arrived score has second moment at most one. Its empirical mean
therefore has parametric sampling error; projection preserves the resulting
bias-and-sampling bound. Bounded loss closes the small-log regime uniformly.
-/

@[expose] public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The centered arrived-outcome score used by the fallback branch. Given [the specified input `d`](hyp:d), [the specified input `o`](hyp:o), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_fallbackScore
noncomputable def upper_fallbackScore {d : ℕ} (o : Obs d) : ℝ :=
  2 * (if o.A then (1 : ℝ) else -1) *
    (if o.R then (1 : ℝ) else 0) *
    ((if o.RY then (1 : ℝ) else 0) - 1 / 2)

/-- Every fallback score has squared magnitude at most one. Given [the specified input `d`](hyp:d), [the specified input `o`](hyp:o), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_fallbackScore_sq_le_one
lemma upper_fallbackScore_sq_le_one {d : ℕ} (o : Obs d) :
    upper_fallbackScore o ^ 2 ≤ 1 := by
  cases hA : o.A <;> cases hR : o.R <;> cases hY : o.RY <;>
    norm_num [upper_fallbackScore, hA, hR, hY]

/-- The fallback formula is the projection of the empirical score mean. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `sample`](hyp:sample), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_fallbackHT_eq_average
lemma upper_fallbackHT_eq_average {n d : ℕ} (sample : Fin n → Obs d) :
    fallbackHT sample = clipUnit ((n : ℝ)⁻¹ * ∑ i, upper_fallbackScore (sample i)) := by
  simp only [upper_fallbackScore, Finset.mul_sum, fallbackHT]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The iid empirical fallback score mean has sampling error at most one over n. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_fallback_average_sampling_risk
lemma upper_fallback_average_sampling_risk {n d : ℕ} (hn : 0 < n)
    (P : FullLaw d) :
    (∫ sample, ((n : ℝ)⁻¹ * ∑ i : Fin n, upper_fallbackScore (sample i) -
      ∫ o, upper_fallbackScore o ∂(observedLaw P).toMeasure) ^ 2 ∂samplePi P n) ≤
      1 / (n : ℝ) := by
  have hF : MemLp (upper_fallbackScore (d := d)) 2 (observedLaw P).toMeasure := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
    exact Integrable.of_finite
  have hsecond : (∫ o, upper_fallbackScore o ^ 2 ∂(observedLaw P).toMeasure) ≤ 1 := by
    calc
      _ ≤ ∫ _ : Obs d, (1 : ℝ) ∂(observedLaw P).toMeasure :=
        integral_mono Integrable.of_finite (integrable_const 1)
          upper_fallbackScore_sq_le_one
      _ = 1 := by simp
  have hi := Causalean.Mathlib.Probability.iid_mean_sq_le
    (observedLaw P).toMeasure hn upper_fallbackScore hF
  exact hi.trans (div_le_div_of_nonneg_right hsecond (by positivity))

/-- Projection and the sampling bound control fallback risk by twice sampling
error plus twice its population bias squared. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_fallback_risk_le_bias
lemma upper_fallback_risk_le_bias {n d : ℕ} (hn : 0 < n) (P : FullLaw d) :
    (∫ sample, (fallbackHT sample - tau P) ^ 2 ∂samplePi P n) ≤
      2 / (n : ℝ) + 2 *
        ((∫ o, upper_fallbackScore o ∂(observedLaw P).toMeasure) - tau P) ^ 2 := by
  let : IsProbabilityMeasure (samplePi P n) := by unfold samplePi; infer_instance
  let b := (∫ o, upper_fallbackScore o ∂(observedLaw P).toMeasure) - tau P
  let c := ∫ o, upper_fallbackScore o ∂(observedLaw P).toMeasure
  have hs := upper_fallback_average_sampling_risk hn P
  calc
    _ ≤ ∫ sample, (2 * ((n : ℝ)⁻¹ * ∑ i : Fin n,
        upper_fallbackScore (sample i) - c) ^ 2 + 2 * b ^ 2) ∂samplePi P n := by
      apply integral_mono Integrable.of_finite Integrable.of_finite
      intro sample
      dsimp only
      rw [upper_fallbackHT_eq_average]
      have hp := clipUnit_sq_error_le
        ((n : ℝ)⁻¹ * ∑ i : Fin n, upper_fallbackScore (sample i))
        (tau P) (tau_range P)
      dsimp [b, c]
      nlinarith [sq_nonneg ((n : ℝ)⁻¹ * ∑ i : Fin n,
        upper_fallbackScore (sample i) - 2 * c + tau P)]
    _ = 2 * (∫ sample, ((n : ℝ)⁻¹ * ∑ i : Fin n,
        upper_fallbackScore (sample i) - c) ^ 2 ∂samplePi P n) + 2 * b ^ 2 := by
      rw [integral_add Integrable.of_finite (integrable_const _), integral_const_mul]
      simp
    _ ≤ 2 * (1 / (n : ℝ)) + 2 * b ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 2)) le_rfl
    _ = _ := by dsimp [b]; ring

/-- The bounded estimator and target have squared loss at most four. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_estimator_risk_le_four
lemma upper_estimator_risk_le_four {n d : ℕ} (q : ℝ) (P : FullLaw d) :
    (∫ sample, (tauhatMM n d q sample - tau P) ^ 2 ∂samplePi P n) ≤ 4 := by
  let : IsProbabilityMeasure (samplePi P n) := by unfold samplePi; infer_instance
  calc
    _ ≤ ∫ _ : Fin n → Obs d, (4 : ℝ) ∂samplePi P n := by
      apply integral_mono Integrable.of_finite (integrable_const _)
      intro sample
      have he := tauhatMM_range n d q sample
      have ht := tau_range P
      nlinarith [he.1, he.2, ht.1, ht.2]
    _ = 4 := by simp

/-- When the logarithmic scale is small, bounded loss is already a universal
multiple of the inverse-sample-size component of the frontier rate. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `q`](hyp:q), [the specified input `P`](hyp:P), [the specified input `hL`](hyp:hL), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_small_log_risk_rate
lemma upper_small_log_risk_rate {n d : ℕ} (hn : 0 < n) (q : ℝ)
    (P : FullLaw d) (hL : ell n < 128) :
    (∫ sample, (tauhatMM n d q sample - tau P) ^ 2 ∂samplePi P n) ≤
      (4 * Real.exp 128) * rate n d q := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hexp : (n : ℝ) < Real.exp 128 := by
    have h := Real.lt_exp_of_log_lt hL
    change Real.exp 1 + (n : ℝ) < Real.exp 128 at h
    linarith [Real.exp_pos 1]
  have hrate : 1 / (n : ℝ) ≤ rate n d q := by
    unfold rate
    linarith [sq_nonneg (gScale n d q)]
  calc
    _ ≤ 4 := upper_estimator_risk_le_four q P
    _ ≤ 4 * Real.exp 128 * (1 / (n : ℝ)) := by
      rw [mul_one_div, le_div_iff₀ hnR]
      linarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hrate (by positivity)

end CausalSmith.Stat.MarNearcompleteFrontier

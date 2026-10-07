module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerScoreLogQuantileBridge

/-! Exact quantiles of the normalized Bernoulli margin in the three-score problem. -/

public section

namespace CausalSmith.PartialID.UnlinkedPropensityAte

open MeasureTheory ProbabilityTheory Set
open Causalean.Stat

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:q,t,h0,h1), this result [establishes the stated mathematical conclusion](goal). -/
lemma threeScoreOutcomeLaw_isProbabilityMeasure (q t : ℝ)
    (h0 : 0 ≤ t / q) (h1 : t / q ≤ 1) :
    IsProbabilityMeasure (threeScoreOutcomeLaw q t) := by
  rw [isProbabilityMeasure_iff]
  unfold threeScoreOutcomeLaw
  rw [Measure.add_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply, Set.mem_univ,
    Set.indicator_of_mem, Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 (sub_nonneg.mpr h1)]
  norm_num

private lemma threeScoreOutcomeLaw_cdf_of_lt_zero (q t r : ℝ)
    (h0 : 0 ≤ t / q) (h1 : t / q ≤ 1) (hr : r < 0) :
    cdf (threeScoreOutcomeLaw q t) r = 0 := by
  letI := threeScoreOutcomeLaw_isProbabilityMeasure q t h0 h1
  rw [cdf_eq_real]
  have hr0 : ¬0 ≤ r := not_le.mpr hr
  have hr1 : ¬1 ≤ r := not_le.mpr (lt_trans hr (by norm_num))
  simp [threeScoreOutcomeLaw, Measure.real, hr0, hr1]

private lemma threeScoreOutcomeLaw_cdf_between (q t r : ℝ)
    (h0 : 0 ≤ t / q) (h1 : t / q ≤ 1) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    cdf (threeScoreOutcomeLaw q t) r = 1 - t / q := by
  letI := threeScoreOutcomeLaw_isProbabilityMeasure q t h0 h1
  rw [cdf_eq_real]
  simp [threeScoreOutcomeLaw, Measure.real, hr0, not_le.mpr hr1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr h1)]

private lemma threeScoreOutcomeLaw_cdf_one (q t : ℝ)
    (h0 : 0 ≤ t / q) (h1 : t / q ≤ 1) :
    cdf (threeScoreOutcomeLaw q t) 1 = 1 := by
  letI := threeScoreOutcomeLaw_isProbabilityMeasure q t h0 h1
  rw [cdf_eq_real]
  simp only [threeScoreOutcomeLaw, Measure.real, Measure.add_apply,
    Measure.smul_apply, Measure.dirac_apply]
  rw [Set.indicator_of_mem (show (1 : ℝ) ∈ Iic 1 by simp),
    Set.indicator_of_mem (show (0 : ℝ) ∈ Iic 1 by simp)]
  simp only [Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 (sub_nonneg.mpr h1)]
  norm_num

/-- Given [the stated mathematical inputs and assumptions](hyp:q,t,u,h0,h1,hu0,hu1), this result [establishes the stated mathematical conclusion](goal). -/
lemma threeScoreOutcomeLaw_quantile
    (q t u : ℝ) (h0 : 0 ≤ t / q) (h1 : t / q ≤ 1)
    (hu0 : 0 < u) (hu1 : u < 1) :
    quantile (threeScoreOutcomeLaw q t) u =
      if u ≤ 1 - t / q then 0 else 1 := by
  letI := threeScoreOutcomeLaw_isProbabilityMeasure q t h0 h1
  split_ifs with hu
  · apply le_antisymm
    · apply quantile_le_of_le_cdf hu0
      have hc := threeScoreOutcomeLaw_cdf_between q t 0 h0 h1 (le_refl 0) (by norm_num)
      simpa [hc] using hu
    · by_contra hn
      have hneg : quantile (threeScoreOutcomeLaw q t) u < 0 := lt_of_not_ge hn
      have hle := (quantile_le_iff hu0 hu1).mp (le_refl (quantile (threeScoreOutcomeLaw q t) u))
      rw [threeScoreOutcomeLaw_cdf_of_lt_zero q t _ h0 h1 hneg] at hle
      linarith
  · apply le_antisymm
    · apply quantile_le_of_le_cdf hu0
      rw [threeScoreOutcomeLaw_cdf_one q t h0 h1]
      exact hu1.le
    · by_contra hn
      have hlt : quantile (threeScoreOutcomeLaw q t) u < 1 := lt_of_not_ge hn
      let r := (quantile (threeScoreOutcomeLaw q t) u + 1) / 2
      have hqr : quantile (threeScoreOutcomeLaw q t) u ≤ r := by
        dsimp [r]
        linarith
      have hr0 : 0 ≤ r := by
        have hq0 : 0 ≤ quantile (threeScoreOutcomeLaw q t) u := by
          by_contra hn0
          have hqneg : quantile (threeScoreOutcomeLaw q t) u < 0 := lt_of_not_ge hn0
          have hle := (quantile_le_iff hu0 hu1).mp
            (le_refl (quantile (threeScoreOutcomeLaw q t) u))
          rw [threeScoreOutcomeLaw_cdf_of_lt_zero q t _ h0 h1 hqneg] at hle
          linarith
        dsimp [r]
        linarith
      have hr1 : r < 1 := by dsimp [r]; linarith
      have hle := (quantile_le_iff hu0 hu1).mp hqr
      rw [threeScoreOutcomeLaw_cdf_between q t r h0 h1 hr0 hr1] at hle
      exact hu hle

end
end CausalSmith.PartialID.UnlinkedPropensityAte

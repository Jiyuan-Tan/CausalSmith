module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperArmMean
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperRaoBlackwell

/-! # Completed bounded-alphabet upper branch

The empirical-ratio risk bound from roadmap equations (4)–(6), together with
unit-range loss, gives the headline minimum-rate bound whenever d is below
the fixed universal cutoff. No unknown cell mass enters the final constant.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory


-- @node: logAlphabet_le_of_le
/-- Below a fixed alphabet cutoff, the logarithmic rate scale is uniformly bounded. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hdD), the [stated conclusion](goal) holds. -/
lemma logAlphabet_le_of_le {d D : ℕ} (hd : 1 ≤ d) (hdD : d ≤ D) :
    logAlphabet d ≤ logAlphabet D := by
  apply Real.log_le_log
  · have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    positivity
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hdD) (Real.exp_pos _).le

/-- On the bounded-alphabet branch the exact headline estimator satisfies the minimum-form rate, with a constant depending only on the fixed cutoff. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH₀,hκ,hD₀,hn,hd,hdD,hε,hε1,hP,hiid), the [stated conclusion](goal) holds. -/
lemma armwiseEstimator_boundedAlphabet_sqRisk_le
    (H₀ κ : ℝ) (D₀ : ℕ) (hH₀ : 0 < H₀) (hκ : 0 < κ) (hD₀ : 2 ≤ D₀)
    {n d : ℕ} {ε : ℝ} (hn : 1 ≤ n) (hd : 2 ≤ d) (hdD : d < D₀)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (P : DiscreteLaw d) (hP : ObservedClass ε P)
    (μ : Measure (Fin n → Obs d)) (hiid : IidSampling P μ) :
    Causalean.Stat.sqRisk μ (armwiseEstimatorFormula H₀ κ D₀ hH₀ hκ hD₀ n d ε)
      (observedValue P) ≤ (1 + 8 * logAlphabet D₀) * rateScale n d ε := by
  have hn0 : 0 < n := by omega
  have hN : (0 : ℝ) < n := by exact_mod_cast hn0
  have hL : 0 < logAlphabet d := logAlphabet_pos (by omega)
  have hL₀ : 0 < logAlphabet D₀ := logAlphabet_pos (by omega)
  have hLL := logAlphabet_le_of_le (by omega : 1 ≤ d) (Nat.le_of_lt hdD)
  have hparam := empiricalValue_sqRisk_le hn0 P hP hε hε1
  let : IsProbabilityMeasure μ := by
    rw [hiid]
    dsimp [productLaw]
    infer_instance
  have hi := armwiseEstimator_sqRisk_le_one H₀ κ D₀ hH₀ hκ hD₀ ε P μ
  have heq : armwiseEstimatorFormula H₀ κ D₀ hH₀ hκ hD₀ n d ε = empiricalValue := by
    funext o
    simp only [armwiseEstimatorFormula, hdD, if_pos]
  rw [heq] at hi ⊢
  rw [hiid] at hi ⊢
  have hR : 0 ≤ (d : ℝ) / ((n : ℝ) * ε * logAlphabet d) := by positivity
  have hscale : 8 * d / ((n : ℝ) * ε) =
      8 * logAlphabet d * ((d : ℝ) / ((n : ℝ) * ε * logAlphabet d)) := by
    field_simp
  rw [hscale] at hparam
  unfold rateScale
  rcases le_total (1 : ℝ) ((d : ℝ) / ((n : ℝ) * ε * logAlphabet d)) with hsat | hsmall
  · rw [min_eq_left hsat, mul_one]
    exact hi.trans (by linarith)
  · rw [min_eq_right hsmall]
    exact hparam.trans (mul_le_mul_of_nonneg_right (by linarith) hR)

end CausalSmith.Stat.OptvalueVanishingoverlapRate

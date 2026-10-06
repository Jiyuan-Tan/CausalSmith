module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperBoundedAlphabet
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperPoissonization

/-! # Observable upper-risk assembly

Equations (34)–(37) transfer an uncapped marked-experiment estimate to the
actual observed estimator and combine all three branches. The remaining
input is explicitly the uncapped experiment estimate; no headline theorem
is asserted here without that analytic input.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory
open Causalean.Mathlib.Probability
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Mathlib.Probability.Poisson.FinitePartition.CappedPrefix

/-- On the active branch, cap restoration and finite Rao–Blackwellization convert the uncapped intensity-scale estimate into the observed minimum rate. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH₀,hκ,hD₀,hn,hd,hε,hε1,hC,hactive,hiid,hmarked), the [stated conclusion](goal) holds. -/
lemma armwiseEstimator_active_marked_rate_le (H₀ κ : ℝ) (D₀ : ℕ)
    (hH₀ : 0 < H₀) (hκ : 0 < κ) (hD₀ : 2 ≤ D₀)
    {n d : ℕ} {ε C : ℝ} (hn : 1 ≤ n) (hd : D₀ ≤ d)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hC : 0 ≤ C)
    (hactive : (d : ℝ) / logAlphabet d ≤ (n : ℝ) * ε)
    (P : DiscreteLaw d) (μ : Measure (Fin n → Obs d)) (hiid : IidSampling P μ)
    (hmarked : Causalean.Stat.sqRisk
      (finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : NNReal) / 4))
      (markedPoissonStatistic n d H₀ hH₀ κ ε) (observedValue P) ≤
        C * ((d : ℝ) / (((n : ℝ) / 8) * ε * logAlphabet d))) :
    Causalean.Stat.sqRisk μ (armwiseEstimatorFormula H₀ κ D₀ hH₀ hκ hD₀ n d ε)
      (observedValue P) ≤ (8 * C + 2) * rateScale n d ε := by
  rw [hiid]
  let : IsProbabilityMeasure (productLaw P n) := by dsimp [productLaw]; infer_instance
  have hunit := armwiseEstimator_sqRisk_le_one H₀ κ D₀ hH₀ hκ hD₀ ε P (productLaw P n)
  have htransfer := armwiseEstimator_active_le_markedPoisson_sqRisk
    H₀ κ D₀ hH₀ hκ hD₀ hd hactive P
  have htail := capExponential_le_observable_rate (d := d) hn (by omega) hε hε1
  have hscale : (d : ℝ) / (((n : ℝ) / 8) * ε * logAlphabet d) =
      8 * ((d : ℝ) / ((n : ℝ) * ε * logAlphabet d)) := by ring
  rw [hscale] at hmarked
  have hraw : Causalean.Stat.sqRisk (productLaw P n)
      (armwiseEstimatorFormula H₀ κ D₀ hH₀ hκ hD₀ n d ε) (observedValue P) ≤
      (8 * C + 2) * ((d : ℝ) / ((n : ℝ) * ε * logAlphabet d)) := by
    nlinarith
  unfold rateScale
  rcases le_total (1 : ℝ) ((d : ℝ) / ((n : ℝ) * ε * logAlphabet d)) with hsat | hsmall
  · rw [min_eq_left hsat, mul_one]
    exact hunit.trans (by linarith)
  · rw [min_eq_right hsmall]
    exact hraw

/-- A uniform uncapped marked-experiment bound on active parameters suffices for the actual estimator on every branch; the cutoff enters only through a bounded logarithm in the empirical branch. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH₀,hκ,hD₀,hn,hd,hε,hε1,hC,hP,hiid,hmarked), the [stated conclusion](goal) holds. -/
lemma armwiseEstimator_allBranches_rate_le (H₀ κ : ℝ) (D₀ : ℕ)
    (hH₀ : 0 < H₀) (hκ : 0 < κ) (hD₀ : 2 ≤ D₀)
    {n d : ℕ} {ε C : ℝ} (hn : 1 ≤ n) (hd : 2 ≤ d)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hC : 0 ≤ C)
    (P : DiscreteLaw d) (hP : ObservedClass ε P)
    (μ : Measure (Fin n → Obs d)) (hiid : IidSampling P μ)
    (hmarked : D₀ ≤ d → (d : ℝ) / logAlphabet d ≤ (n : ℝ) * ε →
      Causalean.Stat.sqRisk
        (finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
          ((n : NNReal) / 4))
        (markedPoissonStatistic n d H₀ hH₀ κ ε) (observedValue P) ≤
          C * ((d : ℝ) / (((n : ℝ) / 8) * ε * logAlphabet d))) :
    Causalean.Stat.sqRisk μ (armwiseEstimatorFormula H₀ κ D₀ hH₀ hκ hD₀ n d ε)
      (observedValue P) ≤
        (3 + 8 * logAlphabet D₀ + 8 * C) * rateScale n d ε := by
  have hL₀ := logAlphabet_pos (by omega : 1 ≤ D₀)
  have hL := logAlphabet_pos (by omega : 1 ≤ d)
  have hrate : 0 ≤ rateScale n d ε := by
    unfold rateScale
    exact le_min (by norm_num) (by positivity)
  by_cases hsmall : d < D₀
  · exact (armwiseEstimator_boundedAlphabet_sqRisk_le H₀ κ D₀ hH₀ hκ hD₀
      hn hd hsmall hε hε1 P hP μ hiid).trans
        (mul_le_mul_of_nonneg_right (by linarith) hrate)
  · have hdD : D₀ ≤ d := Nat.le_of_not_gt hsmall
    by_cases hsat : (n : ℝ) * ε < (d : ℝ) / logAlphabet d
    · exact (armwiseEstimator_saturated_rate_bound H₀ κ D₀ hH₀ hκ hD₀
        hn hdD hε hsat P μ hiid).trans
          (mul_le_mul_of_nonneg_right (by linarith) hrate)
    · have hactive := le_of_not_gt hsat
      exact (armwiseEstimator_active_marked_rate_le H₀ κ D₀ hH₀ hκ hD₀
        hn hdD hε hε1 hC hactive P μ hiid (hmarked hdD hactive)).trans
          (mul_le_mul_of_nonneg_right (by linarith) hrate)

/-- Taking the supremum over all legal observed laws preserves the assembled three-branch rate. Measurability follows from the finite observed sample alphabet, so the remaining input is only the marked-experiment content bound. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH₀,hκ,hD₀,hn,hd,hε,hε1,hC,hiid,hmarked), the [stated conclusion](goal) holds. -/
lemma armwiseEstimator_allBranches_worstRisk_le (H₀ κ : ℝ) (D₀ : ℕ)
    (hH₀ : 0 < H₀) (hκ : 0 < κ) (hD₀ : 2 ≤ D₀)
    {n d : ℕ} {ε C : ℝ} (hn : 1 ≤ n) (hd : 2 ≤ d)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hC : 0 ≤ C)
    (sampleLaw : ModelLaw d ε → Measure (Fin n → Obs d))
    (hiid : ∀ P, IidSampling P.1 (sampleLaw P))
    (hmarked : D₀ ≤ d → (d : ℝ) / logAlphabet d ≤ (n : ℝ) * ε →
      ∀ P : ModelLaw d ε,
        Causalean.Stat.sqRisk
          (finitePoissonSampleLaw (P.1.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
            ((n : NNReal) / 4))
          (markedPoissonStatistic n d H₀ hH₀ κ ε) (observedValue P.1) ≤
            C * ((d : ℝ) / (((n : ℝ) / 8) * ε * logAlphabet d))) :
    Measurable (armwiseEstimatorFormula H₀ κ D₀ hH₀ hκ hD₀ n d ε) ∧
      (⨆ P : ModelLaw d ε,
        Causalean.Stat.sqRisk (sampleLaw P)
          (armwiseEstimatorFormula H₀ κ D₀ hH₀ hκ hD₀ n d ε) (observedValue P.1)) ≤
        (3 + 8 * logAlphabet D₀ + 8 * C) * rateScale n d ε := by
  constructor
  · fun_prop
  · classical
    cases isEmpty_or_nonempty (ModelLaw d ε) with
    | inl hempty =>
      let := hempty
      rw [iSup_of_empty']
      have hL₀ := logAlphabet_pos (by omega : 1 ≤ D₀)
      have hL := logAlphabet_pos (by omega : 1 ≤ d)
      have hrate : 0 ≤ rateScale n d ε := by
        unfold rateScale
        exact le_min (by norm_num) (by positivity)
      simpa using mul_nonneg (show 0 ≤ 3 + 8 * logAlphabet D₀ + 8 * C by positivity) hrate
    | inr hnonempty =>
      let := hnonempty
      apply ciSup_le
      intro P
      exact armwiseEstimator_allBranches_rate_le H₀ κ D₀ hH₀ hκ hD₀
        hn hd hε hε1 hC P.1 P.2 (sampleLaw P) (hiid P)
        (fun hdD hactive => hmarked hdD hactive P)

end CausalSmith.Stat.OptvalueVanishingoverlapRate

module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperEmpiricalRatio

/-! # Finite Rao–Blackwell risk transfer

The fair-mark average and the capped Poisson weights implement the auxiliary
expectation in roadmap equation (37). The omitted Poisson tail is an atom at
zero, so its squared loss must be included when applying Jensen. -/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory
open scoped BigOperators


-- @node: projectUnit_mem_unitInterval
/-- The projection used in every capped statistic has range in the unit interval. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma projectUnit_mem_unitInterval (z : ℝ) :
    0 ≤ projectUnit z ∧ projectUnit z ≤ 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- Every auxiliary capped statistic has range in the unit interval. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hk,H₀,hH₀), the [stated conclusion](goal) holds. -/
lemma cappedStatistic_mem_unitInterval {n d k : ℕ} (hk : k ≤ n)
    (H₀ : ℝ) (hH₀ : 0 < H₀) (κ ε : ℝ)
    (o : Fin n → Obs d) (marks : Fin k → Bool) :
    0 ≤ cappedStatisticFormula hk H₀ hH₀ κ ε o marks ∧
      cappedStatisticFormula hk H₀ hH₀ κ ε o marks ≤ 1 :=
  projectUnit_mem_unitInterval _


-- @node: poissonWeight_nonneg
/-- Poisson weights are nonnegative, including at zero intensity. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hrate), the [stated conclusion](goal) holds. -/
lemma poissonWeight_nonneg {rate : ℝ} (hrate : 0 ≤ rate) (k : ℕ) :
    0 ≤ poissonWeight rate k := by
  unfold poissonWeight
  positivity


-- @node: poissonWeight_hasSum_one
/-- The full Poisson weight series has total mass one. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hrate), the [stated conclusion](goal) holds. -/
lemma poissonWeight_hasSum_one {rate : ℝ} (hrate : 0 ≤ rate) :
    HasSum (poissonWeight rate) 1 := by
  exact ProbabilityTheory.hasSum_one_poissonMeasure ⟨rate, hrate⟩


-- @node: poissonWeight_sum_le_one
/-- Truncating Poisson weights at the sample cap produces a subprobability. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hrate), the [stated conclusion](goal) holds. -/
lemma poissonWeight_sum_le_one {rate : ℝ} (hrate : 0 ≤ rate) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), poissonWeight rate k ≤ 1 := by
  have h := poissonWeight_hasSum_one hrate
  rw [← h.tsum_eq]
  exact h.summable.sum_le_tsum _ (fun k _ => poissonWeight_nonneg hrate k)


-- @node: fairMarkWeight_sum_eq_one
/-- Fair marks on k observations have total weight one. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma fairMarkWeight_sum_eq_one (k : ℕ) :
    (∑ _marks : Fin k → Bool, (1 / 2 : ℝ) ^ k) = 1 := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
  rw [Nat.cast_pow, Nat.cast_ofNat, ← mul_pow]
  norm_num


-- @node: subprobability_average_sq_error_le
/-- Squared loss decreases under a finite subprobability average when its missing mass is assigned the statistic zero. This explicitly retains the loss on the cap tail. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hw,hm), the [stated conclusion](goal) holds. -/
lemma subprobability_average_sq_error_le {ι : Type*} (s : Finset ι)
    (w v : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (hm : ∑ i ∈ s, w i ≤ 1)
    (t : ℝ) :
    ((∑ i ∈ s, w i * v i) - t) ^ 2 ≤
      (∑ i ∈ s, w i * (v i - t) ^ 2) + (1 - ∑ i ∈ s, w i) * t ^ 2 := by
  have hc := Causalean.Mathlib.Analysis.weighted_inner_sq_le s w v (fun _ => 1) hw
  simp only [mul_one, one_pow] at hc
  have hv : 0 ≤ ∑ i ∈ s, w i * v i ^ 2 :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)
  have hb : (∑ i ∈ s, w i * v i) ^ 2 ≤ ∑ i ∈ s, w i * v i ^ 2 :=
    hc.trans (mul_le_of_le_one_right hv hm)
  have he : (∑ i ∈ s, w i * (v i - t) ^ 2) =
      (∑ i ∈ s, w i * v i ^ 2) - 2 * t * (∑ i ∈ s, w i * v i) +
        (∑ i ∈ s, w i) * t ^ 2 := by
    calc
      _ = ∑ i ∈ s, (w i * v i ^ 2 - (2 * t) * (w i * v i) + w i * t ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.mul_sum, Finset.sum_mul]
  rw [he]
  nlinarith


-- @node: fairMark_average_sq_error_le
/-- Averaging over the fair marks contracts squared loss pathwise. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma fairMark_average_sq_error_le (k : ℕ) (v : (Fin k → Bool) → ℝ) (t : ℝ) :
    ((∑ marks, (1 / 2 : ℝ) ^ k * v marks) - t) ^ 2 ≤
      ∑ marks, (1 / 2 : ℝ) ^ k * (v marks - t) ^ 2 := by
  have h := subprobability_average_sq_error_le Finset.univ
    (fun _ : Fin k → Bool => (1 / 2 : ℝ) ^ k) v
    (fun _ _ => by positivity) (fairMarkWeight_sum_eq_one k).le t
  simpa only [fairMarkWeight_sum_eq_one, sub_self, zero_mul, add_zero] using h

/-- In the active branch the deterministic estimator contracts the auxiliary squared loss, including the zero statistic when the Poisson count exceeds the cap. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH₀,hκ,hD₀,hd,hactive), the [stated conclusion](goal) holds. -/
lemma armwiseEstimator_active_sq_error_le (H₀ κ : ℝ) (D₀ : ℕ)
    (hH₀ : 0 < H₀) (hκ : 0 < κ) (hD₀ : 2 ≤ D₀)
    {n d : ℕ} {ε : ℝ} (hd : D₀ ≤ d)
    (hactive : (d : ℝ) / logAlphabet d ≤ (n : ℝ) * ε)
    (o : Fin n → Obs d) (t : ℝ) :
    (armwiseEstimatorFormula H₀ κ D₀ hH₀ hκ hD₀ n d ε o - t) ^ 2 ≤
      (∑ k ∈ Finset.range (n + 1), if hk : k ≤ n then
        poissonWeight (n / 4) k * ∑ marks : Fin k → Bool,
          (1 / 2 : ℝ) ^ k * (cappedStatisticFormula hk H₀ hH₀ κ ε o marks - t) ^ 2
        else 0) +
      (1 - ∑ k ∈ Finset.range (n + 1), poissonWeight (n / 4) k) * t ^ 2 := by
  let v : ℕ → ℝ := fun k => if hk : k ≤ n then
    ∑ marks : Fin k → Bool, (1 / 2 : ℝ) ^ k * cappedStatisticFormula hk H₀ hH₀ κ ε o marks
    else 0
  have hr : 0 ≤ (n : ℝ) / 4 := by positivity
  have hc := subprobability_average_sq_error_le (Finset.range (n + 1))
    (poissonWeight (n / 4)) v (fun k _ => poissonWeight_nonneg hr k)
    (poissonWeight_sum_le_one hr n) t
  have he : armwiseEstimatorFormula H₀ κ D₀ hH₀ hκ hD₀ n d ε o =
      ∑ k ∈ Finset.range (n + 1), poissonWeight (n / 4) k * v k := by
    simp only [armwiseEstimatorFormula, not_lt.mpr hd, not_lt.mpr hactive, ↓reduceIte]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    simp [v, hkn]
  rw [he]
  apply hc.trans
  apply add_le_add _ le_rfl
  apply Finset.sum_le_sum
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  simp only [v, dif_pos hkn]
  exact mul_le_mul_of_nonneg_left
    (fairMark_average_sq_error_le k (cappedStatisticFormula hkn H₀ hH₀ κ ε o) t)
    (poissonWeight_nonneg hr k)

/-- The finite Rao–Blackwell estimator stays in the unit interval in every branch. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH₀,hκ,hD₀), the [stated conclusion](goal) holds. -/
lemma armwiseEstimator_mem_unitInterval (H₀ κ : ℝ) (D₀ : ℕ)
    (hH₀ : 0 < H₀) (hκ : 0 < κ) (hD₀ : 2 ≤ D₀)
    (n d : ℕ) (ε : ℝ) (o : Fin n → Obs d) :
    0 ≤ armwiseEstimatorFormula H₀ κ D₀ hH₀ hκ hD₀ n d ε o ∧
      armwiseEstimatorFormula H₀ κ D₀ hH₀ hκ hD₀ n d ε o ≤ 1 := by
  unfold armwiseEstimatorFormula
  split_ifs with hsmall hsat
  · exact projectUnit_mem_unitInterval _
  · norm_num
  · have hr : 0 ≤ (n : ℝ) / 4 := by positivity
    constructor
    · apply Finset.sum_nonneg
      intro k hk
      split_ifs with hkn
      · apply mul_nonneg (poissonWeight_nonneg hr k)
        exact Finset.sum_nonneg fun marks _ => mul_nonneg (by positivity)
          (cappedStatistic_mem_unitInterval hkn H₀ hH₀ κ ε o marks).1
      · rfl
    · calc
        _ ≤ ∑ k ∈ Finset.range (n + 1), poissonWeight (n / 4) k := by
          apply Finset.sum_le_sum
          intro k hk
          split_ifs with hkn
          · apply mul_le_of_le_one_right (poissonWeight_nonneg hr k)
            calc
              _ ≤ ∑ _marks : Fin k → Bool, (1 / 2 : ℝ) ^ k := by
                apply Finset.sum_le_sum
                intro marks hm
                exact mul_le_of_le_one_right (by positivity)
                  (cappedStatistic_mem_unitInterval hkn H₀ hH₀ κ ε o marks).2
              _ = 1 := fairMarkWeight_sum_eq_one k
          · exact poissonWeight_nonneg hr k
        _ ≤ 1 := poissonWeight_sum_le_one hr n

/-- The estimator's unit-range loss provides the uniform bounded-risk part of the minimum-form bound, independently of the unknown cell masses and propensities. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH₀,hκ,hD₀), the [stated conclusion](goal) holds. -/
lemma armwiseEstimator_sqRisk_le_one (H₀ κ : ℝ) (D₀ : ℕ)
    (hH₀ : 0 < H₀) (hκ : 0 < κ) (hD₀ : 2 ≤ D₀)
    {n d : ℕ} (ε : ℝ) (P : DiscreteLaw d)
    (μ : Measure (Fin n → Obs d)) [IsProbabilityMeasure μ] :
    Causalean.Stat.sqRisk μ (armwiseEstimatorFormula H₀ κ D₀ hH₀ hκ hD₀ n d ε)
      (observedValue P) ≤ 1 := by
  have ht := observedValue_mem_unitInterval P
  have hpoint (o : Fin n → Obs d) :
      (armwiseEstimatorFormula H₀ κ D₀ hH₀ hκ hD₀ n d ε o - observedValue P) ^ 2 ≤ 1 := by
    have hv := armwiseEstimator_mem_unitInterval H₀ κ D₀ hH₀ hκ hD₀ n d ε o
    have hab : |armwiseEstimatorFormula H₀ κ D₀ hH₀ hκ hD₀ n d ε o - observedValue P| ≤ 1 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    simpa only [sq_abs, one_pow] using
      pow_le_pow_left₀ (abs_nonneg _) hab 2
  unfold Causalean.Stat.sqRisk
  calc
    _ ≤ ∫ _o : Fin n → Obs d, (1 : ℝ) ∂μ :=
      integral_mono Integrable.of_finite (integrable_const _) hpoint
    _ = 1 := by simp

/-- Equation (37) for the actual finite estimator: its observed risk is at most the Poisson-weighted, fair-mark auxiliary risk plus the cap-tail loss at zero. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH₀,hκ,hD₀,hd,hactive), the [stated conclusion](goal) holds. -/
lemma armwiseEstimator_active_sqRisk_le (H₀ κ : ℝ) (D₀ : ℕ)
    (hH₀ : 0 < H₀) (hκ : 0 < κ) (hD₀ : 2 ≤ D₀)
    {n d : ℕ} {ε : ℝ} (hd : D₀ ≤ d)
    (hactive : (d : ℝ) / logAlphabet d ≤ (n : ℝ) * ε)
    (P : DiscreteLaw d) (μ : Measure (Fin n → Obs d)) [IsProbabilityMeasure μ] :
    Causalean.Stat.sqRisk μ (armwiseEstimatorFormula H₀ κ D₀ hH₀ hκ hD₀ n d ε)
      (observedValue P) ≤
      (∑ k ∈ Finset.range (n + 1), if hk : k ≤ n then
        poissonWeight (n / 4) k * ∑ marks : Fin k → Bool,
          (1 / 2 : ℝ) ^ k * Causalean.Stat.sqRisk μ
            (fun o => cappedStatisticFormula hk H₀ hH₀ κ ε o marks) (observedValue P)
        else 0) +
      (1 - ∑ k ∈ Finset.range (n + 1), poissonWeight (n / 4) k) * (observedValue P) ^ 2 := by
  unfold Causalean.Stat.sqRisk
  calc
    _ ≤ ∫ o, ((∑ k ∈ Finset.range (n + 1), if hk : k ≤ n then
        poissonWeight (n / 4) k * ∑ marks : Fin k → Bool,
          (1 / 2 : ℝ) ^ k * (cappedStatisticFormula hk H₀ hH₀ κ ε o marks - observedValue P) ^ 2
        else 0) +
      (1 - ∑ k ∈ Finset.range (n + 1), poissonWeight (n / 4) k) * (observedValue P) ^ 2) ∂μ :=
      integral_mono Integrable.of_finite Integrable.of_finite
        (fun o => armwiseEstimator_active_sq_error_le H₀ κ D₀ hH₀ hκ hD₀
          hd hactive o (observedValue P))
    _ = _ := by
      rw [integral_add Integrable.of_finite (integrable_const _)]
      simp only [integral_const, probReal_univ, one_smul]
      congr 1
      rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      simp only [dif_pos hkn]
      rw [integral_const_mul, integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
      simp only [integral_const_mul]

end CausalSmith.Stat.OptvalueVanishingoverlapRate

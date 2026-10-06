module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.SmallCapacityLower
public import Causalean.Stat.Minimax.LeCamTwoPoint
public import Causalean.Stat.Minimax.ChiSquared
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram.Risk

/-! The capacity-active minimax converse, conditional on the known-reference gate. -/

@[expose] public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open MeasureTheory

/-- Measurable scalar estimators of the half-budget value. -/
abbrev ScalarEstimator (n d : ℕ) :=
  {f : (Fin n → Obs d) → ℝ // Measurable f}

private lemma curveRate_nonneg_local {n d : ℕ} (hn : 1 ≤ n) (hd : 2 ≤ d) :
    0 ≤ curveRate n d := by
  unfold curveRate
  apply le_min (by norm_num)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hL : 0 < logAlphabet d := by
    unfold logAlphabet
    rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hdR)]
    simp
    positivity
  positivity

private lemma curveRate_small_le {n d : ℕ} (hn : 1 ≤ n) (hd : 2 ≤ d)
    (hd3 : d ≤ 3) : curveRate n d ≤ 3 / (n : ℝ) := by
  unfold curveRate
  refine (min_le_right _ _).trans ?_
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  have hL : 1 ≤ logAlphabet d := by
    unfold logAlphabet
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hdpos)]
    simp
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ d))
  apply (div_le_iff₀ (mul_pos hnR (lt_of_lt_of_le zero_lt_one hL))).2
  calc
    (d : ℝ) ≤ 3 := hdR
    _ ≤ (3 / (n : ℝ)) * ((n : ℝ) * logAlphabet d) := by
      field_simp
      nlinarith

private lemma curveRate_half_floor {n d : ℕ} (hn : 1 ≤ n) (hd : 4 ≤ d) :
    curveRate n d ≤ 3 * curveRate n (d / 2) := by
  let k := d / 2
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hkd : k ≤ d := by dsimp [k]; omega
  have hdk : d ≤ 3 * k := by dsimp [k]; omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hLk : 0 < logAlphabet k := by
    unfold logAlphabet
    rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hkR)]
    simp
    positivity
  have hLd : 0 < logAlphabet d := by
    unfold logAlphabet
    rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hdR)]
    simp
    positivity
  have hlog : logAlphabet k ≤ logAlphabet d := by
    unfold logAlphabet
    exact Real.log_le_log (mul_pos (Real.exp_pos 1) hkR)
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hkd) (Real.exp_pos 1).le)
  have hratio : (d : ℝ) / ((n : ℝ) * logAlphabet d) ≤
      3 * ((k : ℝ) / ((n : ℝ) * logAlphabet k)) := by
    have hdkR : (d : ℝ) ≤ 3 * k := by exact_mod_cast hdk
    calc
      (d : ℝ) / ((n : ℝ) * logAlphabet d) ≤
          (3 * k : ℝ) / ((n : ℝ) * logAlphabet d) := by gcongr
      _ ≤ (3 * k : ℝ) / ((n : ℝ) * logAlphabet k) := by
        apply div_le_div_of_nonneg_left (by positivity) (mul_pos hnR hLk)
        exact mul_le_mul_of_nonneg_left hlog hnR.le
      _ = 3 * ((k : ℝ) / ((n : ℝ) * logAlphabet k)) := by ring
  unfold curveRate
  by_cases hr : 1 ≤ (k : ℝ) / ((n : ℝ) * logAlphabet k)
  · rw [min_eq_left hr, mul_one]
    exact (min_le_left _ _).trans (by norm_num)
  · rw [min_eq_right (le_of_not_ge hr)]
    exact (min_le_right _ _).trans hratio

-- @node: thm:capacity-active-lower
/-- The capacity active lower result. Under [the he premise](hyp:he), [the he' premise](hyp:he'), It proves [the stated conclusion](goal). -/
theorem capacity_active_lower (epsilon : ℝ)
    (he : 0 < epsilon) (he' : epsilon < 1 / 2)
    (_of_gate : JHWKnownQL1LowerRegime) :
    ∃ c : ℝ, 0 < c ∧ ∀ n d : ℕ,
      1 ≤ n → 2 ≤ d →
      ∀ mu : PotentialLaw d → Measure (Fin n → Obs d),
        (∀ Q, IidSampling (observedMarginal Q) (mu Q)) →
        ∀ T : ScalarEstimator n d,
          ∃ Q : PotentialLaw d,
            Q ∈ capacityHardClass d epsilon ∧
            c * curveRate n d ≤
              Causalean.Stat.sqRisk (mu Q) T.1 (budgetValue Q (1 / 2)) := by
  obtain ⟨cL, hcL, hL⟩ := two_sample_l1_lower_all_samples _of_gate
  let c : ℝ := min (cL / 6144) (1 / 12288)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro n d hn hd mu hmu T
  by_cases hd4 : 4 ≤ d
  · let k := d / 2
    have hk : 2 ≤ k := by dsimp [k]; omega
    have hkd : 2 * k ≤ d := by dsimp [k]; omega
    let L := cL * min 1 ((k : ℝ) / (n * logAlphabet k))
    have hrate0 : 0 < min 1 ((k : ℝ) / (n * logAlphabet k)) := by
      apply lt_min zero_lt_one
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hlog : 0 < logAlphabet k := by
        unfold logAlphabet
        rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hkR)]
        simp
        positivity
      positivity
    have hlow : L ≤ twoSampleL1MinimaxRisk n k := hL k n hk hn
    obtain ⟨Q, hQ, hR⟩ := pairedL1_lower_transport_capacity_padded
      (by omega : 1 ≤ k) hkd epsilon he he' L (mul_pos hcL hrate0) hlow mu hmu T
    refine ⟨Q, hQ, ?_⟩
    have hcurve := curveRate_half_floor hn hd4
    have hc_le : c ≤ cL / 6144 := min_le_left _ _
    calc
      c * curveRate n d ≤ (cL / 6144) * curveRate n d := by
        gcongr
        exact curveRate_nonneg_local hn hd
      _ ≤ (1 / 32 : ℝ) ^ 2 * (L / 2) := by
        dsimp [L, curveRate, k] at hcurve ⊢
        nlinarith [mul_nonneg hcL.le
          (show 0 ≤ min 1 (((d / 2 : ℕ) : ℝ) /
            ((n : ℝ) * logAlphabet (d / 2))) by positivity)]
      _ ≤ _ := hR
  · have hd3 : d ≤ 3 := by omega
    obtain ⟨Q, hQ, hR⟩ := small_capacity_lower_padded hn hd epsilon he he' mu hmu T
    refine ⟨Q, hQ, ?_⟩
    have hc_le : c ≤ 1 / 12288 := min_le_right _ _
    have hcurve := curveRate_small_le hn hd hd3
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    calc
      c * curveRate n d ≤ (1 / 12288 : ℝ) * curveRate n d := by
        gcongr
        exact curveRate_nonneg_local hn hd
      _ ≤ (1 / 12288 : ℝ) * (3 / (n : ℝ)) := by gcongr
      _ = 1 / (4096 * (n : ℝ)) := by field_simp; ring
      _ ≤ _ := hR

end CausalSmith.Stat.DiscreteBudgetvalueCurve

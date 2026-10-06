module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.LowerPriorTransfer

/-! # Choosing the lower-experiment endpoint and amplitude

Roadmap (33), (40), and (45)--(48) optimize the supported sparse endpoint
and the legal dense amplitude. These bounds retain the explicit fixed-sample
shortage penalty; no testing or approximation conclusion is assumed.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

-- @node: sparse_fixedSample_calibrated_lower
/-- Choosing the endpoint in (33) gives the capped sparse rate in (40), whenever the intensity-dependent endpoint is at least two. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma sparse_fixedSample_calibrated_lower :
    ∃ (c η C : ℝ) (D : ℕ), 0 < c ∧ 0 < η ∧ 2 ≤ C ∧ 2 ≤ D ∧
      ∀ (n d : ℕ) (ε B : ℝ),
        1 ≤ n → D ≤ d → 0 < ε → ε ≤ 1 / 2 → 2 < B →
        2 ≤ η * d * lowerLogDegree C d / (B * n * ε) →
        c * min 1 (η * d / (B * n * ε * lowerLogDegree C d)) -
          Real.exp (-(n : ℝ) * (B - 2) ^ 2 / (4 * B)) ≤ minimaxRisk n d ε := by
  obtain ⟨c, η, C, D, hc, hη, hC, hD, hbound⟩ := sparse_fixedSample_minimaxRisk_lower
  refine ⟨c, η, C, D, hc, hη, hC, hD, ?_⟩
  intro n d ε B hn hd hε hεhi hB hband
  have hK := (lowerLogDegree_bounds hC (hD.trans hd)).1
  have hKpos : (0 : ℝ) < lowerLogDegree C d := by exact_mod_cast (by omega : 0 < lowerLogDegree C d)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hden : 0 < B * (n : ℝ) * ε := by positivity
  let M := min ((lowerLogDegree C d : ℝ) ^ 2)
    (η * d * lowerLogDegree C d / (B * n * ε))
  have hKtwo : (2 : ℝ) ≤ lowerLogDegree C d := by exact_mod_cast hK
  have hM : 2 ≤ M := le_min (by nlinarith) hband
  have hl := hbound n d ε M B hn hd hε hεhi hM
    (min_le_left _ _) hB (min_le_right _ _)
  have heq : M / (lowerLogDegree C d : ℝ) ^ 2 =
      min 1 (η * d / (B * n * ε * lowerLogDegree C d)) := by
    dsimp [M]
    rw [← min_div_div_right (sq_nonneg _)]
    congr 1
    · exact div_self (ne_of_gt (sq_pos_of_pos hKpos))
    · field_simp
  simpa only [mul_div_assoc, heq] using hl

-- @node: dense_fixedSample_calibrated_lower
/-- Taking the square root of the largest legal dense squared amplitude optimizes (48), including the amplitude cap needed for Bernoulli legality. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma dense_fixedSample_calibrated_lower :
    ∃ (η C : ℝ) (D : ℕ), 0 < η ∧ 2 ≤ C ∧ 2 ≤ D ∧
      ∀ (n d : ℕ) (ε B : ℝ),
        1 ≤ n → D ≤ d → 0 < ε → ε ≤ 1 / 2 → 2 < B →
        (5 / 2560000 : ℝ) *
          min (1 / (4 * (lowerLogDegree C d : ℝ) ^ 2))
            (η * d / (B * n * ε * lowerLogDegree C d)) -
          Real.exp (-(n : ℝ) * (B - 2) ^ 2 / (4 * B)) ≤ minimaxRisk n d ε := by
  obtain ⟨η, C, D, hη, hC, hD, hbound⟩ := dense_fixedSample_minimaxRisk_lower
  refine ⟨η, C, D, hη, hC, hD, ?_⟩
  intro n d ε B hn hd hε hεhi hB
  have hK := (lowerLogDegree_bounds hC (hD.trans hd)).1
  have hKpos : (0 : ℝ) < lowerLogDegree C d := by exact_mod_cast (by omega : 0 < lowerLogDegree C d)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hden : 0 < B * (n : ℝ) * ε := by positivity
  let q := min (1 / 4 : ℝ) (η * d * lowerLogDegree C d / (B * n * ε))
  have hq : 0 < q := lt_min (by norm_num) (by positivity)
  have hsquare : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq.le
  have hcap : Real.sqrt q ≤ 1 / 2 := by
    have hqcap : q ≤ 1 / 4 := min_le_left _ _
    nlinarith [Real.sqrt_nonneg q]
  have hband : (B * n * ε / d) * (Real.sqrt q) ^ 2 ≤ η * lowerLogDegree C d := by
    rw [hsquare]
    calc
      _ ≤ (B * n * ε / d) * (η * d * lowerLogDegree C d / (B * n * ε)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = _ := by field_simp
  have hl := hbound n d ε (Real.sqrt q) B hn hd hε hεhi
    (Real.sqrt_pos.2 hq) hcap hB hband
  have heq : q / (lowerLogDegree C d : ℝ) ^ 2 =
      min (1 / (4 * (lowerLogDegree C d : ℝ) ^ 2))
        (η * d / (B * n * ε * lowerLogDegree C d)) := by
    dsimp [q]
    rw [← min_div_div_right (sq_nonneg _)]
    congr 1 <;> field_simp
  simpa only [hsquare, mul_div_assoc, heq] using hl

end CausalSmith.Stat.OptvalueVanishingoverlapRate

module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.LowerRateCalibration

/-! # Splicing the sparse and dense lower experiments

The complementary endpoint ranges in roadmap (40) and (48) give one
large-alphabet lower bound. Different universal logarithmic degrees in the
two experiments are compared explicitly. The Poisson shortage penalty is
absorbed by a universal inflation, yielding the exact paper rate.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

-- @node: sparse_dense_fixedSample_spliced_lower
/-- The sparse packet experiment and the dense boundary experiment together cover every intensity, with a single positive lower constant and alphabet cutoff. This is the range splice in (40)--(48), before absorbing (49). In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma sparse_dense_fixedSample_spliced_lower :
    ∃ (c C : ℝ) (D : ℕ), 0 < c ∧ 2 ≤ C ∧ 2 ≤ D ∧
      ∀ (n d : ℕ) (ε B : ℝ),
        1 ≤ n → D ≤ d → 0 < ε → ε ≤ 1 / 2 → 2 < B →
        c * min 1 ((d : ℝ) / (B * n * ε * lowerLogDegree C d)) -
          Real.exp (-(n : ℝ) * (B - 2) ^ 2 / (4 * B)) ≤ minimaxRisk n d ε := by
  obtain ⟨cs, ηs, Cs, Ds, hcs, hηs, hCs, hDs, hs⟩ :=
    sparse_fixedSample_calibrated_lower
  obtain ⟨ηd, Cd, Dd, hηd, hCd, hDd, hdense⟩ :=
    dense_fixedSample_calibrated_lower
  let q := (Cd + 2) / Cs
  have hCspos : 0 < Cs := by linarith
  have hq : 0 < q := by dsimp [q]; positivity
  let b := min (ηs / (8 * q ^ 2)) (ηd / q)
  have hb : 0 < b := lt_min (by positivity) (by positivity)
  let c := min (cs * min 1 ηs) ((5 / 2560000 : ℝ) * b)
  have hc : 0 < c := lt_min (mul_pos hcs (lt_min (by norm_num) hηs)) (by positivity)
  refine ⟨c, Cs, max Ds Dd, hc, hCs, hDs.trans (le_max_left _ _), ?_⟩
  intro n d ε B hn hd hε hεhi hB
  have hds : Ds ≤ d := (le_max_left _ _).trans hd
  have hdd : Dd ≤ d := (le_max_right _ _).trans hd
  have hd2 := hDs.trans hds
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hBpos : 0 < B := by linarith
  let Ks : ℝ := lowerLogDegree Cs d
  let Kd : ℝ := lowerLogDegree Cd d
  have hKs : 0 < Ks := by
    have h := (lowerLogDegree_bounds hCs hd2).1
    dsimp [Ks]; exact_mod_cast (by omega : 0 < lowerLogDegree Cs d)
  have hKd : 0 < Kd := by
    have h := (lowerLogDegree_bounds hCd hd2).1
    dsimp [Kd]; exact_mod_cast (by omega : 0 < lowerLogDegree Cd d)
  have hdegrees : Kd ≤ q * Ks := by
    have hlo := (lowerLogDegree_bounds hCs hd2).2.1
    have hhi := (lowerLogDegree_bounds hCd hd2).2.2
    have hm := mul_le_mul_of_nonneg_left hlo hq.le
    have heq : q * (Cs * logAlphabet d) = (Cd + 2) * logAlphabet d := by
      dsimp [q]; field_simp
    rw [heq] at hm
    exact hhi.trans hm
  let x : ℝ := (d : ℝ) / (B * n * ε)
  have hx : 0 < x := by dsimp [x]; positivity
  have hrate : (d : ℝ) / (B * n * ε * lowerLogDegree Cs d) = x / Ks := by
    dsimp [x, Ks]; rw [div_div]
  rw [hrate]
  by_cases hband : 2 ≤ ηs * d * lowerLogDegree Cs d / (B * n * ε)
  · have hl := hs n d ε B hn hds hε hεhi hB hband
    have heq : ηs * d / (B * n * ε * lowerLogDegree Cs d) = ηs * (x / Ks) := by
      dsimp [x, Ks]; field_simp
    rw [heq] at hl
    have hmin : min 1 ηs * min 1 (x / Ks) ≤ min 1 (ηs * (x / Ks)) := by
      apply le_min
      · calc
          _ ≤ (1 : ℝ) * 1 := mul_le_mul (min_le_left 1 ηs) (min_le_left 1 (x / Ks))
            (le_min (by norm_num) (by positivity)) (by norm_num)
          _ = 1 := by ring
      · exact mul_le_mul (min_le_right _ _) (min_le_right _ _)
          (le_min (by norm_num) (by positivity)) hηs.le
    have hbound : c * min 1 (x / Ks) ≤ cs * min 1 (ηs * (x / Ks)) := by
      calc
        _ ≤ (cs * min 1 ηs) * min 1 (x / Ks) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
        _ = cs * (min 1 ηs * min 1 (x / Ks)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hmin hcs.le
    exact (sub_le_sub_right hbound _).trans hl
  · have hsmall : ηs * x * Ks ≤ 2 := by
      have hlt := le_of_lt (lt_of_not_ge hband)
      have heq : ηs * (d : ℝ) * lowerLogDegree Cs d / (B * n * ε) = ηs * x * Ks := by
        dsimp [x, Ks]; field_simp
      rwa [heq] at hlt
    have hl := hdense n d ε B hn hdd hε hεhi hB
    have heq : ηd * d / (B * n * ε * lowerLogDegree Cd d) = ηd * x / Kd := by
      dsimp [x, Kd]; field_simp
    rw [heq] at hl
    have hcap : b * (x / Ks) ≤ 1 / (4 * Kd ^ 2) := by
      have hsq : Kd ^ 2 ≤ q ^ 2 * Ks ^ 2 := by
        have h := pow_le_pow_left₀ hKd.le hdegrees 2
        simpa only [mul_pow] using h
      have hbcap : b ≤ ηs / (8 * q ^ 2) := min_le_left _ _
      have hprod : (ηs / (8 * q ^ 2)) * (x / Ks) * (4 * Kd ^ 2) ≤ 1 := by
        calc
          _ ≤ (ηs / (8 * q ^ 2)) * (x / Ks) * (4 * (q ^ 2 * Ks ^ 2)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (by norm_num))
              (by positivity)
          _ = ηs * x * Ks / 2 := by field_simp; ring
          _ ≤ 1 := by linarith
      apply (le_div_iff₀ (by positivity : 0 < 4 * Kd ^ 2)).2
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hbcap (by positivity)) (by positivity)).trans hprod
    have hlinear : b * (x / Ks) ≤ ηd * x / Kd := by
      have hblinear : b ≤ ηd / q := min_le_right _ _
      calc
        _ ≤ (ηd / q) * (x / Ks) := mul_le_mul_of_nonneg_right hblinear (by positivity)
        _ = ηd * x / (q * Ks) := by field_simp
        _ ≤ ηd * x / Kd := div_le_div_of_nonneg_left (by positivity) hKd hdegrees
    have hbound : c * min 1 (x / Ks) ≤
        (5 / 2560000 : ℝ) * min (1 / (4 * Kd ^ 2)) (ηd * x / Kd) := by
      calc
        _ ≤ ((5 / 2560000 : ℝ) * b) * min 1 (x / Ks) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
        _ ≤ ((5 / 2560000 : ℝ) * b) * (x / Ks) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
        _ = (5 / 2560000 : ℝ) * (b * (x / Ks)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_min hcap hlinear) (by norm_num)
    exact (sub_le_sub_right hbound _).trans hl

-- @node: largeAlphabet_lower_with_shortage
/-- Comparing the rounded degree with the paper logarithm converts the spliced bound to the exact capped rate, uniformly in the inflation B. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma largeAlphabet_lower_with_shortage :
    ∃ (c : ℝ) (D : ℕ), 0 < c ∧ 2 ≤ D ∧
      ∀ (n d : ℕ) (ε B : ℝ),
        1 ≤ n → D ≤ d → 0 < ε → ε ≤ 1 / 2 → 2 < B →
        (c / B) * rateScale n d ε -
          Real.exp (-(n : ℝ) * (B - 2) ^ 2 / (4 * B)) ≤ minimaxRisk n d ε := by
  obtain ⟨c, C, D, hc, hC, hD, hl⟩ := sparse_dense_fixedSample_spliced_lower
  refine ⟨c / (C + 2), D, by positivity, hD, ?_⟩
  intro n d ε B hn hd hε hεhi hB
  have hd2 := hD.trans hd
  have hL := logAlphabet_pos (by omega : 1 ≤ d)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hBpos : 0 < B := by linarith
  have hKpos : (0 : ℝ) < lowerLogDegree C d := by
    have h := (lowerLogDegree_bounds hC hd2).1
    exact_mod_cast (by omega : 0 < lowerLogDegree C d)
  let r := (d : ℝ) / (n * ε * logAlphabet d)
  let a := 1 / (B * (C + 2))
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    apply (div_le_iff₀ (by positivity : 0 < B * (C + 2))).2
    nlinarith
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hratio : a * r ≤ (d : ℝ) / (B * n * ε * lowerLogDegree C d) := by
    have hdegree := (lowerLogDegree_bounds hC hd2).2.2
    calc
      _ = (d : ℝ) / (B * n * ε * ((C + 2) * logAlphabet d)) := by
        dsimp [a, r]; field_simp
      _ ≤ _ := div_le_div_of_nonneg_left (Nat.cast_nonneg d) (by positivity)
        (mul_le_mul_of_nonneg_left hdegree (by positivity))
  have hmin : a * min 1 r ≤ min 1 ((d : ℝ) / (B * n * ε * lowerLogDegree C d)) := by
    apply le_min
    · exact (mul_le_mul_of_nonneg_left (min_le_left _ _) ha.le).trans
        (by simpa using ha1)
    · exact (mul_le_mul_of_nonneg_left (min_le_right _ _) ha.le).trans hratio
  have hbound : (c / (C + 2) / B) * rateScale n d ε ≤
      c * min 1 ((d : ℝ) / (B * n * ε * lowerLogDegree C d)) := by
    calc
      _ = c * (a * min 1 r) := by dsimp [a, r, rateScale]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hmin hc.le
  exact (sub_le_sub_right hbound _).trans (hl n d ε B hn hd hε hεhi hB)

-- @node: shortageExponential_le_inverse_inflation_sq
/-- Squaring the inverse-inflation exponential bound makes the shortage penalty negligible compared with the lower constant's 1/B scaling. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hB,hn), the [stated conclusion](goal) holds. -/
lemma shortageExponential_le_inverse_inflation_sq {B : ℝ} (hB : 4 ≤ B)
    {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-(n : ℝ) * (B - 2) ^ 2 / (4 * B)) ≤ 1024 / (B ^ 2 * n) := by
  have hBpos : 0 < B := by linarith
  let a := (B - 2) ^ 2 / (8 * B)
  have ha : B / 32 ≤ a := by
    dsimp [a]
    apply (le_div_iff₀ (by positivity : 0 < 8 * B)).2
    nlinarith
  have hδ : 0 < 32 / B := by positivity
  have hcoef : 1 / (32 / B) ≤ a := by simpa using ha
  have hfirst := shortageExponential_le_inverse_sample hn hδ hcoef
  have hsecond := shortageExponential_le_inverse_sample (n := 1) (by omega) hδ hcoef
  simp only [Nat.cast_one, mul_one, div_one] at hsecond
  have hmono : Real.exp (-a * (n : ℝ)) ≤ Real.exp (-a) := by
    apply Real.exp_le_exp.mpr
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have ha0 : 0 ≤ a := (by positivity : 0 ≤ B / 32).trans ha
    nlinarith
  calc
    _ = Real.exp (-a * (n : ℝ)) * Real.exp (-a * (n : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [a]; ring
    _ ≤ (32 / B / n) * (32 / B) :=
      mul_le_mul hfirst (hmono.trans hsecond) (Real.exp_nonneg _) (by positivity)
    _ = _ := by ring

-- @node: largeAlphabet_minimaxRisk_lower
/-- One universal inflation absorbs the Poisson shortage penalty, completing the large-alphabet fixed-sample lower bound in the exact paper rate. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma largeAlphabet_minimaxRisk_lower :
    ∃ (c : ℝ) (D : ℕ), 0 < c ∧ 2 ≤ D ∧
      ∀ (n d : ℕ) (ε : ℝ),
        1 ≤ n → D ≤ d → 0 < ε → ε ≤ 1 / 2 →
        c * rateScale n d ε ≤ minimaxRisk n d ε := by
  obtain ⟨c, D, hc, hD, hl⟩ := largeAlphabet_lower_with_shortage
  let B := max 4 (2048 / c)
  have hB4 : 4 ≤ B := le_max_left _ _
  have hB : 2 < B := by linarith
  have hBpos : 0 < B := by linarith
  have hBc : 2048 ≤ B * c := (div_le_iff₀ hc).mp (le_max_right _ _)
  refine ⟨c / (2 * B), D, by positivity, hD, ?_⟩
  intro n d ε hn hd hε hεhi
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hL := logAlphabet_pos hd1
  have hLhi : logAlphabet d ≤ d := by
    have hlog := Real.log_le_sub_one_of_pos hdpos
    rw [logAlphabet, Real.log_mul (Real.exp_pos _).ne' hdpos.ne', Real.log_exp]
    linarith
  have hrate : 1 / (n : ℝ) ≤ rateScale n d ε := by
    apply le_min
    · exact (div_le_one hnpos).2 (by exact_mod_cast hn)
    · apply (div_le_div_iff₀ hnpos (by positivity : 0 < (n : ℝ) * ε * logAlphabet d)).2
      have he : ε ≤ 1 := by linarith
      have hprod : ε * logAlphabet d ≤ d :=
        (mul_le_mul_of_nonneg_right he hL.le).trans (by simpa using hLhi)
      nlinarith
  have hpenalty : Real.exp (-(n : ℝ) * (B - 2) ^ 2 / (4 * B)) ≤
      (c / (2 * B)) * rateScale n d ε := by
    calc
      _ ≤ 1024 / (B ^ 2 * n) := shortageExponential_le_inverse_inflation_sq hB4 hn
      _ ≤ (c / (2 * B)) * (1 / n) := by
        apply (div_le_iff₀ (by positivity : 0 < B ^ 2 * (n : ℝ))).2
        have heq : (c / (2 * B) * (1 / (n : ℝ))) * (B ^ 2 * n) = B * c / 2 := by
          field_simp
        rw [heq]
        linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hrate (by positivity)
  have hbound := hl n d ε B hn hd hε hεhi hB
  have heq : c / B = 2 * (c / (2 * B)) := by ring
  rw [heq] at hbound
  linarith

end CausalSmith.Stat.OptvalueVanishingoverlapRate

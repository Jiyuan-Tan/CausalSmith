module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.PacketSmoothRemainder
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Angular regularity for weighted Jackson approximation

The remainder in roadmap (10) is uniformly Lipschitz in the square-root
intensity coordinate. The half-angle identity then gives the sqrt(M)
angular Lipschitz bound needed for the weighted upper approximation (14).
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate


-- @node: weightedLowerBranch_sqrt_lipschitz
/-- Clipping the lower quadratic branch confines its slope to [-2,0]. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hx,hxy), the [stated conclusion](goal) holds. -/
lemma weightedLowerBranch_sqrt_lipschitz {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    |max (1 - x ^ 2) 0 - max (1 - y ^ 2) 0| ≤ 2 * (y - x) := by
  have hy : 0 ≤ y := hx.trans hxy
  by_cases hy1 : y ≤ 1
  · have hx1 : x ≤ 1 := hxy.trans hy1
    rw [max_eq_left (by nlinarith : 0 ≤ 1 - x ^ 2),
      max_eq_left (by nlinarith : 0 ≤ 1 - y ^ 2),
      abs_of_nonneg (by nlinarith : 0 ≤ (1 - x ^ 2) - (1 - y ^ 2))]
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (by linarith : 0 ≤ 2 - x - y)]
  · rw [max_eq_right (by nlinarith : 1 - y ^ 2 ≤ 0), sub_zero,
      abs_of_nonneg (le_max_right _ _)]
    by_cases hx1 : x ≤ 1
    · rw [max_eq_left (by nlinarith : 0 ≤ 1 - x ^ 2)]
      nlinarith [sq_nonneg (1 - x)]
    · rw [max_eq_right (by nlinarith : 1 - x ^ 2 ≤ 0)]
      linarith


-- @node: weightedUpperBranch_sqrt_lipschitz
/-- The clipped rational upper branch has slope bounded by two in the square-root intensity coordinate, including intervals crossing the kink. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hx,hxy), the [stated conclusion](goal) holds. -/
lemma weightedUpperBranch_sqrt_lipschitz {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    |max (x ^ 2 - 1) 0 / (1 + x ^ 2) -
      max (y ^ 2 - 1) 0 / (1 + y ^ 2)| ≤ 2 * (y - x) := by
  have hy : 0 ≤ y := hx.trans hxy
  have hdx : 0 < 1 + x ^ 2 := by positivity
  have hdy : 0 < 1 + y ^ 2 := by positivity
  by_cases hx1 : 1 ≤ x
  · have hy1 : 1 ≤ y := hx1.trans hxy
    rw [max_eq_left (by nlinarith : 0 ≤ x ^ 2 - 1),
      max_eq_left (by nlinarith : 0 ≤ y ^ 2 - 1)]
    have he : (x ^ 2 - 1) / (1 + x ^ 2) - (y ^ 2 - 1) / (1 + y ^ 2) =
        -(2 * (y - x) * (x + y) / ((1 + x ^ 2) * (1 + y ^ 2))) := by
      field_simp
      ring
    rw [he, abs_neg, abs_of_nonneg (by positivity)]
    apply (div_le_iff₀ (mul_pos hdx hdy)).mpr
    have hb : x + y ≤ (1 + x ^ 2) * (1 + y ^ 2) := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1),
        mul_nonneg (sq_nonneg x) (sq_nonneg y)]
    nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * (y - x))
      (sub_nonneg.mpr hb)]
  · rw [max_eq_right (by nlinarith : x ^ 2 - 1 ≤ 0), zero_div, zero_sub, abs_neg,
      abs_of_nonneg (div_nonneg (le_max_right _ _) hdy.le)]
    by_cases hy1 : 1 ≤ y
    · rw [max_eq_left (by nlinarith : 0 ≤ y ^ 2 - 1)]
      apply (div_le_iff₀ hdy).mpr
      have h1 : y + 1 ≤ 2 * (1 + y ^ 2) := by nlinarith [sq_nonneg (y - 1)]
      have h2 := mul_nonneg (by linarith : 0 ≤ y - 1) (sub_nonneg.mpr h1)
      have h3 := mul_nonneg (by linarith : 0 ≤ 1 - x) hdy.le
      nlinarith
    · rw [max_eq_right (by nlinarith : y ^ 2 - 1 ≤ 0), zero_div]
      linarith


-- @node: packetRemainder_sqrt_lipschitz
/-- The nonlinear remainder has a universal Lipschitz constant in sqrt(z), uniform over the entire closed overlap interval. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hεhi,hx,hy), the [stated conclusion](goal) holds. -/
lemma packetRemainder_sqrt_lipschitz {ε x y : ℝ}
    (hε : 0 ≤ ε) (hεhi : ε ≤ 1 / 2) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |packetRemainder ε (x ^ 2) - packetRemainder ε (y ^ 2)| ≤ 2 * |x - y| := by
  have ordered (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
      |packetRemainder ε (x ^ 2) - packetRemainder ε (y ^ 2)| ≤ 2 * (y - x) := by
    have hl := weightedLowerBranch_sqrt_lipschitz hx hxy
    have hu := weightedUpperBranch_sqrt_lipschitz hx hxy
    have he : packetRemainder ε (x ^ 2) - packetRemainder ε (y ^ 2) =
        ε * (max (1 - x ^ 2) 0 - max (1 - y ^ 2) 0) +
        (1 - 2 * ε) * (max (x ^ 2 - 1) 0 / (1 + x ^ 2) -
          max (y ^ 2 - 1) 0 / (1 + y ^ 2)) := by
      unfold packetRemainder
      ring
    rw [he]
    calc
      _ ≤ |ε * (max (1 - x ^ 2) 0 - max (1 - y ^ 2) 0)| +
          |(1 - 2 * ε) * (max (x ^ 2 - 1) 0 / (1 + x ^ 2) -
            max (y ^ 2 - 1) 0 / (1 + y ^ 2))| := abs_add_le _ _
      _ ≤ ε * (2 * (y - x)) + (1 - 2 * ε) * (2 * (y - x)) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hε, abs_of_nonneg (by linarith : 0 ≤ 1 - 2 * ε)]
        exact add_le_add (mul_le_mul_of_nonneg_left hl hε)
          (mul_le_mul_of_nonneg_left hu (by linarith))
      _ ≤ 2 * (y - x) := by nlinarith
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    simpa only [neg_sub] using ordered x y hx hxy
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact ordered y x hy hyx


-- @node: packetRemainder_angular_lipschitz
/-- The half-angle coordinate gives the uniform angular regularity asserted before roadmap (14), without differentiability at either kink. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM,hε,hεhi), the [stated conclusion](goal) holds. -/
lemma packetRemainder_angular_lipschitz {M ε : ℝ} (hM : 0 ≤ M)
    (hε : 0 ≤ ε) (hεhi : ε ≤ 1 / 2) (s t : ℝ) :
    |packetRemainder ε (packetIntensity M s) -
      packetRemainder ε (packetIntensity M t)| ≤ Real.sqrt M * |s - t| := by
  have he (u : ℝ) : (Real.sqrt M * |Real.cos (u / 2)|) ^ 2 = packetIntensity M u := by
    rw [mul_pow, Real.sq_sqrt hM, sq_abs]
    have hc := Real.cos_two_mul (u / 2)
    rw [show 2 * (u / 2) = u by ring] at hc
    unfold packetIntensity
    nlinarith
  have h := packetRemainder_sqrt_lipschitz hε hεhi
    (by positivity : 0 ≤ Real.sqrt M * |Real.cos (s / 2)|)
    (by positivity : 0 ≤ Real.sqrt M * |Real.cos (t / 2)|)
  rw [he s, he t] at h
  calc
    _ ≤ 2 * abs (Real.sqrt M * |Real.cos (s / 2)| - Real.sqrt M * |Real.cos (t / 2)|) := h
    _ = 2 * Real.sqrt M * abs (|Real.cos (s / 2)| - |Real.cos (t / 2)|) := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg M)]
      ring
    _ ≤ 2 * Real.sqrt M * |Real.cos (s / 2) - Real.cos (t / 2)| :=
      mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub _ _) (by positivity)
    _ ≤ 2 * Real.sqrt M * |s / 2 - t / 2| :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_sub_cos_le _ _) (by positivity)
    _ = Real.sqrt M * |s - t| := by
      rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring

end CausalSmith.Stat.OptvalueVanishingoverlapRate

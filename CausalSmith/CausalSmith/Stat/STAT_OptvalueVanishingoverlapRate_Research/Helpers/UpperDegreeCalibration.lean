module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperFactorial
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Universal Jackson degree calibration

Roadmap equation (27) chooses a universal small degree coefficient so the
linear and quadratic exponential growth in (26) costs only d^(1/16).
The additive degree floor contributes a universal multiplicative constant.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate


-- @node: jacksonDegree_le_two_add
/-- The degree floor costs at most two in addition to the tuned logarithmic degree. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hκ,hL), the [stated conclusion](goal) holds. -/
lemma jacksonDegree_le_two_add {κ : ℝ} {d : ℕ} (hκ : 0 ≤ κ)
    (hL : 0 ≤ logAlphabet d) :
    (jacksonDegree κ d : ℝ) ≤ 2 + κ * logAlphabet d := by
  have hf := Nat.floor_le (mul_nonneg hκ hL)
  rw [jacksonDegree, Nat.cast_max]
  exact max_le (by norm_num; exact mul_nonneg hκ hL) (by linarith)


-- @node: jacksonDegree_ge_half_log
/-- The degree floor and minimum degree two retain at least half the tuned logarithmic degree, uniformly without a large-alphabet cutoff. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma jacksonDegree_ge_half_log (κ : ℝ) (d : ℕ) :
    κ / 2 * logAlphabet d ≤ (jacksonDegree κ d : ℝ) := by
  have hf := Nat.lt_floor_add_one (κ * logAlphabet d)
  have htwo : (2 : ℝ) ≤ jacksonDegree κ d := by
    exact_mod_cast (le_max_left 2 ⌊κ * logAlphabet d⌋₊)
  have hfloor : (⌊κ * logAlphabet d⌋₊ : ℝ) ≤ jacksonDegree κ d := by
    exact_mod_cast (le_max_right 2 ⌊κ * logAlphabet d⌋₊)
  by_cases hsmall : κ * logAlphabet d ≤ 4
  · linarith
  · linarith


-- @node: degree_exponent_le
/-- A logarithmic degree bound controls the quadratic exponent without a log n term. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hC₁,hC₂,hL,hK,hdegree,htune), the [stated conclusion](goal) holds. -/
lemma degree_exponent_le {C₁ C₂ κ L K : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hL : 1 ≤ L)
    (hK : 0 ≤ K) (hdegree : K ≤ 2 + κ * L)
    (htune : C₁ * κ + 2 * C₂ * κ ^ 2 ≤ 1 / 16) :
    C₁ * K + C₂ * K ^ 2 / L ≤ 2 * C₁ + 8 * C₂ + L / 16 := by
  have hLp : 0 < L := by linarith
  have hsq : K ^ 2 ≤ 8 + 2 * κ ^ 2 * L ^ 2 := by
    have h := pow_le_pow_left₀ hK hdegree 2
    nlinarith [sq_nonneg (2 - κ * L)]
  have hlin := mul_le_mul_of_nonneg_left hdegree hC₁
  have hquad := mul_le_mul_of_nonneg_left hsq hC₂
  have ht := mul_le_mul_of_nonneg_right htune hLp.le
  apply (mul_le_mul_iff_right₀ hLp).mp
  have he : (C₁ * K + C₂ * K ^ 2 / L) * L = C₁ * K * L + C₂ * K ^ 2 := by
    field_simp
  rw [mul_comm L (C₁ * K + C₂ * K ^ 2 / L), he]
  have hl := mul_le_mul_of_nonneg_right hlin hLp.le
  have ht₂ := mul_le_mul_of_nonneg_right ht hLp.le
  have hc₂ := mul_le_mul_of_nonneg_left hL (show 0 ≤ 8 * C₂ by positivity)
  nlinarith


-- @node: degree_tuning_exists
/-- One universal positive tuning coefficient suffices for any fixed nonnegative linear and quadratic moment-growth constants. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hC₁,hC₂), the [stated conclusion](goal) holds. -/
lemma degree_tuning_exists (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ κ : ℝ, 0 < κ ∧ C₁ * κ + 2 * C₂ * κ ^ 2 ≤ 1 / 16 := by
  let B := C₁ + 2 * C₂ + 1
  have hB : 0 < B := by dsimp [B]; linarith
  let κ := 1 / (32 * B)
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκ1 : κ ≤ 1 := by
    dsimp [κ]
    apply (div_le_iff₀ (by positivity : 0 < 32 * B)).2
    dsimp [B]
    linarith
  have he : B * κ = 1 / 32 := by dsimp [κ]; field_simp
  refine ⟨κ, hκ, ?_⟩
  have hs : κ ^ 2 ≤ κ := by nlinarith
  have hq := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * C₂ by positivity)
  dsimp [B] at he
  nlinarith


-- @node: jacksonDegree_exponential_growth_le
/-- The tuned Jackson degree has at most d^(1/16) exponential moment inflation, with a universal prefactor, as in roadmap (27). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hC₁,hC₂), the [stated conclusion](goal) holds. -/
lemma jacksonDegree_exponential_growth_le (C₁ C₂ : ℝ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ κ A : ℝ, 0 < κ ∧ 0 < A ∧ ∀ {d : ℕ}, 1 ≤ d →
      Real.exp (C₁ * jacksonDegree κ d + C₂ * (jacksonDegree κ d : ℝ) ^ 2 /
        logAlphabet d) ≤ A * (d : ℝ) ^ (1 / 16 : ℝ) := by
  obtain ⟨κ, hκ, htune⟩ := degree_tuning_exists C₁ C₂ hC₁ hC₂
  refine ⟨κ, Real.exp (2 * C₁ + 8 * C₂ + 1 / 16), hκ, Real.exp_pos _, ?_⟩
  intro d hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog : logAlphabet d = 1 + Real.log d := by
    rw [logAlphabet, Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt hd0), Real.log_exp]
  have hL : 1 ≤ logAlphabet d := by rw [hlog]; linarith [Real.log_nonneg hd1]
  have hex := degree_exponent_le hC₁ hC₂ hL (Nat.cast_nonneg _)
    (jacksonDegree_le_two_add hκ.le (by linarith)) htune
  calc
    _ ≤ Real.exp (2 * C₁ + 8 * C₂ + logAlphabet d / 16) := Real.exp_le_exp.mpr hex
    _ = _ := by
      rw [hlog, Real.rpow_def_of_pos hd0, ← Real.exp_add]
      congr 1
      ring

end CausalSmith.Stat.OptvalueVanishingoverlapRate

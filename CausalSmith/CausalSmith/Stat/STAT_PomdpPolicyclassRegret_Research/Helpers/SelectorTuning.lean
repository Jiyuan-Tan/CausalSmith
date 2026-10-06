module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Basic

/-!
# Block count and adaptive depth tuning

Arithmetic ingredients of equations (15)--(17) in the observable-selector
roadmap: odd block counts, logarithmic comparison, usable block length, and
the floor bounds for the uncapped adaptive depth.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open CausalSmith.Stat.PomdpLatentOverlapMinimax

/-- The block count is at least three. For [the candidate-policy count](hyp:M), this establishes
[the selector num blocks ge three result](goal). -/
-- @node: selector_numBlocks_ge_three
lemma selector_numBlocks_ge_three (M : Nat) : 3 ≤ numBlocks M := by
  unfold numBlocks
  dsimp only
  split <;> omega

/-- The median uses an odd number of blocks. For [the candidate-policy count](hyp:M), this
establishes [the selector num blocks odd result](goal). -/
-- @node: selector_numBlocks_odd
lemma selector_numBlocks_odd (M : Nat) : numBlocks M % 2 = 1 := by
  unfold numBlocks
  dsimp only
  split <;> omega

/-- Rounding to the next odd integer adds at most one block. For
[the candidate-policy count](hyp:M), this establishes
[the selector num blocks rounding result](goal). -/
-- @node: selector_numBlocks_rounding
lemma selector_numBlocks_rounding (M : Nat) :
    max 3 (Nat.ceil (Real.log (2 * M : ℝ))) ≤ numBlocks M ∧
    numBlocks M ≤ max 3 (Nat.ceil (Real.log (2 * M : ℝ))) + 1 := by
  unfold numBlocks
  dsimp only
  split <;> omega

/-- The block count dominates the logarithm needed for the median tail bound. For
[the candidate-policy count](hyp:M), this establishes
[the selector log two mul bound num blocks result](goal). -/
-- @node: selector_log_two_mul_le_numBlocks
lemma selector_log_two_mul_le_numBlocks (M : Nat) :
    Real.log (2 * M : ℝ) ≤ (numBlocks M : ℝ) := by
  calc
    _ ≤ (Nat.ceil (Real.log (2 * M : ℝ)) : ℝ) := Nat.le_ceil _
    _ ≤ (max 3 (Nat.ceil (Real.log (2 * M : ℝ))) : Nat) := by
      exact_mod_cast Nat.le_max_right _ _
    _ ≤ (numBlocks M : ℝ) := by
      exact_mod_cast (selector_numBlocks_rounding M).1

/-- Equation (17), with an explicit universal logarithmic constant. For
[the candidate-policy count](hyp:M) and [the candidate-policy count assumption](hyp:hM), this
establishes [the selector num blocks log bounds result](goal). -/
-- @node: selector_numBlocks_log_bounds
lemma selector_numBlocks_log_bounds (M : Nat) (hM : 2 ≤ M) :
    Real.log (M : ℝ) ≤ (numBlocks M : ℝ) ∧
    (numBlocks M : ℝ) ≤ (2 + 4 / Real.log 2) * Real.log (M : ℝ) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogM : Real.log (2 : ℝ) ≤ Real.log (M : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hM)
  have hlog : Real.log (2 * M : ℝ) = Real.log 2 + Real.log (M : ℝ) :=
    Real.log_mul (by norm_num) hMpos.ne'
  have hnonneg : 0 ≤ Real.log (2 * M : ℝ) := by rw [hlog]; linarith
  have hceil := Nat.ceil_lt_add_one hnonneg
  have hround : (numBlocks M : ℝ) ≤
      (max 3 (Nat.ceil (Real.log (2 * M : ℝ))) : Nat) + 1 := by
    exact_mod_cast (selector_numBlocks_rounding M).2
  have hB : (numBlocks M : ℝ) ≤ 2 * Real.log (M : ℝ) + 4 := by
    rcases le_total 3 (Nat.ceil (Real.log (2 * M : ℝ))) with h | h
    · rw [max_eq_right h] at hround
      rw [hlog] at hceil hround
      linarith
    · rw [max_eq_left h] at hround
      have hroundR : (numBlocks M : ℝ) ≤ 4 := by exact_mod_cast hround
      linarith
  have hfour : 4 ≤ (4 / Real.log 2) * Real.log (M : ℝ) := by
    calc
      4 = (4 / Real.log 2) * Real.log 2 := by field_simp
      _ ≤ (4 / Real.log 2) * Real.log (M : ℝ) :=
        mul_le_mul_of_nonneg_left hlogM (by positivity)
  constructor
  · have := selector_log_two_mul_le_numBlocks M
    rw [hlog] at this
    linarith
  · nlinarith

/-- Truncating a depth at half a block leaves at least half its observations. For
[the sample size](hyp:n), [the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta), and
[the latent-overlap radius](hyp:C), this establishes
[the selector adaptive depth half result](goal). -/
-- @node: selector_adaptiveDepth_half
lemma selector_adaptiveDepth_half (n : Nat) (t0 zeta C : ℝ) :
    2 * adaptiveDepth n t0 zeta C ≤ n := by
  unfold adaptiveDepth
  split
  · omega
  · have := Nat.min_le_left (n / 2)
      (Int.toNat ⌊Real.log ((n : ℝ) * overlapRadius C ^ 2) /
        (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta))⌋)
    omega

/-- The usable length in the moment theorem is positive and at least half a block. For
[the sample size](hyp:n), [the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), and [the sample size assumption](hyp:hn), this establishes
[the selector adaptive depth usable result](goal). -/
-- @node: selector_adaptiveDepth_usable
lemma selector_adaptiveDepth_usable (n : Nat) (t0 zeta C : ℝ) (hn : 0 < n) :
    0 < n - adaptiveDepth n t0 zeta C ∧
    (n : ℝ) / 2 ≤ (n - adaptiveDepth n t0 zeta C : Nat) := by
  have hk := selector_adaptiveDepth_half n t0 zeta C
  constructor
  · omega
  · have hkn : adaptiveDepth n t0 zeta C ≤ n := by omega
    rw [Nat.cast_sub hkn]
    have hkr : 2 * (adaptiveDepth n t0 zeta C : ℝ) ≤ n := by exact_mod_cast hk
    linarith

/-- The logarithmic tuning denominator agrees with the regime parameters. For
[the mixing scale](hyp:t0) and [the policy-overlap scale](hyp:zeta), this establishes
[the selector tuning denominator result](goal). -/
-- @node: selector_tuning_denominator
lemma selector_tuning_denominator (t0 zeta : ℝ) :
    2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta) =
      2 / t0 + zeta := by
  simp [mixingAlpha, policyFactor, one_div, Real.log_inv, Real.log_exp]
  ring

/-- A positive tuning denominator makes the logarithmic floor well posed. For
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the mixing scale assumption](hyp:ht0), and [the policy-overlap scale assumption](hyp:hzeta),
this establishes [the selector tuning denominator positivity result](goal). -/
-- @node: selector_tuning_denominator_pos
lemma selector_tuning_denominator_pos (t0 zeta : ℝ) (ht0 : 0 < t0)
    (hzeta : 0 < zeta) :
    0 < 2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta) := by
  rw [selector_tuning_denominator]
  positivity

/-- The logarithmic bias exponent is exactly the paper's half-rate exponent. For
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the mixing scale assumption](hyp:ht0), and [the policy-overlap scale assumption](hyp:hzeta),
this establishes [the selector tuning rate identity result](goal). -/
-- @node: selector_tuning_rate_identity
lemma selector_tuning_rate_identity (t0 zeta : ℝ) (ht0 : 0 < t0)
    (hzeta : 0 < zeta) :
    Real.log (1 / mixingAlpha t0) /
      (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta)) =
        rateExponent t0 zeta / 2 := by
  rw [selector_tuning_denominator]
  have hden : 2 + t0 * zeta ≠ 0 := by positivity
  simp only [mixingAlpha, one_div, Real.log_inv, Real.log_exp, neg_neg, rateExponent]
  field_simp

/-- In the low-radius branch the prescribed depth is zero, as in equation (14). For
[the sample size](hyp:n), [the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), and [the small assumption](hyp:hsmall), this establishes
[the selector adaptive depth zero result](goal). -/
-- @node: selector_adaptiveDepth_zero
lemma selector_adaptiveDepth_zero (n : Nat) (t0 zeta C : ℝ)
    (hsmall : (n : ℝ) * overlapRadius C ^ 2 ≤ 1) :
    adaptiveDepth n t0 zeta C = 0 := by
  exact if_pos hsmall

/-- An inactive cap gives the two floor inequalities used in equation (15). For
[the sample size](hyp:n), [the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta), [the large assumption](hyp:hlarge), and
[the cap assumption](hyp:hcap), this establishes
[the selector adaptive depth floor bounds result](goal). -/
-- @node: selector_adaptiveDepth_floor_bounds
lemma selector_adaptiveDepth_floor_bounds (n : Nat) (t0 zeta C : ℝ)
    (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hlarge : 1 < (n : ℝ) * overlapRadius C ^ 2)
    (hcap : Real.log ((n : ℝ) * overlapRadius C ^ 2) /
      (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta)) ≤
        (n / 2 : Nat)) :
    let r := Real.log ((n : ℝ) * overlapRadius C ^ 2) /
      (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta))
    r - 1 ≤ (adaptiveDepth n t0 zeta C : ℝ) ∧
      (adaptiveDepth n t0 zeta C : ℝ) ≤ r := by
  let r := Real.log ((n : ℝ) * overlapRadius C ^ 2) /
    (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta))
  have hr : 0 ≤ r := (div_pos (Real.log_pos hlarge)
    (selector_tuning_denominator_pos t0 zeta ht0 hzeta)).le
  have hfloor : (Int.toNat ⌊r⌋ : ℝ) ≤ r := by
    rw [Int.floor_toNat]
    exact Nat.floor_le hr
  have hfloorcap : Int.toNat ⌊r⌋ ≤ n / 2 := by
    exact_mod_cast hfloor.trans hcap
  have hk : adaptiveDepth n t0 zeta C = Int.toNat ⌊r⌋ := by
    rw [adaptiveDepth, if_neg (not_le.mpr hlarge)]
    exact Nat.min_eq_right hfloorcap
  rw [hk]
  constructor
  · have hlower := Nat.lt_floor_add_one r
    rw [← Int.floor_toNat] at hlower
    linarith
  · exact hfloor

/-- Exponentiating the lower floor bound gives the bias part of equation (15). The power of the
combined coordinate is kept factored for downstream use. For [the sample size](hyp:n),
[the history length](hyp:k), [the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta), [the large assumption](hyp:hlarge), and
[the history length assumption](hyp:hk), this establishes
[the selector depth bias power bound result](goal). -/
-- @node: selector_depth_bias_power_le
lemma selector_depth_bias_power_le (n k : Nat) (t0 zeta C : ℝ)
    (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hlarge : 1 < (n : ℝ) * overlapRadius C ^ 2)
    (hk : Real.log ((n : ℝ) * overlapRadius C ^ 2) /
      (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta)) - 1 ≤
        (k : ℝ)) :
    mixingAlpha t0 ^ k ≤ (mixingAlpha t0)⁻¹ *
      ((n : ℝ) * overlapRadius C ^ 2) ^ (-(rateExponent t0 zeta / 2)) := by
  have hα : 0 < mixingAlpha t0 := Real.exp_pos _
  have hα1 : mixingAlpha t0 ≤ 1 := by
    unfold mixingAlpha
    exact (Real.exp_le_one_iff).mpr (neg_nonpos.mpr (by positivity))
  have hx : 0 < (n : ℝ) * overlapRadius C ^ 2 := by linarith
  have hlog : Real.log (mixingAlpha t0) = -Real.log (1 / mixingAlpha t0) := by
    rw [one_div, Real.log_inv, neg_neg]
  have hmono := Real.rpow_le_rpow_of_exponent_ge hα hα1 hk
  rw [Real.rpow_natCast] at hmono
  refine hmono.trans_eq ?_
  have hinv : (mixingAlpha t0)⁻¹ = Real.exp (-Real.log (mixingAlpha t0)) := by
    rw [Real.exp_neg, Real.exp_log hα]
  rw [Real.rpow_def_of_pos hα, Real.rpow_def_of_pos hx, hinv, ← Real.exp_add]
  congr 1
  rw [hlog, ← selector_tuning_rate_identity t0 zeta ht0 hzeta]
  ring

/-- Exponentiating the upper floor bound gives the variance-growth factor in equation (15). For
[the sample size](hyp:n), [the history length](hyp:k), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the policy-overlap scale assumption](hyp:hzeta), [the large assumption](hyp:hlarge), and
[the history length assumption](hyp:hk), this establishes
[the selector depth variance power bound result](goal). -/
-- @node: selector_depth_variance_power_le
lemma selector_depth_variance_power_le (n k : Nat) (t0 zeta C : ℝ)
    (hzeta : 0 < zeta) (hlarge : 1 < (n : ℝ) * overlapRadius C ^ 2)
    (hk : (k : ℝ) ≤ Real.log ((n : ℝ) * overlapRadius C ^ 2) /
      (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta))) :
    policyFactor zeta ^ (k + 1) ≤ policyFactor zeta *
      ((n : ℝ) * overlapRadius C ^ 2) ^
        (Real.log (policyFactor zeta) /
          (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta))) := by
  have hL : 1 ≤ policyFactor zeta := (Real.one_lt_exp_iff.mpr hzeta).le
  have hLpos : 0 < policyFactor zeta := Real.exp_pos _
  have hx : 0 < (n : ℝ) * overlapRadius C ^ 2 := by linarith
  have hmono := Real.rpow_le_rpow_of_exponent_le hL hk
  rw [Real.rpow_natCast] at hmono
  rw [pow_succ, mul_comm]
  refine mul_le_mul_of_nonneg_left (hmono.trans_eq ?_) hLpos.le
  rw [Real.rpow_def_of_pos hLpos, Real.rpow_def_of_pos hx]
  congr 1
  ring

/-- The complementary exponent in the variance factor equals one minus beta. For
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the mixing scale assumption](hyp:ht0), and [the policy-overlap scale assumption](hyp:hzeta),
this establishes [the selector tuning variance identity result](goal). -/
-- @node: selector_tuning_variance_identity
lemma selector_tuning_variance_identity (t0 zeta : ℝ) (ht0 : 0 < t0)
    (hzeta : 0 < zeta) :
    Real.log (policyFactor zeta) /
      (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta)) =
        1 - rateExponent t0 zeta := by
  have hD := selector_tuning_denominator_pos t0 zeta ht0 hzeta
  have hβ := selector_tuning_rate_identity t0 zeta ht0 hzeta
  have hsum :
      2 * (Real.log (1 / mixingAlpha t0) /
        (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta))) +
      Real.log (policyFactor zeta) /
        (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta)) = 1 := by
    field_simp
  rw [hβ] at hsum
  linarith

/-- The floor remainder bounds the full trajectory-to-block ratio. For [the time horizon](hyp:T)
and [the candidate-policy count](hyp:M), this establishes
[the selector block len ratio strict bound result](goal). -/
-- @node: selector_blockLen_ratio_lt
lemma selector_blockLen_ratio_lt (T M : Nat) :
    (T : ℝ) / (numBlocks M : ℝ) < (blockLen T M : ℝ) + 1 := by
  have hB : 0 < numBlocks M := lt_of_lt_of_le (by norm_num) (selector_numBlocks_ge_three M)
  have hdecomp := Nat.mod_add_div T (numBlocks M)
  have hrem := Nat.mod_lt T hB
  have hremR : ((T % numBlocks M : Nat) : ℝ) < (numBlocks M : ℝ) := by exact_mod_cast hrem
  have hdecompR : ((T % numBlocks M : Nat) : ℝ) +
      (numBlocks M : ℝ) * (blockLen T M : ℝ) = (T : ℝ) := by
    exact_mod_cast hdecomp
  apply (div_lt_iff₀ (by exact_mod_cast hB)).mpr
  nlinarith

/-- A nonempty block is at least half of the real-valued ratio T/B. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), and
[the sample size assumption](hyp:hn), this establishes
[the selector block len ge half ratio result](goal). -/
-- @node: selector_blockLen_ge_half_ratio
lemma selector_blockLen_ge_half_ratio (T M : Nat) (hn : 1 ≤ blockLen T M) :
    (T : ℝ) / (2 * (numBlocks M : ℝ)) ≤ (blockLen T M : ℝ) := by
  have hratio := selector_blockLen_ratio_lt T M
  have hnR : (1 : ℝ) ≤ blockLen T M := by exact_mod_cast hn
  have hB : (0 : ℝ) < numBlocks M := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) (selector_numBlocks_ge_three M))
  apply (div_le_iff₀ (by positivity)).mpr
  have hratio' := (div_lt_iff₀ hB).mp hratio
  nlinarith

/-- A regime-only threshold makes the logarithmic cap inactive uniformly in all
stationary-overlap radii. This is the n₀ construction after equation (16). For
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the mixing scale assumption](hyp:ht0), and [the policy-overlap scale assumption](hyp:hzeta),
this establishes [the selector eventually cap inactive result](goal). -/
-- @node: selector_eventually_cap_inactive
lemma selector_eventually_cap_inactive (t0 zeta : ℝ) (ht0 : 0 < t0)
    (hzeta : 0 < zeta) :
    ∃ n0 : Nat, 4 ≤ n0 ∧ ∀ n : Nat, n0 ≤ n → ∀ C : ℝ, 1 ≤ C →
      1 < (n : ℝ) * overlapRadius C ^ 2 →
      Real.log ((n : ℝ) * overlapRadius C ^ 2) /
        (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta)) ≤
          (n / 2 : Nat) := by
  let D := 2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta)
  have hD : 0 < D := selector_tuning_denominator_pos t0 zeta ht0 hzeta
  have hev : ∀ᶠ n : Nat in Filter.atTop,
      ‖Real.log (n : ℝ)‖ ≤ (D / 4) * ‖(n : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually
      (Real.isLittleO_log_id_atTop.bound (by positivity : 0 < D / 4))
  obtain ⟨n1, hn1⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max 4 n1, Nat.le_max_left _ _, ?_⟩
  intro n hn C hC hlarge
  have hn4 : 4 ≤ n := (Nat.le_max_left _ _).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hbound := hn1 n ((Nat.le_max_right _ _).trans hn)
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg n),
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] at hbound
  have hCpos : 0 < C := by linarith
  have hq0 : 0 ≤ overlapRadius C := div_nonneg (by linarith) hCpos.le
  have hq1 : overlapRadius C ≤ 1 := by
    unfold overlapRadius
    exact (div_le_one hCpos).mpr (by linarith)
  have hxle : (n : ℝ) * overlapRadius C ^ 2 ≤ n := by
    have hq2 : overlapRadius C ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hlogle := Real.log_le_log (by linarith : 0 < (n : ℝ) * overlapRadius C ^ 2) hxle
  have hhalf : (n : ℝ) / 4 ≤ (n / 2 : Nat) := by
    have hmod := Nat.mod_lt n (by norm_num : 0 < 2)
    have hdecomp := Nat.mod_add_div n 2
    have hdecompR : ((n % 2 : Nat) : ℝ) + 2 * ((n / 2 : Nat) : ℝ) = n := by
      exact_mod_cast hdecomp
    have hmodR : ((n % 2 : Nat) : ℝ) ≤ 1 := by exact_mod_cast (by omega : n % 2 ≤ 1)
    have hn4R : (4 : ℝ) ≤ n := by exact_mod_cast hn4
    linarith
  apply (div_le_iff₀ hD).mpr
  have := mul_le_mul_of_nonneg_left hhalf hD.le
  dsimp only [D] at *
  nlinarith

/-- Factoring the balanced bias coordinate produces the radius-adaptive rate. For
[the sample size](hyp:n), [the q](hyp:q), [the β](hyp:β), and [the q assumption](hyp:hq), this
establishes [the selector bias rate factorization result](goal). -/
-- @node: selector_bias_rate_factorization
lemma selector_bias_rate_factorization (n : Nat) (q β : ℝ) (hq : 0 < q) :
    q * ((n : ℝ) * q ^ 2) ^ (-(β / 2)) =
      q ^ (1 - β) * (n : ℝ) ^ (-(β / 2)) := by
  rw [Real.mul_rpow (Nat.cast_nonneg n) (sq_nonneg q),
    ← Real.rpow_two, ← Real.rpow_mul hq.le]
  have hexp : (2 : ℝ) * -(β / 2) = -β := by ring
  rw [hexp]
  calc
    q * ((n : ℝ) ^ (-(β / 2)) * q ^ (-β)) =
        (q ^ (1 : ℝ) * q ^ (-β)) * (n : ℝ) ^ (-(β / 2)) := by
      rw [Real.rpow_one]
      ring
    _ = q ^ (1 - β) * (n : ℝ) ^ (-(β / 2)) := by
      rw [← Real.rpow_add hq]
      congr 2

/-- The prescribed uncapped depth satisfies the radius-dependent bias rate in equation (15),
including the floor-rounding constant alpha inverse. For [the sample size](hyp:n),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the large assumption](hyp:hlarge), and
[the cap assumption](hyp:hcap), this establishes
[the selector adaptive depth bias rate result](goal). -/
-- @node: selector_adaptiveDepth_bias_rate
lemma selector_adaptiveDepth_bias_rate (n : Nat) (t0 zeta C : ℝ)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (hlarge : 1 < (n : ℝ) * overlapRadius C ^ 2)
    (hcap : Real.log ((n : ℝ) * overlapRadius C ^ 2) /
      (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta)) ≤
        (n / 2 : Nat)) :
    overlapRadius C * mixingAlpha t0 ^ adaptiveDepth n t0 zeta C ≤
      (mixingAlpha t0)⁻¹ * overlapRadius C ^ (1 - rateExponent t0 zeta) *
        (n : ℝ) ^ (-(rateExponent t0 zeta / 2)) := by
  have hq0 : 0 ≤ overlapRadius C := by
    unfold overlapRadius
    exact div_nonneg (by linarith) (by linarith)
  have hq : 0 < overlapRadius C := by
    by_contra h
    have hzero : overlapRadius C = 0 := le_antisymm (le_of_not_gt h) hq0
    norm_num [hzero] at hlarge
  have hf := (selector_adaptiveDepth_floor_bounds n t0 zeta C ht0 hzeta hlarge hcap).1
  have hb := selector_depth_bias_power_le n (adaptiveDepth n t0 zeta C)
    t0 zeta C ht0 hzeta hlarge hf
  calc
    _ ≤ overlapRadius C * ((mixingAlpha t0)⁻¹ *
        ((n : ℝ) * overlapRadius C ^ 2) ^ (-(rateExponent t0 zeta / 2))) :=
      mul_le_mul_of_nonneg_left hb hq0
    _ = (mixingAlpha t0)⁻¹ *
        (overlapRadius C * ((n : ℝ) * overlapRadius C ^ 2) ^
          (-(rateExponent t0 zeta / 2))) := by ring
    _ = _ := by rw [selector_bias_rate_factorization n _ _ hq]; ring

end CausalSmith.Stat.PomdpPolicyclassRegret

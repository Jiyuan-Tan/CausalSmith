module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorTuning
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.HwExpectation

/-! # Conservative-depth HW rates

The regime-only logarithmic cap threshold and the two floor exponent bounds
implement equation (71), independently of any stationary-overlap radius.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open CausalSmith.Stat.PomdpLatentOverlapMinimax

/-- An inactive conservative-depth cap gives both floor inequalities. For
[the sample size](hyp:n), [the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the large assumption](hyp:hlarge), and [the cap assumption](hyp:hcap), this establishes
[the Hu–Wager conservative depth floor bounds result](goal). -/
-- @node: hw_conservativeDepth_floor_bounds
lemma hw_conservativeDepth_floor_bounds (n : Nat) (t0 zeta : ℝ)
    (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hlarge : 1 < (n : ℝ))
    (hcap : Real.log ((n : ℝ)) /
      (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta)) ≤
        (n / 2 : Nat)) :
    let r := Real.log ((n : ℝ)) /
      (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta))
    r - 1 ≤ (conservativeDepth n t0 zeta : ℝ) ∧
      (conservativeDepth n t0 zeta : ℝ) ≤ r := by
  let r := Real.log ((n : ℝ)) /
    (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta))
  have hr : 0 ≤ r := (div_pos (Real.log_pos hlarge)
    (selector_tuning_denominator_pos t0 zeta ht0 hzeta)).le
  have hfloor : (Int.toNat ⌊r⌋ : ℝ) ≤ r := by
    rw [Int.floor_toNat]
    exact Nat.floor_le hr
  have hfloorcap : Int.toNat ⌊r⌋ ≤ n / 2 := by
    exact_mod_cast hfloor.trans hcap
  have hk : conservativeDepth n t0 zeta = Int.toNat ⌊r⌋ := by
    unfold conservativeDepth
    exact Nat.min_eq_right hfloorcap
  rw [hk]
  constructor
  · have hlower := Nat.lt_floor_add_one r
    rw [← Int.floor_toNat] at hlower
    linarith
  · exact hfloor

/-- The lower floor inequality yields the conservative bias power rate. For
[the sample size](hyp:n), [the history length](hyp:k), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta), [the large assumption](hyp:hlarge), and
[the history length assumption](hyp:hk), this establishes
[the Hu–Wager depth bias power bound result](goal). -/
-- @node: hw_depth_bias_power_le
lemma hw_depth_bias_power_le (n k : Nat) (t0 zeta : ℝ)
    (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hlarge : 1 < (n : ℝ))
    (hk : Real.log ((n : ℝ)) /
      (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta)) - 1 ≤
        (k : ℝ)) :
    mixingAlpha t0 ^ k ≤ (mixingAlpha t0)⁻¹ *
      ((n : ℝ)) ^ (-(rateExponent t0 zeta / 2)) := by
  have hα : 0 < mixingAlpha t0 := Real.exp_pos _
  have hα1 : mixingAlpha t0 ≤ 1 := by
    unfold mixingAlpha
    exact (Real.exp_le_one_iff).mpr (neg_nonpos.mpr (by positivity))
  have hx : 0 < (n : ℝ) := by linarith
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

/-- The upper floor inequality yields the conservative variance power rate. For
[the sample size](hyp:n), [the history length](hyp:k), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the policy-overlap scale assumption](hyp:hzeta),
[the large assumption](hyp:hlarge), and [the history length assumption](hyp:hk), this
establishes [the Hu–Wager depth variance power bound result](goal). -/
-- @node: hw_depth_variance_power_le
lemma hw_depth_variance_power_le (n k : Nat) (t0 zeta : ℝ)
    (hzeta : 0 < zeta) (hlarge : 1 < (n : ℝ))
    (hk : (k : ℝ) ≤ Real.log ((n : ℝ)) /
      (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta))) :
    policyFactor zeta ^ (k + 1) ≤ policyFactor zeta *
      ((n : ℝ)) ^
        (Real.log (policyFactor zeta) /
          (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta))) := by
  have hL : 1 ≤ policyFactor zeta := (Real.one_lt_exp_iff.mpr hzeta).le
  have hLpos : 0 < policyFactor zeta := Real.exp_pos _
  have hx : 0 < (n : ℝ) := by linarith
  have hmono := Real.rpow_le_rpow_of_exponent_le hL hk
  rw [Real.rpow_natCast] at hmono
  rw [pow_succ, mul_comm]
  refine mul_le_mul_of_nonneg_left (hmono.trans_eq ?_) hLpos.le
  rw [Real.rpow_def_of_pos hLpos, Real.rpow_def_of_pos hx]
  congr 1
  ring

/-- A regime-only block threshold makes the conservative cap inactive. For
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the mixing scale assumption](hyp:ht0), and [the policy-overlap scale assumption](hyp:hzeta),
this establishes [the Hu–Wager eventually cap inactive result](goal). -/
-- @node: hw_eventually_cap_inactive
lemma hw_eventually_cap_inactive (t0 zeta : ℝ) (ht0 : 0 < t0)
    (hzeta : 0 < zeta) :
    ∃ n0 : Nat, 4 ≤ n0 ∧ ∀ n : Nat, n0 ≤ n →
      Real.log ((n : ℝ)) /
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
  intro n hn
  have hn4 : 4 ≤ n := (Nat.le_max_left _ _).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hbound := hn1 n ((Nat.le_max_right _ _).trans hn)
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg n),
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] at hbound
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

/-- The bias and standard deviation at conservative depth are bounded by the hidden-memory block
coordinate, as in equation (71). For [the sample size](hyp:n), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta), [the sample size assumption](hyp:hn), and
[the cap assumption](hyp:hcap), this establishes
[the Hu–Wager conservative depth moment rates result](goal). -/
-- @node: hw_conservativeDepth_moment_rates
lemma hw_conservativeDepth_moment_rates (n : Nat) (t0 zeta : ℝ)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hn : 4 ≤ n)
    (hcap : Real.log (n : ℝ) /
      (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta)) ≤ (n / 2 : Nat)) :
    mixingAlpha t0 ^ conservativeDepth n t0 zeta *
        (1 + 1 / ((n - conservativeDepth n t0 zeta : Nat) * (1 - mixingAlpha t0))) ≤
      ((mixingAlpha t0)⁻¹ + 2 / (1 - mixingAlpha t0)) *
        (n : ℝ) ^ (-(rateExponent t0 zeta / 2)) ∧
    Real.sqrt (policyFactor zeta ^ (conservativeDepth n t0 zeta + 1) /
      (n - conservativeDepth n t0 zeta : Nat)) ≤
        Real.sqrt (2 * policyFactor zeta) * (n : ℝ) ^ (-(rateExponent t0 zeta / 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlarge : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hLpos : 0 < policyFactor zeta := Real.exp_pos _
  have hα0 : 0 ≤ mixingAlpha t0 := Real.exp_nonneg _
  have hα1 : mixingAlpha t0 < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos (one_div_pos.mpr ht0))
  have hf := hw_conservativeDepth_floor_bounds n t0 zeta ht0 hzeta hlarge hcap
  have hb := hw_depth_bias_power_le n (conservativeDepth n t0 zeta) t0 zeta ht0 hzeta hlarge hf.1
  have hv := hw_depth_variance_power_le n (conservativeDepth n t0 zeta) t0 zeta hzeta hlarge hf.2
  rw [selector_tuning_variance_identity t0 zeta ht0 hzeta] at hv
  have hk := hw_conservativeDepth_half n t0 zeta
  have hN : (n : ℝ) / 2 ≤ (n - conservativeDepth n t0 zeta : Nat) := by
    have hcast : (n : ℝ) = (n - conservativeDepth n t0 zeta : Nat) +
        (conservativeDepth n t0 zeta : ℝ) := by
      exact_mod_cast (Nat.sub_add_cancel (by omega : conservativeDepth n t0 zeta ≤ n)).symm
    have hhalf : 2 * (conservativeDepth n t0 zeta : ℝ) ≤ n := by exact_mod_cast hk
    linarith
  have hNR : (0 : ℝ) < (n - conservativeDepth n t0 zeta : Nat) := lt_of_lt_of_le (by positivity) hN
  have hβ : rateExponent t0 zeta / 2 ≤ 1 := by
    unfold rateExponent
    have hden : 0 < 2 + t0 * zeta := by positivity
    have hb : 2 / (2 + t0 * zeta) ≤ (1 : ℝ) := (div_le_one hden).mpr (by nlinarith [mul_pos ht0 hzeta])
    linarith
  have hinv : 1 / (n : ℝ) ≤ (n : ℝ) ^ (-(rateExponent t0 zeta / 2)) := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by linarith)
  constructor
  · have ht : mixingAlpha t0 ^ conservativeDepth n t0 zeta /
        ((n - conservativeDepth n t0 zeta : Nat) * (1 - mixingAlpha t0)) ≤
          (2 / (1 - mixingAlpha t0)) / n := by
      calc
        _ ≤ 1 / ((n - conservativeDepth n t0 zeta : Nat) * (1 - mixingAlpha t0)) :=
          div_le_div_of_nonneg_right (pow_le_one₀ hα0 hα1.le) (by positivity)
        _ ≤ 1 / (((n : ℝ) / 2) * (1 - mixingAlpha t0)) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity)
            (mul_le_mul_of_nonneg_right hN (by positivity))
        _ = _ := by field_simp
    have ht' := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ 2 / (1 - mixingAlpha t0))
    have hid : (2 / (1 - mixingAlpha t0)) / n = (2 / (1 - mixingAlpha t0)) * (1 / (n : ℝ)) := by ring
    calc
      _ = mixingAlpha t0 ^ conservativeDepth n t0 zeta +
          mixingAlpha t0 ^ conservativeDepth n t0 zeta /
            ((n - conservativeDepth n t0 zeta : Nat) * (1 - mixingAlpha t0)) := by ring
      _ ≤ (mixingAlpha t0)⁻¹ * (n : ℝ) ^ (-(rateExponent t0 zeta / 2)) +
          (2 / (1 - mixingAlpha t0)) * (n : ℝ) ^ (-(rateExponent t0 zeta / 2)) :=
        add_le_add hb (ht.trans (hid.symm ▸ ht'))
      _ = _ := by ring
  · have hv' : policyFactor zeta ^ (conservativeDepth n t0 zeta + 1) /
        (n - conservativeDepth n t0 zeta : Nat) ≤
          2 * policyFactor zeta * (n : ℝ) ^ (-rateExponent t0 zeta) := by
      calc
        _ ≤ (policyFactor zeta * (n : ℝ) ^ (1 - rateExponent t0 zeta)) /
            (n - conservativeDepth n t0 zeta : Nat) := div_le_div_of_nonneg_right hv hNR.le
        _ ≤ (policyFactor zeta * (n : ℝ) ^ (1 - rateExponent t0 zeta)) / ((n : ℝ) / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hN
        _ = _ := by
          rw [show 1 - rateExponent t0 zeta = -rateExponent t0 zeta + 1 by ring,
            Real.rpow_add hnR, Real.rpow_one]
          field_simp
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · convert hv' using 1
      rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.rpow_natCast _ 2,
        ← Real.rpow_mul (Nat.cast_nonneg n)]
      congr 1
      ring

/-- The conservative selector has the uniform HW block rate in (72), for blocks above a
regime-only threshold. For [the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the mixing scale assumption](hyp:ht0), and [the policy-overlap scale assumption](hyp:hzeta),
this establishes [the Hu–Wager expected regret block rate result](goal). -/
-- @node: hw_expectedRegret_block_rate
lemma hw_expectedRegret_block_rate (t0 zeta : ℝ) (ht0 : 0 < t0)
    (hzeta : 0 < zeta) :
    ∃ (K : ℝ) (n0 : Nat), 0 < K ∧ 4 ≤ n0 ∧
      ∀ {T M : Nat} (m : ModelIndex T M), HWPolicyListClass t0 zeta m →
        n0 ≤ blockLen T M →
        expectedRegret (hwBlockSelector T M (by have := m.list_size; omega) t0 zeta) m ≤
          K * (blockLen T M : ℝ) ^ (-(rateExponent t0 zeta / 2)) := by
  obtain ⟨n0, hn0, hcap⟩ := hw_eventually_cap_inactive t0 zeta ht0 hzeta
  let A := 1 + 2 / (policyFactor zeta - 1) + 4 / (1 - mixingAlpha t0)
  let K := 2 * ((mixingAlpha t0)⁻¹ + 2 / (1 - mixingAlpha t0)) +
    8 * Real.exp 1 * Real.sqrt A * Real.sqrt (2 * policyFactor zeta)
  have hα0 : 0 < mixingAlpha t0 := Real.exp_pos _
  have hα1 : mixingAlpha t0 < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos (one_div_pos.mpr ht0))
  have hL : 1 < policyFactor zeta := Real.one_lt_exp_iff.mpr hzeta
  refine ⟨K, n0, by dsimp [K]; positivity, hn0, ?_⟩
  intro T M m hClass hn
  obtain ⟨hb, hs⟩ := hw_conservativeDepth_moment_rates (blockLen T M) t0 zeta
    ht0 hzeta (hn0.trans hn) (hcap _ hn)
  have he := hw_block_expectedRegret_le_bias_sd t0 zeta m hClass (hn0.trans hn)
  dsimp only at he
  rw [show (1 + 2 / (policyFactor zeta - 1) + 4 / (1 - mixingAlpha t0)) *
      policyFactor zeta ^ (conservativeDepth (blockLen T M) t0 zeta + 1) /
        (blockLen T M - conservativeDepth (blockLen T M) t0 zeta : Nat) =
      A * (policyFactor zeta ^ (conservativeDepth (blockLen T M) t0 zeta + 1) /
        (blockLen T M - conservativeDepth (blockLen T M) t0 zeta : Nat)) by dsimp [A]; ring,
    Real.sqrt_mul (by dsimp [A]; positivity)] at he
  have hs' := mul_le_mul_of_nonneg_left hs
    (by positivity : 0 ≤ 8 * Real.exp 1 * Real.sqrt A)
  change expectedRegret _ m ≤ K * _
  dsimp [K]
  nlinarith

end CausalSmith.Stat.PomdpPolicyclassRegret

module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.LogEnclosure
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.SeriesEnclosures

/-! # Certified integer-base power enclosures

The logarithm midpoint and exponential bracket compose at the prescribed internal
precision; clipping preserves containment and endpoint excess.
-/
public section
set_option linter.style.longLine false
noncomputable section
open Causalean.Mathlib.Analysis.IntervalArithmetic
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The prescribed internal precision pays for the cubic base amplification. [the stated conclusion](goal) holds. -/
-- @node: power_internal_budget
lemma power_internal_budget (q B : ℕ) :
    193 * (B : ℝ)^3 * precisionError (q + 12 + 3 * Nat.clog 2 B) ≤ precisionError q ∧
    precisionError (q + 12 + 3 * Nat.clog 2 B) ≤ 1 / 4096 := by
  have hB : (B : ℝ) ≤ 2 ^ Nat.clog 2 B := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < (2 : ℕ)) B
  have hc : (B : ℝ)^3 ≤ (2 : ℝ)^(3 * Nat.clog 2 B) := by
    rw [mul_comm 3, pow_mul]
    gcongr
  have hq : (1 : ℝ) ≤ 2^q := one_le_pow₀ (by norm_num)
  have hl : (1 : ℝ) ≤ 2^(3 * Nat.clog 2 B) := one_le_pow₀ (by norm_num)
  simp only [precisionError, zpow_neg, zpow_natCast, pow_add]
  constructor
  · apply (mul_le_mul_iff_left₀ (by positivity :
      (0 : ℝ) < 2^q * 2^12 * 2^(3 * Nat.clog 2 B))).mp
    field_simp
    nlinarith
  · apply (mul_le_mul_iff_left₀ (by positivity :
      (0 : ℝ) < 2^q * 2^12 * 2^(3 * Nat.clog 2 B))).mp
    field_simp
    nlinarith

/-- A positive integer base raised to an exponent in the primitive domain stays in its clip range. Under the stated assumptions. [The stated hypotheses](hyp:hb,hl,hu) hold, and [the stated conclusion follows](goal). -/
-- @node: power_value_range
lemma power_value_range (b : ℕ) (hb : 1 ≤ b) (v : ℝ) (hl : -3 ≤ v) (hu : v ≤ 3) :
    1 / (b : ℝ)^3 ≤ (b : ℝ)^v ∧ (b : ℝ)^v ≤ (b : ℝ)^3 := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  constructor
  · have h := Real.rpow_le_rpow_of_exponent_le hbR hl
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ b)] at h
    norm_num only [Real.rpow_ofNat] at h
    simpa only [one_div] using h
  · simpa using Real.rpow_le_rpow_of_exponent_le hbR hu

/-- [The certified logarithm midpoint approximates the true logarithm.](goal) Under [the stated assumptions](hyp:hb). -/
-- @node: paperLogScalar_midpoint_error
lemma paperLogScalar_midpoint_error (p b : ℕ) (hb : 1 ≤ b) :
    |(((paperLogScalar p b).lo + (paperLogScalar p b).hi) / 2 : ℚ) -
      Real.log b| ≤ precisionError p := by
  obtain ⟨h, he, hf⟩ := paperLogScalar_spec p b (by exact_mod_cast (Nat.zero_lt_of_lt hb))
  rw [abs_le]
  push_cast at he hf ⊢
  obtain ⟨hlo, hhi⟩ := h
  push_cast at hlo hhi
  exact ⟨by linarith, by linarith⟩

/-- [The logarithm argument error gives a uniform cubic bound on the power value error.](goal) Under [the stated assumptions](hyp:hb,hl,hu). -/
-- @node: power_midpoint_value_error
lemma power_midpoint_value_error (q b : ℕ) (hb : 1 ≤ b) (v : ℚ)
    (hl : -3 ≤ v) (hu : v ≤ 3) :
    let B := max 2 b
    let p := q + 12 + 3 * Nat.clog 2 B
    let L := paperLogScalar p b
    |Real.exp (v * ((L.lo + L.hi) / 2 : ℚ)) - (b : ℝ)^(v : ℝ)| ≤
      96 * (B : ℝ)^3 * precisionError p := by
  dsimp only
  let B := max 2 b
  let p := q + 12 + 3 * Nat.clog 2 B
  let a : ℝ := v * (((paperLogScalar p b).lo + (paperLogScalar p b).hi) / 2 : ℚ)
  let c : ℝ := v * Real.log b
  have hv : |(v : ℝ)| ≤ 3 := by exact_mod_cast abs_le.mpr ⟨hl, hu⟩
  have he : |a - c| ≤ 3 * precisionError p := by
    have hm := paperLogScalar_midpoint_error p b hb
    have hid : a - c = (v : ℝ) *
      ((((paperLogScalar p b).lo + (paperLogScalar p b).hi) / 2 : ℚ) - Real.log b) := by
      dsimp [a, c]; push_cast; ring
    rw [hid, abs_mul]
    exact mul_le_mul hv hm (abs_nonneg _) (by norm_num)
  have hsmall : |a - c| ≤ 1 := he.trans (by
    have := (power_internal_budget q B).2
    dsimp [p]; linarith)
  have hlocal := Real.abs_exp_sub_one_le hsmall
  have hc : Real.exp c = (b : ℝ)^(v : ℝ) := by
    rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < b)]
    dsimp [c]; rw [mul_comm]
  have hbase : Real.exp c ≤ (B : ℝ)^3 := by
    rw [hc]
    apply (power_value_range b hb v (by exact_mod_cast hl) (by exact_mod_cast hu)).2.trans
    gcongr
    exact_mod_cast le_max_right 2 b
  have hid : Real.exp a - Real.exp c = Real.exp c * (Real.exp (a-c) - 1) := by
    rw [mul_sub, ← Real.exp_add, mul_one]
    rw [show c + (a-c) = a by ring]
  change |Real.exp a - (b : ℝ)^(v : ℝ)| ≤ _
  rw [← hc, hid, abs_mul, abs_of_pos (Real.exp_pos c)]
  have h := mul_le_mul hbase hlocal (abs_nonneg _) (by positivity : (0 : ℝ) ≤ (B : ℝ)^3)
  have hp : 0 ≤ precisionError p := by unfold precisionError; positivity
  calc
    Real.exp c * |Real.exp (a-c)-1| ≤ (B : ℝ)^3 * (2 * |a-c|) := h
    _ ≤ (B : ℝ)^3 * (2 * (3 * precisionError p)) := by gcongr
    _ ≤ 96 * (B : ℝ)^3 * precisionError p := by nlinarith [show 0 ≤ (B : ℝ)^3 by positivity]

/-- [Clipped scalar power brackets contain the value and satisfy the requested excess bound.](goal) Under [the stated assumptions](hyp:hb,hl,hu). -/
-- @node: paperPowerScalar_spec
lemma paperPowerScalar_spec (q b : ℕ) (hb : 1 ≤ b) (v : ℚ)
    (hl : -3 ≤ v) (hu : v ≤ 3) :
    (paperPowerScalar q b v).Contains ((b : ℝ)^(v : ℝ)) ∧
    0 < (paperPowerScalar q b v).lo ∧
    (b : ℝ)^(v : ℝ) - (paperPowerScalar q b v).lo ≤ precisionError q ∧
    (paperPowerScalar q b v).hi - (b : ℝ)^(v : ℝ) ≤ precisionError q := by
  by_cases hb1 : b = 1
  · subst b
    simp [paperPowerScalar, RatInterval.Contains, RatInterval.point,
      show 0 ≤ precisionError q by unfold precisionError; positivity]
  let B := max 2 b
  let p := q + 12 + 3 * Nat.clog 2 B
  let L := paperLogScalar p b
  let z : ℚ := v * ((L.lo + L.hi) / 2)
  let J := paperExpScalar p z
  let e : ℚ := 96 * (B : ℚ)^3 * rationalError p
  let y : ℝ := (b : ℝ)^(v : ℝ)
  have heq : (e : ℝ) = 96 * (B : ℝ)^3 * precisionError p := by
    simp [e, rationalError, precisionError, zpow_neg, zpow_natCast]
  have herr : |Real.exp z - y| ≤ (e : ℝ) := by
    rw [heq]
    simpa only [z, y, L, p, B, Rat.cast_mul] using power_midpoint_value_error q b hb v hl hu
  obtain ⟨⟨hJlo, hJhi⟩, hJ0, hJl, hJu⟩ := paperExpScalar_spec p z
  change (J.lo : ℝ) ≤ Real.exp z at hJlo
  change Real.exp z ≤ (J.hi : ℝ) at hJhi
  change Real.exp z - (J.lo : ℝ) ≤ precisionError p at hJl
  change (J.hi : ℝ) - Real.exp z ≤ precisionError p at hJu
  have hcl : 1 / (b : ℝ)^3 ≤ y :=
    (power_value_range b hb v (by exact_mod_cast hl) (by exact_mod_cast hu)).1
  have hcu : y ≤ (b : ℝ)^3 :=
    (power_value_range b hb v (by exact_mod_cast hl) (by exact_mod_cast hu)).2
  have hlR : ((max (1 / (b : ℚ)^3) (J.lo-e) : ℚ) : ℝ) ≤ y := by
    push_cast
    exact max_le hcl (by linarith only [hJlo, (abs_le.mp herr).2])
  have huR : y ≤ ((min ((b : ℚ)^3) (J.hi+e) : ℚ) : ℝ) := by
    push_cast
    exact le_min hcu (by linarith only [hJhi, (abs_le.mp herr).1])
  have hord : max (1 / (b : ℚ)^3) (J.lo-e) ≤ min ((b : ℚ)^3) (J.hi+e) := by
    exact_mod_cast hlR.trans huR
  have hlo : J.lo - e ≤ max (1 / (b : ℚ)^3) (J.lo-e) := le_max_right _ _
  have hhi : min ((b : ℚ)^3) (J.hi+e) ≤ J.hi + e := min_le_right _ _
  have hloR : (J.lo : ℝ) - e ≤ (max (1 / (b : ℚ)^3) (J.lo-e) : ℚ) := by
    exact_mod_cast hlo
  have hhiR : (min ((b : ℚ)^3) (J.hi+e) : ℚ) ≤ (J.hi : ℝ) + e := by
    exact_mod_cast hhi
  have hB : (1 : ℝ) ≤ (B : ℝ)^3 := by
    have : (1 : ℝ) ≤ B := by dsimp [B]; exact_mod_cast (le_max_left 2 b).trans' (by norm_num : 1 ≤ (2 : ℕ))
    exact one_le_pow₀ this
  have hp : 0 ≤ precisionError p := by unfold precisionError; positivity
  have hbudget : precisionError p + 2 * (e : ℝ) ≤ precisionError q := by
    rw [heq]
    have hbound : 193 * (B : ℝ)^3 * precisionError p ≤ precisionError q :=
      (power_internal_budget q B).1
    nlinarith only [hbound, mul_nonneg (sub_nonneg.mpr hB) hp]
  have hout : paperPowerScalar q b v = rationalBox
      (max (1 / (b : ℚ)^3) (J.lo-e)) (min ((b : ℚ)^3) (J.hi+e)) := by
    simp only [paperPowerScalar, if_neg hb1]
    rfl
  rw [hout]
  simp only [rationalBox, min_eq_left hord,
    max_eq_right hord, RatInterval.Contains]
  refine ⟨⟨hlR, huR⟩, ?_, ?_, ?_⟩
  · exact (by positivity : (0 : ℚ) < 1 / (b : ℚ)^3).trans_le (le_max_left _ _)
  · change y - (max (1 / (b : ℚ)^3) (J.lo-e) : ℚ) ≤ precisionError q
    linarith only [hloR, hJl, hbudget, (abs_le.mp herr).1]
  · change (min ((b : ℚ)^3) (J.hi+e) : ℚ) - y ≤ precisionError q
    linarith only [hhiR, hJu, hbudget, (abs_le.mp herr).2]

/-- [Monotone endpoint evaluation gives the complete integer-base power primitive contract.](goal) Under [the stated assumptions](hyp:hb,hl,hu). -/
-- @node: concreteEngine_power_contract
lemma concreteEngine_power_contract (q b : ℕ) (I : RatInterval)
    (hb : 1 ≤ b) (hl : -3 ≤ I.lo) (hu : I.hi ≤ 3) :
    MonotoneContract (fun v => (b : ℝ)^v) q I (concreteEngine.powBox q b I) ∧
    0 < (concreteEngine.powBox q b I).lo := by
  have hmono : Monotone (fun v : ℝ => (b : ℝ)^v) :=
    fun _ _ h => Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hb) h
  obtain ⟨hlo, hp, hle, _⟩ := paperPowerScalar_spec q b hb I.lo hl (I.lo_le_hi.trans hu)
  obtain ⟨hhi, _, _, hue⟩ := paperPowerScalar_spec q b hb I.hi (hl.trans I.lo_le_hi) hu
  have hordR : ((paperPowerScalar q b I.lo).lo : ℝ) ≤ (paperPowerScalar q b I.hi).hi :=
    hlo.1.trans ((hmono (by exact_mod_cast I.lo_le_hi)).trans hhi.2)
  have hord : (paperPowerScalar q b I.lo).lo ≤ (paperPowerScalar q b I.hi).hi := by
    exact_mod_cast hordR
  simp only [concreteEngine, endpointExtension, rationalBox, min_eq_left hord,
    max_eq_right hord, MonotoneContract, RatInterval.Contains]
  refine ⟨⟨?_, sub_nonneg.mpr hlo.1, hle, sub_nonneg.mpr hhi.2, hue⟩, hp⟩
  intro x hx
  exact ⟨hlo.1.trans (hmono hx.1), (hmono hx.2).trans hhi.2⟩

end CausalSmith.Stat.LogoddsLowsmoothFrontier

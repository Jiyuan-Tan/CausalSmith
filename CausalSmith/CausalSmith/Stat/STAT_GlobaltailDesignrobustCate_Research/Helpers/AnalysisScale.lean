module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.BandwidthRate
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.CountAdmissibility
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Deterministic analysis scale for count adaptation

Roadmap (4) rounds a fixed multiple of the continuous rate width upwards.
The resulting scale belongs to the count selector's grid and, for a sufficiently
large multiplier, meets the expected-count condition in (5)--(6).
The final lemmas absorb the exponential count-failure remainder into the
target rate after equation (11).
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

/-- Weak overlap makes the analysis dimension strictly larger than the design dimension. -/
-- @node: effectiveDimension_gt_dimension
lemma effectiveDimension_gt_dimension {d : ℕ} {γ : ℝ}
    (hd : 1 ≤ d) (hγ : 1 < γ) : (d : ℝ) < effectiveDimension d γ := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  unfold effectiveDimension
  apply (lt_div_iff₀ (by linarith : 0 < γ - 1)).mpr
  nlinarith

/-- Upward dyadic rounding preserves the width within a strict factor of two. -/
-- @node: dyadicWidth_rounding_up
lemma dyadicWidth_rounding_up {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) :
    w ≤ dyadicWidth (Nat.floor (Real.log w⁻¹ / Real.log 2)) ∧
      dyadicWidth (Nat.floor (Real.log w⁻¹ / Real.log 2)) < 2 * w := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha : 0 ≤ Real.log w⁻¹ / Real.log 2 :=
    div_nonneg (Real.log_nonneg ((one_le_inv₀ hw).2 hw1)) hlog.le
  have hp : (2 : ℝ) ^ Nat.floor (Real.log w⁻¹ / Real.log 2) =
      Real.exp (Real.log 2 * (Nat.floor (Real.log w⁻¹ / Real.log 2) : ℝ)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
  have hlo : (2 : ℝ) ^ Nat.floor (Real.log w⁻¹ / Real.log 2) ≤ w⁻¹ := by
    rw [hp, ← Real.exp_log (inv_pos.mpr hw)]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (Nat.floor_le ha) hlog.le
    simpa [mul_div_cancel₀ _ hlog.ne'] using h
  have hhi : w⁻¹ < 2 * (2 : ℝ) ^ Nat.floor (Real.log w⁻¹ / Real.log 2) := by
    rw [hp, ← Real.exp_log (inv_pos.mpr hw), ← Real.exp_log (by norm_num : (0 : ℝ) < 2),
      ← Real.exp_add]
    apply Real.exp_lt_exp.mpr
    have h := mul_lt_mul_of_pos_left
      (Nat.lt_floor_add_one (Real.log w⁻¹ / Real.log 2)) hlog
    simpa [mul_add, mul_div_cancel₀ _ hlog.ne', mul_comm, add_comm] using h
  have hp0 : (0 : ℝ) < 2 ^ Nat.floor (Real.log w⁻¹ / Real.log 2) := by positivity
  unfold dyadicWidth
  constructor
  · apply (le_div_iff₀ hp0).mpr
    have h := mul_le_mul_of_nonneg_left hlo hw.le
    rw [mul_inv_cancel₀ hw.ne'] at h
    exact h
  · apply (div_lt_iff₀ hp0).mpr
    have h := mul_lt_mul_of_pos_left hhi hw
    rw [mul_inv_cancel₀ hw.ne'] at h
    nlinarith only [h]

/-- An analysis width enlarged by a multiplier at least one lies in the selector grid. -/
-- @node: analysisLevel_le_selectorMaxLevel
lemma analysisLevel_le_selectorMaxLevel {d n : ℕ} {β γ a : ℝ}
    (hd : 1 ≤ d) (hn : 1 ≤ n) (hβ : 0 < β) (hγ : 1 < γ) (ha : 1 ≤ a) :
    Nat.floor (Real.log (a * rateWidth d n β γ)⁻¹ / Real.log 2) ≤
      selectorMaxLevel d n β := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD := effectiveDimension_gt_dimension hd hγ
  have hden : 0 < 2 * β + (d : ℝ) := by positivity
  have hdenD : 0 < 2 * β + effectiveDimension d γ := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hloga : 0 ≤ Real.log a := Real.log_nonneg ha
  unfold selectorMaxLevel
  apply Nat.floor_le_floor
  rw [Real.log_inv, Real.log_mul (by linarith : a ≠ 0)
    (by unfold rateWidth; positivity : rateWidth d n β γ ≠ 0)]
  unfold rateWidth
  rw [Real.log_rpow hn']
  have hdiv : Real.log (n : ℝ) / (2 * β + effectiveDimension d γ) ≤
      Real.log (n : ℝ) / (2 * β + (d : ℝ)) :=
    div_le_div_of_nonneg_left hlogn hden (by linarith)
  apply (div_le_iff₀ hlog2).mpr
  have heq : Real.log (n : ℝ) / Real.log 2 / (2 * β + (d : ℝ)) * Real.log 2 =
      Real.log (n : ℝ) / (2 * β + (d : ℝ)) := by field_simp
  rw [heq]
  have heq' : -(-1 / (2 * β + effectiveDimension d γ) * Real.log (n : ℝ)) =
      Real.log (n : ℝ) / (2 * β + effectiveDimension d γ) := by ring
  linarith

/-- The continuous analysis bandwidth balances the expected count and occupancy threshold. -/
-- @node: rateWidth_sample_balance
lemma rateWidth_sample_balance {d n : ℕ} {β γ : ℝ} (hn : 1 ≤ n)
    (hden : 2 * β + effectiveDimension d γ ≠ 0) :
    (n : ℝ) * (rateWidth d n β γ) ^ (2 * β + effectiveDimension d γ) = 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  unfold rateWidth
  rw [← Real.rpow_mul hn'.le]
  have he : -(1 : ℝ) / (2 * β + effectiveDimension d γ) *
      (2 * β + effectiveDimension d γ) = -1 := by field_simp
  rw [he, Real.rpow_neg_one, mul_inv_cancel₀ hn'.ne']

/-- The ceiling costs at most a factor of two, so a power balance of four
implies the twice-threshold expected-count condition in roadmap (5). -/
-- @node: selectorThreshold_of_power_balance
lemma selectorThreshold_of_power_balance {n j : ℕ} {β D c : ℝ}
    (hβ : 0 ≤ β)
    (hbalance : 4 ≤ (n : ℝ) * c * (dyadicWidth j) ^ (2 * β + D)) :
    2 * (selectorThreshold j β : ℝ) ≤
      (n : ℝ) * c * (dyadicWidth j) ^ D := by
  have hh : 0 < dyadicWidth j := by unfold dyadicWidth; positivity
  have hpow : 0 < (dyadicWidth j) ^ (2 * β) := by positivity
  have hmul := mul_le_mul_of_nonneg_right (selectorThreshold_upper j β hβ)
    hpow.le
  have hinv : (dyadicWidth j) ^ (-(2 * β)) * (dyadicWidth j) ^ (2 * β) = 1 := by
    rw [← Real.rpow_add hh]; simp
  have hupper : (selectorThreshold j β : ℝ) * (dyadicWidth j) ^ (2 * β) ≤ 2 := by
    simpa only [mul_assoc, hinv, mul_one] using hmul
  rw [Real.rpow_add hh] at hbalance
  apply (mul_le_mul_iff_left₀ hpow).mp
  nlinarith only [hupper, hbalance]

/-- Any fixed positive enlargement of the continuous rate width eventually fits in the unit cube. -/
-- @node: analysisWidth_eventually_le_one
lemma analysisWidth_eventually_le_one {d : ℕ} {β γ a : ℝ}
    (hd : 1 ≤ d) (hβ : 0 < β) (hγ : 1 < γ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a * rateWidth d n β γ ≤ 1 := by
  have hden : 0 < 2 * β + effectiveDimension d γ := by
    have := effectiveDimension_pos hd hγ
    linarith
  have ht : Filter.Tendsto (fun n : ℕ => a * rateWidth d n β γ)
      Filter.atTop (nhds (0 : ℝ)) := by
    have h := (tendsto_rpow_neg_atTop (one_div_pos.mpr hden)).comp
      (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ))
        Filter.atTop Filter.atTop)
    simpa only [rateWidth, neg_div, mul_zero, Function.comp_def] using h.const_mul a
  exact Filter.eventually_atTop.mp (ht.eventually_le_const (by norm_num : (0 : ℝ) < 1))

/-- Roadmap (4)--(5): a sufficiently large fixed multiplier gives a grid
scale within a factor of two of the target width and enough expected counts. -/
-- @node: analysisScale_exists
lemma analysisScale_exists {d : ℕ} {β γ c a : ℝ}
    (hd : 1 ≤ d) (hβ : 0 < β) (hγ : 1 < γ) (hc : 0 < c) (ha : 1 ≤ a)
    (hlarge : 4 ≤ c * a ^ (2 * β + effectiveDimension d γ)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 ≤ n → ∃ j : ℕ,
      j ≤ selectorMaxLevel d n β ∧
      a * rateWidth d n β γ ≤ dyadicWidth j ∧
      dyadicWidth j < 2 * a * rateWidth d n β γ ∧
      2 * (selectorThreshold j β : ℝ) ≤
        (n : ℝ) * c * (dyadicWidth j) ^ effectiveDimension d γ := by
  have ha0 : 0 < a := by linarith
  have hden : 0 < 2 * β + effectiveDimension d γ := by
    have := effectiveDimension_pos hd hγ
    linarith
  obtain ⟨N, hN⟩ := analysisWidth_eventually_le_one (a := a) hd hβ hγ
  refine ⟨N, ?_⟩
  intro n hn hn1
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hw : 0 < rateWidth d n β γ := by unfold rateWidth; positivity
  let j := Nat.floor (Real.log (a * rateWidth d n β γ)⁻¹ / Real.log 2)
  obtain ⟨hlo, hhi⟩ := dyadicWidth_rounding_up (mul_pos ha0 hw) (hN n hn)
  refine ⟨j, analysisLevel_le_selectorMaxLevel hd hn1 hβ hγ ha, hlo,
    by simpa only [mul_assoc] using hhi, ?_⟩
  apply selectorThreshold_of_power_balance hβ.le
  have heq : (n : ℝ) * c * (a * rateWidth d n β γ) ^
      (2 * β + effectiveDimension d γ) =
      c * a ^ (2 * β + effectiveDimension d γ) := by
    rw [Real.mul_rpow ha0.le hw.le]
    have hb := rateWidth_sample_balance hn1 hden.ne'
    calc
      _ = c * a ^ (2 * β + effectiveDimension d γ) *
          ((n : ℝ) * (rateWidth d n β γ) ^ (2 * β + effectiveDimension d γ)) := by ring
      _ = _ := by rw [hb, mul_one]
  calc
    4 ≤ (n : ℝ) * c * (a * rateWidth d n β γ) ^
        (2 * β + effectiveDimension d γ) := by rw [heq]; exact hlarge
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hlo hden.le) (by positivity)

/-- A fixed positive mass constant can always be offset by an enlarged analysis bandwidth. -/
-- @node: analysisMultiplier_exists
lemma analysisMultiplier_exists {c p : ℝ} (hc : 0 < c) (hp : 0 < p) :
    ∃ a : ℝ, 1 ≤ a ∧ 4 ≤ c * a ^ p := by
  let a : ℝ := max 1 ((4 / c) ^ (1 / p))
  have hbase : 0 < 4 / c := by positivity
  have heq : ((4 / c) ^ (1 / p)) ^ p = 4 / c := by
    rw [← Real.rpow_mul hbase.le, one_div_mul_cancel hp.ne', Real.rpow_one]
  have hpow : 4 / c ≤ a ^ p := by
    rw [← heq]
    exact Real.rpow_le_rpow (by positivity) (le_max_right _ _) hp.le
  refine ⟨a, le_max_left _ _, ?_⟩
  have h := mul_le_mul_of_nonneg_left hpow hc.le
  have he : c * (4 / c) = 4 := by field_simp
  rwa [he] at h

/-- The expected occupancy at the continuous analysis width is a positive
power of sample size, implementing the last exponential remainder in (11). -/
-- @node: rateWidth_count_eq
lemma rateWidth_count_eq {d n : ℕ} {β γ : ℝ} (hn : 1 ≤ n)
    (hden : 2 * β + effectiveDimension d γ ≠ 0) :
    (n : ℝ) * (rateWidth d n β γ) ^ effectiveDimension d γ =
      (n : ℝ) ^ (2 * β / (2 * β + effectiveDimension d γ)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  unfold rateWidth
  rw [← Real.rpow_mul hn'.le]
  conv_lhs => lhs; rw [← Real.rpow_one (n : ℝ)]
  rw [← Real.rpow_add hn']
  congr 1
  field_simp
  ring

/-- Exponential decay at a positive power of sample size eventually dominates
any inverse-power remainder. This is the analytic absorption after (11). -/
-- @node: exp_samplePower_eventually_le
lemma exp_samplePower_eventually_le (c p r : ℝ) (hc : 0 < c) (hp : 0 < p) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 ≤ n →
      Real.exp (-c * (n : ℝ) ^ p) ≤ (n : ℝ) ^ (-r) := by
  have ht : Filter.Tendsto
      (fun n : ℕ => ((n : ℝ) ^ p) ^ (r / p) * Real.exp (-c * (n : ℝ) ^ p))
      Filter.atTop (nhds (0 : ℝ)) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (r / p) c hc).comp
      ((tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (ht.eventually_le_const (by norm_num : (0 : ℝ) < 1))
  refine ⟨N, ?_⟩
  intro n hn hn1
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h := hN n hn
  rw [← Real.rpow_mul hn'.le, mul_div_cancel₀ r hp.ne'] at h
  apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hn' r)).mp
  rw [← Real.rpow_add hn', add_neg_cancel, Real.rpow_zero]
  simpa only [mul_comm] using h

/-- At every analysis width at least the continuous rate width, the
exponential count-failure remainder is eventually at most the target rate.
The bound holds uniformly over the choice of dyadic level. -/
-- @node: analysisScale_exponential_le_rate
lemma analysisScale_exponential_le_rate {d : ℕ} {β γ c : ℝ}
    (hd : 1 ≤ d) (hβ : 0 < β) (hγ : 1 < γ) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 ≤ n → ∀ j : ℕ,
      rateWidth d n β γ ≤ dyadicWidth j →
      Real.exp (-c * (n : ℝ) * (dyadicWidth j) ^ effectiveDimension d γ) ≤
        rate d n β γ := by
  have hD := effectiveDimension_pos hd hγ
  have hden : 0 < 2 * β + effectiveDimension d γ := by linarith
  obtain ⟨N, hN⟩ := exp_samplePower_eventually_le c
    (2 * β / (2 * β + effectiveDimension d γ))
    (β / (2 * β + effectiveDimension d γ)) hc (by positivity)
  refine ⟨N, ?_⟩
  intro n hn hn1 j hj
  calc
    _ ≤ Real.exp (-c * ((n : ℝ) *
        (rateWidth d n β γ) ^ effectiveDimension d γ)) := by
      apply Real.exp_le_exp.mpr
      have hpow := Real.rpow_le_rpow (by unfold rateWidth; positivity) hj hD.le
      have hmul := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      nlinarith only [hmul, hc]
    _ = Real.exp (-c * (n : ℝ) ^ (2 * β / (2 * β + effectiveDimension d γ))) := by
      rw [rateWidth_count_eq hn1 hden.ne']
    _ ≤ rate d n β γ := by
      simpa only [rate, neg_div] using hN n hn hn1

end CausalSmith.Stat.GlobalTailDesignRobustCate

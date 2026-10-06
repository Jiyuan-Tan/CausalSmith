module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.Construction
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
/-! Exact comparisons of the benchmark terms and the four public budget regimes. -/
public section
open Filter
open scoped Topology
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- The sparse-privacy term meets the sampling term at the fourth-root budget. The result uses [the stated assumptions](hyp:hx,he) and establishes [the displayed conclusion](goal). -/
-- @node: sparse_le_sampling_iff
lemma sparse_le_sampling_iff (x epsilon : ℝ) (hx : 0 < x) (he : 0 < epsilon) :
    (x ^ 2 * epsilon) ^ (-1 / 7 : ℝ) ≤ x ^ (-1 / 4 : ℝ) ↔ x ^ (-1 / 4 : ℝ) ≤ epsilon := by
  have hxe : 0 < x ^ 2 * epsilon := by positivity
  rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hxe _) (Real.rpow_pos_of_pos hx _),
    ← Real.log_le_log_iff (Real.rpow_pos_of_pos hx _) he]
  rw [Real.log_rpow hxe, Real.log_rpow hx, Real.log_mul (by positivity) he.ne',
    Real.log_pow]
  norm_num
  constructor <;> intro h <;> linarith

/-- The dense-privacy term meets the sampling term at the square-root budget. The result uses [the stated assumptions](hyp:hx,he) and establishes [the displayed conclusion](goal). -/
-- @node: dense_le_sampling_iff
lemma dense_le_sampling_iff (x epsilon : ℝ) (hx : 0 < x) (he : 0 < epsilon) :
    (x * epsilon) ^ (-1 / 2 : ℝ) ≤ x ^ (-1 / 4 : ℝ) ↔ x ^ (-1 / 2 : ℝ) ≤ epsilon := by
  have hxe : 0 < x * epsilon := by positivity
  rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hxe _) (Real.rpow_pos_of_pos hx _),
    ← Real.log_le_log_iff (Real.rpow_pos_of_pos hx _) he]
  rw [Real.log_rpow hxe, Real.log_rpow hx, Real.log_rpow hx,
    Real.log_mul hx.ne' he.ne']
  constructor <;> intro h <;> linarith

/-- The two privacy terms meet at the three-fifths budget. The result uses [the stated assumptions](hyp:hx,he) and establishes [the displayed conclusion](goal). -/
-- @node: dense_le_sparse_iff
lemma dense_le_sparse_iff (x epsilon : ℝ) (hx : 0 < x) (he : 0 < epsilon) :
    (x * epsilon) ^ (-1 / 2 : ℝ) ≤ (x ^ 2 * epsilon) ^ (-1 / 7 : ℝ) ↔
      x ^ (-3 / 5 : ℝ) ≤ epsilon := by
  have hxe : 0 < x * epsilon := by positivity
  have hx2e : 0 < x ^ 2 * epsilon := by positivity
  rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hxe _) (Real.rpow_pos_of_pos hx2e _),
    ← Real.log_le_log_iff (Real.rpow_pos_of_pos hx _) he]
  rw [Real.log_rpow hxe, Real.log_rpow hx2e, Real.log_rpow hx,
    Real.log_mul hx.ne' he.ne', Real.log_mul (by positivity) he.ne',
    Real.log_pow]
  norm_num
  constructor <;> intro h <;> linarith

/-- Reversing the budget comparison reverses the order of the two privacy terms. The result uses [the stated assumptions](hyp:hx,he) and establishes [the displayed conclusion](goal). -/
-- @node: sparse_le_dense_iff
lemma sparse_le_dense_iff (x epsilon : ℝ) (hx : 0 < x) (he : 0 < epsilon) :
    (x ^ 2 * epsilon) ^ (-1 / 7 : ℝ) ≤ (x * epsilon) ^ (-1 / 2 : ℝ) ↔
      epsilon ≤ x ^ (-3 / 5 : ℝ) := by
  have hxe : 0 < x * epsilon := by positivity
  have hx2e : 0 < x ^ 2 * epsilon := by positivity
  rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hx2e _) (Real.rpow_pos_of_pos hxe _),
    ← Real.log_le_log_iff he (Real.rpow_pos_of_pos hx _)]
  rw [Real.log_rpow hxe, Real.log_rpow hx2e, Real.log_rpow hx,
    Real.log_mul hx.ne' he.ne', Real.log_mul (by positivity) he.ne',
    Real.log_pow]
  norm_num
  constructor <;> intro h <;> linarith

/-- In the large-budget regime both privacy terms are below the sampling term. The result uses [the stated assumptions](hyp:hn,he,hb) and establishes [the displayed conclusion](goal). -/
-- @node: rate_sampling_regime
lemma rate_sampling_regime (n : ℕ) (epsilon : ℝ) (hn : 2 ≤ n) (he : 0 < epsilon)
    (hb : (n : ℝ) ^ (-1 / 4 : ℝ) ≤ epsilon) :
    rate n epsilon = (n : ℝ) ^ (-1 / 4 : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hba := (sparse_le_sampling_iff _ _ hn0 he).mpr hb
  have hca := (dense_le_sampling_iff _ _ hn0 he).mpr
    ((Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (-1 / 2 : ℝ) ≤ -1 / 4)).trans hb)
  have ha1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num : (-1 / 4 : ℝ) ≤ 0)
  simp only [rate, max_eq_left (max_le hba hca), min_eq_right ha1]

/-- In the intermediate sparse regime the sparse-privacy term is the maximum and below one. The result uses [the stated assumptions](hyp:hn,he,hb) and establishes [the displayed conclusion](goal). -/
-- @node: rate_sparse_regime
lemma rate_sparse_regime (n : ℕ) (epsilon : ℝ) (hn : 2 ≤ n) (he : 0 < epsilon)
    (hb : (n : ℝ) ^ (-3 / 5 : ℝ) ≤ epsilon ∧ epsilon ≤ (n : ℝ) ^ (-1 / 4 : ℝ)) :
    rate n epsilon = ((n : ℝ) ^ 2 * epsilon) ^ (-1 / 7 : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hab : (n : ℝ) ^ (-1 / 4 : ℝ) ≤ ((n : ℝ) ^ 2 * epsilon) ^ (-1 / 7 : ℝ) := by
    have hx : 0 < (n : ℝ) ^ 2 * epsilon := by positivity
    rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hn0 _) (Real.rpow_pos_of_pos hx _)]
    have hl := (Real.log_le_log_iff he (Real.rpow_pos_of_pos hn0 _)).mpr hb.2
    rw [Real.log_rpow hn0] at hl
    rw [Real.log_rpow hn0, Real.log_rpow hx, Real.log_mul (by positivity) he.ne',
    Real.log_pow]
    norm_num
    linarith
  have hcb := (dense_le_sparse_iff _ _ hn0 he).mpr hb.1
  have hi : (n : ℝ) ^ (-1 : ℝ) ≤ epsilon :=
    (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (-1 : ℝ) ≤ -3 / 5)).trans hb.1
  have hprod : 1 ≤ (n : ℝ) * epsilon := by
    rw [Real.rpow_neg_one] at hi
    have := mul_le_mul_of_nonneg_left hi hn0.le
    simpa [mul_inv_cancel₀ hn0.ne'] using this
  have hprod2 : 1 ≤ (n : ℝ) ^ 2 * epsilon := by nlinarith
  have hb1 := Real.rpow_le_one_of_one_le_of_nonpos hprod2 (by norm_num : (-1 / 7 : ℝ) ≤ 0)
  simp only [rate, max_eq_left hcb, max_eq_right hab, min_eq_right hb1]

/-- In the dense regime the dense-privacy term is the maximum and below one. The result uses [the stated assumptions](hyp:hn,he,hb) and establishes [the displayed conclusion](goal). -/
-- @node: rate_dense_regime
lemma rate_dense_regime (n : ℕ) (epsilon : ℝ) (hn : 2 ≤ n) (he : 0 < epsilon)
    (hb : (n : ℝ) ^ (-1 : ℤ) ≤ epsilon ∧ epsilon ≤ (n : ℝ) ^ (-3 / 5 : ℝ)) :
    rate n epsilon = ((n : ℝ) * epsilon) ^ (-1 / 2 : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hbc := (sparse_le_dense_iff _ _ hn0 he).mpr hb.2
  have hac : (n : ℝ) ^ (-1 / 4 : ℝ) ≤ ((n : ℝ) * epsilon) ^ (-1 / 2 : ℝ) := by
    have hx : 0 < (n : ℝ) * epsilon := by positivity
    have hi : epsilon ≤ (n : ℝ) ^ (-1 / 2 : ℝ) := hb.2.trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (-3 / 5 : ℝ) ≤ -1 / 2))
    have hl := (Real.log_le_log_iff he (Real.rpow_pos_of_pos hn0 _)).mpr hi
    rw [Real.log_rpow hn0] at hl
    rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hn0 _) (Real.rpow_pos_of_pos hx _),
      Real.log_rpow hn0, Real.log_rpow hx, Real.log_mul hn0.ne' he.ne']
    linarith
  have hprod : 1 ≤ (n : ℝ) * epsilon := by
    have := mul_le_mul_of_nonneg_left hb.1 hn0.le
    simpa [zpow_neg_one, mul_inv_cancel₀ hn0.ne'] using this
  have hc1 := Real.rpow_le_one_of_one_le_of_nonpos hprod (by norm_num : (-1 / 2 : ℝ) ≤ 0)
  simp only [rate, max_eq_right hbc, max_eq_right hac, min_eq_right hc1]

/-- Below the inverse-sample-size budget the dense term reaches the cap. The result uses [the stated assumptions](hyp:hn,he,hb) and establishes [the displayed conclusion](goal). -/
-- @node: rate_capped_regime
lemma rate_capped_regime (n : ℕ) (epsilon : ℝ) (hn : 2 ≤ n) (he : 0 < epsilon)
    (hb : epsilon ≤ (n : ℝ) ^ (-1 : ℤ)) : rate n epsilon = 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hx : 0 < (n : ℝ) * epsilon := by positivity
  have hprod : (n : ℝ) * epsilon ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hb hn0.le
    simpa [zpow_neg_one, mul_inv_cancel₀ hn0.ne'] using this
  have hc : 1 ≤ ((n : ℝ) * epsilon) ^ (-1 / 2 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_nonpos hx hprod (by norm_num : (-1 / 2 : ℝ) ≤ 0)
  exact min_eq_left (hc.trans ((le_max_right _ _).trans (le_max_right _ _)))

/-- Unit budget gives exactly the nonprivate sampling benchmark.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,hn). -/
-- @node: rate_unit_budget
lemma rate_unit_budget (n : ℕ) (hn : 2 ≤ n) : rate n 1 = (n : ℝ) ^ (-1 / 4 : ℝ) := by
  apply rate_sampling_regime n 1 hn zero_lt_one
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast (show 1 ≤ n by omega)) (by norm_num)

/-- The capped dense-privacy term is always a lower bound for the benchmark.  [the theorem's stated inputs and assumptions](hyp:n,epsilon), and [the asserted conclusion follows](goal). -/
-- @node: capped_dense_le_rate
lemma capped_dense_le_rate (n : ℕ) (epsilon : ℝ) :
    min 1 (((n : ℝ) * epsilon) ^ (-1 / 2 : ℝ)) ≤ rate n epsilon := by
  exact min_le_min_left 1 ((le_max_right _ _).trans (le_max_right _ _))

/-- Divergence of sample size times budget makes all three benchmark terms vanish. The result uses [the stated assumptions](hyp:he,hdiv) and establishes [the displayed conclusion](goal). -/
-- @node: rate_tendsto_zero_of_budget_diverges
lemma rate_tendsto_zero_of_budget_diverges (budgets : ℕ → ℝ)
    (he : ∀ j, 2 ≤ j → 0 < budgets j)
    (hdiv : Tendsto (fun j : ℕ => (j : ℝ) * budgets j) atTop atTop) :
    Tendsto (fun j => rate j (budgets j)) atTop (𝓝 0) := by
  have ha : Tendsto (fun j : ℕ => (j : ℝ) ^ (-1 / 4 : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def, neg_div] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop
  have hdiv2 : Tendsto (fun j : ℕ => (j : ℝ) ^ 2 * budgets j) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hdiv
    filter_upwards [eventually_ge_atTop 2] with j hj
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
    have heb := (he j hj).le
    have hs : (j : ℝ) ≤ (j : ℝ) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right hs heb
  have hb : Tendsto (fun j : ℕ => ((j : ℝ) ^ 2 * budgets j) ^ (-1 / 7 : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def, neg_div] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 7)).comp hdiv2
  have hc : Tendsto (fun j : ℕ => ((j : ℝ) * budgets j) ^ (-1 / 2 : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def, neg_div] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hdiv
  simpa [rate] using
    (tendsto_const_nhds (x := (1 : ℝ))).min (ha.max (hb.max hc))

/-- A vanishing benchmark forces sample size times budget past every finite bound.  [the theorem's stated inputs and assumptions](hyp:he,hr), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:budgets). -/
-- @node: budget_diverges_of_rate_tendsto_zero
lemma budget_diverges_of_rate_tendsto_zero (budgets : ℕ → ℝ)
    (he : ∀ j, 2 ≤ j → 0 < budgets j)
    (hr : Tendsto (fun j => rate j (budgets j)) atTop (𝓝 0)) :
    Tendsto (fun j : ℕ => (j : ℝ) * budgets j) atTop atTop := by
  apply tendsto_atTop.2
  intro K
  let B : ℝ := max 1 K
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hsmall : 0 < min 1 (B ^ (-1 / 2 : ℝ)) :=
    lt_min zero_lt_one (Real.rpow_pos_of_pos hB _)
  filter_upwards [(tendsto_order.1 hr).2 _ hsmall, eventually_ge_atTop 2] with j hj hj2
  have hp : 0 < (j : ℝ) * budgets j := by
    have : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    exact mul_pos this (he j hj2)
  have hm := lt_of_le_of_lt (capped_dense_le_rate j (budgets j)) hj
  have hc : ((j : ℝ) * budgets j) ^ (-1 / 2 : ℝ) < B ^ (-1 / 2 : ℝ) := by
    by_contra hh
    have : min 1 (B ^ (-1 / 2 : ℝ)) ≤ min 1 (((j : ℝ) * budgets j) ^ (-1 / 2 : ℝ)) :=
      min_le_min_left 1 (le_of_not_gt hh)
    exact (not_lt_of_ge this) hm
  have hlt := (Real.rpow_lt_rpow_iff_of_neg hp hB (by norm_num : (-1 / 2 : ℝ) < 0)).mp hc
  exact (le_max_right 1 K).trans hlt.le

/-- The numerical benchmark vanishes exactly for diverging sample size times budget.  [the theorem's stated inputs and assumptions](hyp:he), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:budgets). -/
-- @node: rate_consistency_iff
lemma rate_consistency_iff (budgets : ℕ → ℝ)
    (he : ∀ j, 2 ≤ j → 0 < budgets j) :
    Tendsto (fun j => rate j (budgets j)) atTop (𝓝 0) ↔
      Tendsto (fun j : ℕ => (j : ℝ) * budgets j) atTop atTop := by
  exact ⟨budget_diverges_of_rate_tendsto_zero budgets he,
    rate_tendsto_zero_of_budget_diverges budgets he⟩

end CausalSmith.Stat.PrivateCateRoughdesign

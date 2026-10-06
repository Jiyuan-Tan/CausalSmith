module
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Gaussian summation over the selected dyadic scales

The geometric growth in the scale-union prefactor is dominated by the
exponential of geometric growth in the admissibility threshold. These are
the analytic series bounds in equation (10) of the adaptation roadmap.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open Filter

/-- Exponential decay in a geometrically increasing threshold dominates
any fixed geometric prefactor. -/
-- @node: geometricExponentialSeries_summable
lemma geometricExponentialSeries_summable (a b c : ℝ)
    (ha : 0 < a) (hb : 1 < b) (hc : 0 < c) :
    Summable (fun j : ℕ => a ^ j * Real.exp (-c * b ^ j)) := by
  have hlim : Tendsto (fun j : ℕ => a * Real.exp (-(c * (b - 1) * b ^ j)))
      atTop (nhds 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_pow_atTop_atTop_of_one_lt hb).const_mul_atTop
        (mul_pos hc (sub_pos.mpr hb)))).const_mul a
  apply summable_of_ratio_test_tendsto_lt_one (l := 0) (by norm_num)
  · exact Eventually.of_forall (fun j => by positivity)
  · convert hlim using 1
    ext j
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity),
      abs_of_pos (by positivity), pow_succ, pow_succ]
    rw [mul_div_mul_comm, mul_div_cancel_left₀ _ (ne_of_gt (pow_pos ha j)),
      ← Real.exp_sub]
    congr 2
    ring

/-- Split the product of the squared tail parameter and the scale threshold
to retain a Gaussian factor and a summable scale envelope. -/
-- @node: geometricExponentialSeries_factor
lemma geometricExponentialSeries_factor (a b c u : ℝ)
    (ha : 0 < a) (hb : 1 < b) (hc : 0 < c) (hu : 1 ≤ u) :
    (∑' j : ℕ, a ^ j * Real.exp (-c * u ^ 2 * b ^ j)) ≤
      Real.exp (-c * u ^ 2 / 2) *
        ∑' j : ℕ, a ^ j * Real.exp (-(c / 2) * b ^ j) := by
  have hterm (j : ℕ) :
      a ^ j * Real.exp (-c * u ^ 2 * b ^ j) ≤
        Real.exp (-c * u ^ 2 / 2) * (a ^ j * Real.exp (-(c / 2) * b ^ j)) := by
    have hu2 : 1 ≤ u ^ 2 := by nlinarith
    have hj : 1 ≤ b ^ j := one_le_pow₀ hb.le
    have hprod : u ^ 2 + b ^ j ≤ 2 * (u ^ 2 * b ^ j) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hu2) (sub_nonneg.mpr hj)]
    rw [mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg ha.le j)
    rw [← Real.exp_add]
    apply Real.exp_monotone
    nlinarith [mul_nonneg (sub_nonneg.mpr hprod) hc.le]
  have henv := (geometricExponentialSeries_summable a b (c / 2) ha hb
    (by positivity)).mul_left (Real.exp (-c * u ^ 2 / 2))
  calc
    _ ≤ ∑' j : ℕ, Real.exp (-c * u ^ 2 / 2) *
        (a ^ j * Real.exp (-(c / 2) * b ^ j)) :=
      (henv.of_nonneg_of_le (fun j => by positivity) hterm).tsum_le_tsum hterm henv
    _ = _ := tsum_mul_left

/-- The selected-scale union series has a Gaussian tail with constants
independent of the number of available scales. -/
-- @node: geometricExponentialSeries_gaussianTail
lemma geometricExponentialSeries_gaussianTail (a b c : ℝ)
    (ha : 0 < a) (hb : 1 < b) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : ℝ, 1 ≤ u →
      (∑' j : ℕ, a ^ j * Real.exp (-c * u ^ 2 * b ^ j)) ≤
        K * Real.exp (-c * u ^ 2 / 2) := by
  let S : ℝ := ∑' j : ℕ, a ^ j * Real.exp (-(c / 2) * b ^ j)
  have hS : 0 ≤ S := tsum_nonneg (fun j => by positivity)
  refine ⟨S + 1, by positivity, ?_⟩
  intro u hu
  apply (geometricExponentialSeries_factor a b c u ha hb hc hu).trans
  change Real.exp (-c * u ^ 2 / 2) * S ≤ _
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)

/-- Equation (10) in the paper's dyadic notation, retaining its inverse-power
tail prefactor and allowing any finite subset of selected scales. -/
-- @node: dyadicSelectedScaleSeries_gaussianTail
lemma dyadicSelectedScaleSeries_gaussianTail (A β q c : ℝ)
    (hβ : 0 < β) (hq : 0 < q) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s : Finset ℕ) (u : ℝ), 1 ≤ u →
      (∑ j ∈ s, u ^ (-(2 * q)) * (2 : ℝ) ^ ((j : ℝ) * A) *
        Real.exp (-c * u ^ 2 * (2 : ℝ) ^ (2 * β * j))) ≤
          K * Real.exp (-c * u ^ 2 / 2) := by
  have ha : 0 < (2 : ℝ) ^ A := by positivity
  have hb : 1 < (2 : ℝ) ^ (2 * β) :=
    Real.one_lt_rpow (by norm_num) (by positivity)
  obtain ⟨K, hK, htail⟩ := geometricExponentialSeries_gaussianTail
    ((2 : ℝ) ^ A) ((2 : ℝ) ^ (2 * β)) c ha hb hc
  refine ⟨K, hK, ?_⟩
  intro s u hu
  have hu0 : 0 < u := by linarith
  have hpref : u ^ (-(2 * q)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hu (by linarith)
  have hsum : Summable (fun j : ℕ => ((2 : ℝ) ^ A) ^ j *
      Real.exp (-c * u ^ 2 * ((2 : ℝ) ^ (2 * β)) ^ j)) :=
    by simpa only [neg_mul] using
      geometricExponentialSeries_summable _ _ (c * u ^ 2) ha hb (by positivity)
  calc
    _ ≤ ∑ j ∈ s, ((2 : ℝ) ^ A) ^ j *
        Real.exp (-c * u ^ 2 * ((2 : ℝ) ^ (2 * β)) ^ j) := by
      apply Finset.sum_le_sum
      intro j _
      rw [mul_comm (j : ℝ) A, Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
      have h := mul_le_mul_of_nonneg_right hpref
        (show 0 ≤ ((2 : ℝ) ^ A) ^ j *
          Real.exp (-c * u ^ 2 * ((2 : ℝ) ^ (2 * β)) ^ j) by positivity)
      simpa only [one_mul, mul_assoc] using h
    _ ≤ ∑' j : ℕ, ((2 : ℝ) ^ A) ^ j *
        Real.exp (-c * u ^ 2 * ((2 : ℝ) ^ (2 * β)) ^ j) :=
      hsum.sum_le_tsum s (fun _ _ => by positivity)
    _ ≤ _ := htail u hu

end CausalSmith.Stat.GlobalTailDesignRobustCate

module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.Construction
/-! The benchmark constraints and the dyadic public tuning variance envelope. -/
public section
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- A reciprocal-root lower bound is equivalent to the corresponding polynomial constraint. The result uses [the stated assumptions](hyp:hx,hm,_hr,h) and establishes [the displayed conclusion](goal). -/
-- @node: reciprocal_root_constraint
lemma reciprocal_root_constraint (x r : ℝ) (m : ℕ) (hx : 0 < x) (hm : 0 < m)
    (_hr : 0 ≤ r) (h : x ^ (-1 / (m : ℝ)) ≤ r) : 1 ≤ x * r^m := by
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg hx.le _) h m
  have heq : (x ^ (-1 / (m : ℝ))) ^ m = x⁻¹ := by
    rw [← Real.rpow_mul_natCast hx.le]
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [div_mul_cancel₀ _ hm', Real.rpow_neg_one]
  rw [heq] at hp
  have := mul_le_mul_of_nonneg_left hp hx.le
  simpa [hx.ne'] using this

/-- Below the public fallback threshold the cap is inactive, so each candidate scale bounds
its polynomial information constraint.  [the theorem's stated inputs and assumptions](hyp:he,hr), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,epsilon,hn). -/
-- @node: active_rate_constraints
lemma active_rate_constraints (n : ℕ) (epsilon : ℝ) (hn : 2 ≤ n)
    (he : 0 < epsilon) (hr : rate n epsilon < 1 / 8) :
    1 ≤ (n : ℝ) * (rate n epsilon)^4 ∧
    1 ≤ (n : ℝ)^2 * epsilon * (rate n epsilon)^7 ∧
    1 ≤ (n : ℝ) * epsilon * (rate n epsilon)^2 := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hr0 := (rate_pos n epsilon (by omega)).le
  have hcap : rate n epsilon = max ((n : ℝ)^(-1/4 : ℝ))
      (max (((n : ℝ)^2*epsilon)^(-1/7 : ℝ)) (((n : ℝ)*epsilon)^(-1/2 : ℝ))) := by
    unfold rate at hr ⊢
    exact min_eq_right (by rcases min_lt_iff.mp hr with h | h <;> linarith)
  have ha : (n : ℝ)^(-1/4 : ℝ) ≤ rate n epsilon := by
    rw [hcap]; exact le_max_left _ _
  have hb : ((n : ℝ)^2*epsilon)^(-1/7 : ℝ) ≤ rate n epsilon := by
    rw [hcap]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hc : ((n : ℝ)*epsilon)^(-1/2 : ℝ) ≤ rate n epsilon := by
    rw [hcap]; exact (le_max_right _ _).trans (le_max_right _ _)
  exact ⟨reciprocal_root_constraint _ _ 4 hn0 (by norm_num) hr0 ha,
    reciprocal_root_constraint _ _ 7 (by positivity) (by norm_num) hr0 hb,
    reciprocal_root_constraint _ _ 2 (by positivity) (by norm_num) hr0 hc⟩

/-- Dyadic rounding loses at most a factor of sixty-four in the occupancy scale.  [the theorem's stated inputs and assumptions](hyp:he,hr), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,epsilon,hn). -/
-- @node: tuned_info_lower
lemma tuned_info_lower (n : ℕ) (epsilon : ℝ) (hn : 2 ≤ n)
    (he : 0 < epsilon ∧ epsilon ≤ 1) (hr : rate n epsilon < 1 / 8) :
    min ((n : ℝ) * rate n epsilon) ((n : ℝ)^2 * (rate n epsilon)^6) / 64 ≤
      info n (tunedH n epsilon) (tunedK n epsilon) := by
  have hp := public_tuning_parameters n epsilon hn he hr
  have hb := tunedH_bounds n epsilon (by omega)
  have hr0 := (rate_pos n epsilon (by omega)).le
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h6 := pow_le_pow_left₀ (by positivity : 0 ≤ rate n epsilon / 2) hb.2.1 6
  have h1 : rate n epsilon / 64 ≤ tunedH n epsilon := by linarith
  have h6' : (rate n epsilon)^6 / 64 ≤ (tunedH n epsilon)^6 := by
    nlinarith [h6]
  have hi : info n (tunedH n epsilon) (tunedK n epsilon) =
      min ((n : ℝ) * tunedH n epsilon) ((n : ℝ)^2 * (tunedH n epsilon)^6) := by
    unfold info
    rw [hp.2.2.2.2, mul_min_of_nonneg]
    · congr 1 <;> ring
    · exact mul_nonneg hn0 hb.1.le
  rw [hi]
  apply le_min
  · calc
      _ ≤ ((n : ℝ) * rate n epsilon) / 64 :=
        div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left h1 hn0]
  · calc
      _ ≤ ((n : ℝ)^2 * (rate n epsilon)^6) / 64 :=
        div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left h6' (sq_nonneg (n : ℝ))]

/-- The three candidate rate constraints imply the two scaled information lower bounds used
by the public variance envelope.  [the theorem's stated inputs and assumptions](hyp:he,hr), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,epsilon,hn). -/
-- @node: tuned_scaled_info_lower
lemma tuned_scaled_info_lower (n : ℕ) (epsilon : ℝ) (hn : 2 ≤ n)
    (he : 0 < epsilon ∧ epsilon ≤ 1) (hr : rate n epsilon < 1 / 8) :
    1 / 64 ≤ (rate n epsilon)^2 * info n (tunedH n epsilon) (tunedK n epsilon) ∧
    1 / 64 ≤ rate n epsilon * epsilon * info n (tunedH n epsilon) (tunedK n epsilon) := by
  have hc := active_rate_constraints n epsilon hn he.1 hr
  have hi := tuned_info_lower n epsilon hn he hr
  have hr0 := (rate_pos n epsilon (by omega)).le
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h3 : 1 ≤ (n : ℝ) * (rate n epsilon)^3 := by
    have hpow : (rate n epsilon)^4 ≤ (rate n epsilon)^3 := by
      have := mul_le_mul_of_nonneg_left (show rate n epsilon ≤ 1 by linarith) (pow_nonneg hr0 3)
      nlinarith
    exact hc.1.trans (mul_le_mul_of_nonneg_left hpow hn0)
  have h8 : 1 ≤ (n : ℝ)^2 * (rate n epsilon)^8 := by
    nlinarith [sq_nonneg ((n : ℝ) * (rate n epsilon)^4 - 1)]
  constructor
  · have hm : 1 ≤ (rate n epsilon)^2 *
        min ((n : ℝ) * rate n epsilon) ((n : ℝ)^2 * (rate n epsilon)^6) := by
      rw [mul_min_of_nonneg _ _ (sq_nonneg _)]
      apply le_min <;> nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hi (sq_nonneg (rate n epsilon))]
  · have hm : 1 ≤ (rate n epsilon) * epsilon *
        min ((n : ℝ) * rate n epsilon) ((n : ℝ)^2 * (rate n epsilon)^6) := by
      rw [mul_min_of_nonneg _ _ (mul_nonneg hr0 he.1.le)]
      apply le_min <;> nlinarith [hc.2.1, hc.2.2]
    nlinarith [mul_le_mul_of_nonneg_left hi (mul_nonneg hr0 he.1.le)]

/-- The scaled information bounds control the inverse occupancy and inverse privacy scales.  [the theorem's stated inputs and assumptions](hyp:he,hr), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,epsilon,hn). -/
-- @node: tuned_inverse_info_upper
lemma tuned_inverse_info_upper (n : ℕ) (epsilon : ℝ) (hn : 2 ≤ n)
    (he : 0 < epsilon ∧ epsilon ≤ 1) (hr : rate n epsilon < 1 / 8) :
    (info n (tunedH n epsilon) (tunedK n epsilon))⁻¹ ≤ 64 * (rate n epsilon)^2 ∧
    (epsilon * info n (tunedH n epsilon) (tunedK n epsilon))^(-2 : ℤ) ≤
      4096 * (rate n epsilon)^2 := by
  have hp := public_tuning_parameters n epsilon hn he hr
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hh0 := hp.1
  have ha : 0 < info n (tunedH n epsilon) (tunedK n epsilon) := by
    unfold info
    rw [hp.2.2.2.2]
    positivity
  have hs := tuned_scaled_info_lower n epsilon hn he hr
  have hi : (info n (tunedH n epsilon) (tunedK n epsilon))⁻¹ ≤
      64 * (rate n epsilon)^2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ ha).mpr
    nlinarith [hs.1]
  have hea : 0 < epsilon * info n (tunedH n epsilon) (tunedK n epsilon) :=
    mul_pos he.1 ha
  have hie : (epsilon * info n (tunedH n epsilon) (tunedK n epsilon))⁻¹ ≤
      64 * rate n epsilon := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hea).mpr
    nlinarith [hs.2]
  refine ⟨hi, ?_⟩
  have hsq := pow_le_pow_left₀ (inv_nonneg.mpr hea.le) hie 2
  simpa only [zpow_neg, zpow_ofNat, inv_pow, mul_pow,
    show (64 : ℝ)^2 = 4096 by norm_num] using hsq

/-- At the tuned cell width, the roughness term equals the squared macro radius.  [the theorem's stated inputs and assumptions](hyp:he,hr), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,epsilon,hn). -/
-- @node: tuned_cell_roughness
lemma tuned_cell_roughness (n : ℕ) (epsilon : ℝ) (hn : 2 ≤ n)
    (he : 0 < epsilon ∧ epsilon ≤ 1) (hr : rate n epsilon < 1 / 8) :
    (cellWidth (tunedH n epsilon) (tunedK n epsilon))^(2/5 : ℝ) =
      (tunedH n epsilon)^2 := by
  have hp := public_tuning_parameters n epsilon hn he hr
  rw [hp.2.2.2.2, ← Real.rpow_natCast, ← Real.rpow_mul hp.1.le]
  norm_num

/-- The public tuning puts the entire second-moment envelope below the roadmap's squared-rate
constant, independently of the law or the statistical second-moment proof.  [the theorem's stated inputs and assumptions](hyp:he,hr), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,epsilon,hn). -/
-- @node: tuned_Vbound_le
lemma tuned_Vbound_le (n : ℕ) (epsilon : ℝ) (hn : 2 ≤ n)
    (he : 0 < epsilon ∧ epsilon ≤ 1) (hr : rate n epsilon < 1 / 8) :
    Vbound n epsilon (tunedH n epsilon) (tunedK n epsilon) ≤
      2^33 * (rate n epsilon)^2 := by
  have hi := tuned_inverse_info_upper n epsilon hn he hr
  have hb := tunedH_bounds n epsilon (by omega)
  have hsq := pow_le_pow_left₀ hb.1.le hb.2.2 2
  unfold Vbound
  rw [tuned_cell_roughness n epsilon hn he hr]
  nlinarith [hi.1, hi.2, sq_nonneg (rate n epsilon)]

end CausalSmith.Stat.PrivateCateRoughdesign

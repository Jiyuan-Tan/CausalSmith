module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Defs.Estimator

/-! Deterministic logarithm bounds for clipped factorial moments. -/

public section

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

/-- Logarithms are Lipschitz above a positive moment floor. -/
-- @node: log_difference_le_of_floor
lemma log_difference_le_of_floor {c x y : ℝ}
    (hc : 0 < c) (hx : c ≤ x) (hy : c ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / c := by
  have hx0 : 0 < x := lt_of_lt_of_le hc hx
  have hy0 : 0 < y := lt_of_lt_of_le hc hy
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hx0 hxy)),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    have hlog : Real.log y - Real.log x ≤ (y - x) / x := by
      rw [← Real.log_div hy0.ne' hx0.ne']
      have h := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
      convert h using 1; field_simp
    have hdiv := div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) hc hx
    simpa only [neg_sub] using hlog.trans hdiv
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hy0 hyx)),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    have hlog : Real.log x - Real.log y ≤ (x - y) / y := by
      rw [← Real.log_div hx0.ne' hy0.ne']
      have h := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
      convert h using 1; field_simp
    exact hlog.trans (div_le_div_of_nonneg_left (sub_nonneg.mpr hyx) hc hy)

/-- Clipping is inactive on a sufficiently accurate estimate, and the log
error is controlled by the unclipped moment error. -/
-- @node: clipped_log_difference_le
lemma clipped_log_difference_le {c x u τ : ℝ}
    (hc : 0 < c) (hu : 2 * c ≤ u)
    (hτ : 0 ≤ τ ∧ τ ≤ c) (happrox : |x - u| ≤ τ) :
    |Real.log (max c x) - Real.log u| ≤ τ / c := by
  have hx : c ≤ x := by
    have h := (abs_le.mp happrox).1
    linarith
  rw [max_eq_right hx]
  exact (log_difference_le_of_floor hc hx (by linarith : c ≤ u)).trans
    (div_le_div_of_nonneg_right happrox hc.le)

/-- Simultaneous raw factorial-moment errors control one clipped log-moment estimate. -/
-- @node: muHat_error_of_raw_moments
lemma muHat_error_of_raw_moments {p n : ℕ} (ℓ τ : ℝ)
    (δ : {x : ℝ // 0 < x ∧ x < 1 / 2})
    (U W : Fin (p + 1) → Fin n → Fin p → ℝ)
    (e : Fin (p + 1)) (j : Fin p) (u w : ℝ)
    (hℓ : 0 < ℓ) (hτ : 0 ≤ τ ∧ τ ≤ ℓ / 2 ∧ τ ≤ ℓ ^ 2 / 2)
    (hu : ℓ ≤ u) (hw : ℓ ^ 2 ≤ w)
    (hU : |medianOfMeans (momBlocks ((δ : ℝ) / (2 * p * (p + 1))))
      (fun r => U e r j) - u| ≤ τ)
    (hW : |medianOfMeans (momBlocks ((δ : ℝ) / (2 * p * (p + 1))))
      (fun r => W e r j) - w| ≤ τ) :
    |muHat ℓ δ U W e j - (2 * Real.log u - (1 / 2 : ℝ) * Real.log w)| ≤
      2 * (τ / (ℓ / 2)) + (1 / 2 : ℝ) * (τ / (ℓ ^ 2 / 2)) := by
  let x := medianOfMeans (momBlocks ((δ : ℝ) / (2 * p * (p + 1))))
    (fun r => U e r j)
  let y := medianOfMeans (momBlocks ((δ : ℝ) / (2 * p * (p + 1))))
    (fun r => W e r j)
  have hx : |Real.log (max (ℓ / 2) x) - Real.log u| ≤ τ / (ℓ / 2) :=
    clipped_log_difference_le (by positivity) (by linarith) ⟨hτ.1, hτ.2.1⟩ hU
  have hy : |Real.log (max (ℓ ^ 2 / 2) y) - Real.log w| ≤
      τ / (ℓ ^ 2 / 2) :=
    clipped_log_difference_le (by positivity) (by linarith) ⟨hτ.1, hτ.2.2⟩ hW
  change |(2 * Real.log (max (ℓ / 2) x) -
      (1 / 2 : ℝ) * Real.log (max (ℓ ^ 2 / 2) y)) -
      (2 * Real.log u - (1 / 2 : ℝ) * Real.log w)| ≤ _
  calc
    _ = |2 * (Real.log (max (ℓ / 2) x) - Real.log u) -
        (1 / 2 : ℝ) * (Real.log (max (ℓ ^ 2 / 2) y) - Real.log w)| := by ring
    _ ≤ |2 * (Real.log (max (ℓ / 2) x) - Real.log u)| +
        |(1 / 2 : ℝ) * (Real.log (max (ℓ ^ 2 / 2) y) - Real.log w)| :=
          abs_sub _ _
    _ = 2 * |Real.log (max (ℓ / 2) x) - Real.log u| +
        (1 / 2 : ℝ) * |Real.log (max (ℓ ^ 2 / 2) y) - Real.log w| := by
          simp [abs_mul]
    _ ≤ 2 * (τ / (ℓ / 2)) + (1 / 2 : ℝ) * (τ / (ℓ ^ 2 / 2)) := by
      gcongr

/-- Two clipped log-moment errors give the corresponding shift error. -/
-- @node: robustShift_error_of_raw_moments
lemma robustShift_error_of_raw_moments {p n : ℕ} (ℓ τ : ℝ)
    (δ : {x : ℝ // 0 < x ∧ x < 1 / 2})
    (S : Fin (p + 1) → Fin n → Fin p → ℝ)
    (X : Fin (p + 1) → Fin n → Fin p → ℕ)
    (u w : Fin (p + 1) → Fin p → ℝ)
    (hℓ : 0 < ℓ) (hτ : 0 ≤ τ ∧ τ ≤ ℓ / 2 ∧ τ ≤ ℓ ^ 2 / 2)
    (hfloor : ∀ e j, ℓ ≤ u e j ∧ ℓ ^ 2 ≤ w e j)
    (hraw : ∀ e j,
      |medianOfMeans (momBlocks ((δ : ℝ) / (2 * p * (p + 1))))
        (fun r => firstFactorial (X e r) (S e r) j) - u e j| ≤ τ ∧
      |medianOfMeans (momBlocks ((δ : ℝ) / (2 * p * (p + 1))))
        (fun r => secondFactorial (X e r) (S e r) j) - w e j| ≤ τ)
    (m j : Fin p) :
    |robustShiftEstimator ℓ δ S X m j -
      ((2 * Real.log (u m.succ j) - (1 / 2 : ℝ) * Real.log (w m.succ j)) -
       (2 * Real.log (u 0 j) - (1 / 2 : ℝ) * Real.log (w 0 j)))| ≤
      2 * (2 * (τ / (ℓ / 2)) + (1 / 2 : ℝ) * (τ / (ℓ ^ 2 / 2))) := by
  let U : Fin (p + 1) → Fin n → Fin p → ℝ :=
    fun e r i => firstFactorial (X e r) (S e r) i
  let W : Fin (p + 1) → Fin n → Fin p → ℝ :=
    fun e r i => secondFactorial (X e r) (S e r) i
  let a (e : Fin (p + 1)) :=
    2 * Real.log (u e j) - (1 / 2 : ℝ) * Real.log (w e j)
  let b := 2 * (τ / (ℓ / 2)) + (1 / 2 : ℝ) * (τ / (ℓ ^ 2 / 2))
  have hb (e : Fin (p + 1)) : |muHat ℓ δ U W e j - a e| ≤ b := by
    exact muHat_error_of_raw_moments ℓ τ δ U W e j (u e j) (w e j)
      hℓ hτ (hfloor e j).1 (hfloor e j).2 (hraw e j).1 (hraw e j).2
  change |(muHat ℓ δ U W m.succ j - muHat ℓ δ U W 0 j) -
    (a m.succ - a 0)| ≤ 2 * b
  calc
    _ = |(muHat ℓ δ U W m.succ j - a m.succ) -
        (muHat ℓ δ U W 0 j - a 0)| := by ring
    _ ≤ |muHat ℓ δ U W m.succ j - a m.succ| +
        |muHat ℓ δ U W 0 j - a 0| := abs_sub _ _
    _ ≤ 2 * b := by linarith [hb m.succ, hb 0]

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

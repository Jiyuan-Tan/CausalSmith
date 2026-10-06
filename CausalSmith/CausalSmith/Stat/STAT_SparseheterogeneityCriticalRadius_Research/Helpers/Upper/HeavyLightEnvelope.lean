module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.CoefficientGrowth

/-! Polynomial envelopes for the light audit weight beyond the light range. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open scoped BigOperators

/-- A polynomial with the `GK` coefficients is controlled by its coefficient
one-norm on a larger argument `y ≥ 1`. -/
lemma abs_GK_le_coeffSum_mul_pow {K : ℕ} (hK : 2 ≤ K)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : 1 ≤ y) :
    |GK K x| ≤
      (∑ ell ∈ Finset.range (K - 1), |gCoeff K ell|) * y ^ (K - 2) := by
  rw [GK]
  calc
    |∑ ell ∈ Finset.range (K - 1), gCoeff K ell * x ^ ell| ≤
        ∑ ell ∈ Finset.range (K - 1), |gCoeff K ell * x ^ ell| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ell ∈ Finset.range (K - 1),
          |gCoeff K ell| * y ^ (K - 2) := by
      gcongr with ell hell
      rw [abs_mul, abs_pow, abs_of_nonneg hx]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have hell' : ell ≤ K - 2 := by
        have := Finset.mem_range.mp hell
        omega
      exact (pow_le_pow_left₀ hx hxy _).trans
        (pow_le_pow_right₀ hy hell')
    _ = (∑ ell ∈ Finset.range (K - 1), |gCoeff K ell|) *
          y ^ (K - 2) := by
      rw [Finset.sum_mul]

/-- The light audit weight has the polynomial envelope used after (27). -/
lemma abs_lightAuditWeight_le_heavy_envelope {n : ℕ} (rho : ℝ)
    (P : Law n) (k : Fin n) (hn : 0 < n)
    (hheavy : lightScale n rho < P.cellMass k) :
    |lightAuditWeight n rho P k| ≤
      2 * lightScale n rho * (degree n rho : ℝ) *
        (2 : ℝ) ^ (4 * degree n rho) *
        (P.cellMass k / lightScale n rho) ^ degree n rho := by
  let B := lightScale n rho
  let K := degree n rho
  let p := P.cellMass k
  let x0 := armMass P false k / B
  let x1 := armMass P true k / B
  let y := p / B
  have hB : 0 < B := lightScale_pos n rho hn
  have hK : 2 ≤ K := by simp [K, degree]
  have hp0 : 0 ≤ p := by dsimp [p]; exact (P.cellMass_range k).1
  have hy : 1 ≤ y := by
    dsimp [y, p, B]
    exact (one_le_div hB).mpr hheavy.le
  have hx0 : 0 ≤ x0 := by
    dsimp [x0, armMass, B]
    have hpi := (P.propensity_range k)
    exact div_nonneg (mul_nonneg (P.cellMass_range k).1
      (sub_nonneg.mpr hpi.2)) hB.le
  have hx1 : 0 ≤ x1 := by
    dsimp [x1, armMass, B]
    have hpi := (P.propensity_range k)
    exact div_nonneg (mul_nonneg (P.cellMass_range k).1 hpi.1) hB.le
  have hx0y : x0 ≤ y := by
    apply (div_le_div_iff_of_pos_right hB).mpr
    dsimp [x0, y, armMass, p, B]
    have hpi := (P.propensity_range k)
    exact mul_le_of_le_one_right (P.cellMass_range k).1
      (sub_le_self 1 hpi.1)
  have hx1y : x1 ≤ y := by
    apply (div_le_div_iff_of_pos_right hB).mpr
    dsimp [x1, y, armMass, p, B]
    have hpi := (P.propensity_range k)
    exact mul_le_of_le_one_right (P.cellMass_range k).1 hpi.2
  let Gsum := ∑ ell ∈ Finset.range (K - 1), |gCoeff K ell|
  have hGK0 := abs_GK_le_coeffSum_mul_pow hK hx0 hx0y hy
  have hGK1 := abs_GK_le_coeffSum_mul_pow hK hx1 hx1y hy
  have hGsum : Gsum ≤ (K : ℝ) * (2 : ℝ) ^ (4 * K) :=
    sum_abs_gCoeff_le K hK
  have hGsum0 : 0 ≤ Gsum := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hxyprod : x0 * x1 ≤ y ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx0y) (sub_nonneg.mpr hx1y)]
  have hy0 : 0 ≤ y := le_trans zero_le_one hy
  rw [lightAuditWeight]
  change |B * x0 * x1 * (GK K x0 + GK K x1)| ≤ _
  calc
    _ ≤ B * (x0 * x1) * (|GK K x0| + |GK K x1|) := by
      simp only [abs_mul]
      rw [abs_of_nonneg hB.le,
        abs_of_nonneg hx0, abs_of_nonneg hx1]
      calc
        B * x0 * x1 * |GK K x0 + GK K x1| ≤
            B * x0 * x1 * (|GK K x0| + |GK K x1|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _)
            (mul_nonneg (mul_nonneg hB.le hx0) hx1)
        _ = B * (x0 * x1) * (|GK K x0| + |GK K x1|) := by ring
    _ ≤ B * y ^ 2 * (2 * Gsum * y ^ (K - 2)) := by
      have hsum : |GK K x0| + |GK K x1| ≤
          2 * Gsum * y ^ (K - 2) := by
        dsimp [Gsum] at hGK0 hGK1 ⊢
        linarith
      gcongr
    _ = 2 * B * Gsum * y ^ K := by
      have hsub : K - 2 + 2 = K := by omega
      rw [show y ^ K = y ^ (K - 2) * y ^ 2 by
        rw [← pow_add, hsub]]
      ring
    _ ≤ 2 * B * ((K : ℝ) * (2 : ℝ) ^ (4 * K)) * y ^ K := by
      gcongr
    _ = 2 * lightScale n rho * (degree n rho : ℝ) *
        (2 : ℝ) ^ (4 * degree n rho) *
        (P.cellMass k / lightScale n rho) ^ degree n rho := by
      dsimp [B, K, y, p]
      ring

/-- Heavy-regime light-component bias, ready to combine with the classifier tail. -/
lemma abs_lightAuditWeight_sub_cellMass_le_heavy_envelope {n : ℕ} (rho : ℝ)
    (P : Law n) (k : Fin n) (hn : 0 < n)
    (hheavy : lightScale n rho < P.cellMass k) :
    |lightAuditWeight n rho P k - P.cellMass k| ≤
      2 * lightScale n rho * (degree n rho : ℝ) *
          (2 : ℝ) ^ (4 * degree n rho) *
          (P.cellMass k / lightScale n rho) ^ degree n rho +
        P.cellMass k := by
  calc
    _ ≤ |lightAuditWeight n rho P k| + |P.cellMass k| := abs_sub _ _
    _ ≤ _ := by
      rw [abs_of_nonneg (P.cellMass_range k).1]
      gcongr
      exact abs_lightAuditWeight_le_heavy_envelope rho P k hn hheavy

/-- Completed third mass-regime pointwise bound: the polynomial envelope is
multiplied by the heavy-side classifier tail. -/
lemma upperAuditWeights_abs_bias_bound_heavy_envelope {n : ℕ} (rho : ℝ)
    (P : Law n) (k : Fin n) (hn : 0 < n) (hoverlap : FixedOverlap P)
    (hheavy : lightScale n rho < P.cellMass k) :
    |upperAuditWeights n rho P k - P.cellMass k| ≤
      Real.exp (-blockMean n * P.cellMass k / 8) *
        (2 * lightScale n rho * (degree n rho : ℝ) *
            (2 : ℝ) ^ (4 * degree n rho) *
            (P.cellMass k / lightScale n rho) ^ degree n rho +
          P.cellMass k) +
        P.cellMass k * Real.exp (-blockMean n * P.cellMass k / 4) := by
  calc
    _ ≤ Real.exp (-blockMean n * P.cellMass k / 8) *
          |lightAuditWeight n rho P k - P.cellMass k| +
        P.cellMass k * Real.exp (-blockMean n * P.cellMass k / 4) :=
      upperAuditWeights_abs_bias_bound_heavy rho P k hn hoverlap hheavy
    _ ≤ _ := by
      gcongr
      exact abs_lightAuditWeight_sub_cellMass_le_heavy_envelope
        rho P k hn hheavy

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

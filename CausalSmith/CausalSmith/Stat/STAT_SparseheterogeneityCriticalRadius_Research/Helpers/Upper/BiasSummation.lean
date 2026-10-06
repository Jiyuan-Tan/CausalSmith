module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.BiasNumeric

/-! Summation of the three pointwise audit-weight bias regimes. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open scoped BigOperators

lemma blockMean_pos (n : ℕ) (hn : 0 < n) : 0 < blockMean n := by
  simp only [blockMean, postPilotSize, pilotSize]
  have : 0 < n - n / 2 := by omega
  positivity

lemma blockMean_mul_lightScale (n : ℕ) (rho : ℝ) (hn : 0 < n) :
    blockMean n * lightScale n rho = 4096 * (degree n rho : ℝ) := by
  rw [lightScale]
  field_simp [ne_of_gt (blockMean_pos n hn)]

lemma sampleSize_div_blockMean_le_eight (n : ℕ) (hn : 0 < n) :
    (n : ℝ) / blockMean n ≤ 8 := by
  have hm := blockMean_pos n hn
  apply (div_le_iff₀ hm).mpr
  simp only [blockMean, postPilotSize, pilotSize]
  have hnat : n ≤ 2 * (n - n / 2) := by omega
  have hreal : (n : ℝ) ≤ 2 * (n - n / 2 : ℕ) := by exact_mod_cast hnat
  calc
    (n : ℝ) ≤ 2 * (n - n / 2 : ℕ) := hreal
    _ = 8 * ((n - n / 2 : ℕ) / 4 : ℝ) := by push_cast; ring

/-- A single cell, in any of the three mass regimes, obeys a summable envelope. -/
lemma upperAuditWeights_abs_bias_universal {n : ℕ} (rho : ℝ)
    (P : Law n) (k : Fin n) (hn : 0 < n) (hoverlap : FixedOverlap P) :
    |upperAuditWeights n rho P k - P.cellMass k| ≤
      6 * lightScale n rho / (degree n rho : ℝ) ^ 2 +
        4 * P.cellMass k / (degree n rho : ℝ) := by
  let B := lightScale n rho
  let K := degree n rho
  let p := P.cellMass k
  have hB : 0 < B := lightScale_pos n rho hn
  have hK : 2 ≤ K := by simp [K, degree]
  have hKpos : 0 < K := lt_of_lt_of_le (by omega) hK
  have hKr : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hp0 : 0 ≤ p := by dsimp [p]; exact (P.cellMass_range k).1
  by_cases hpB : p ≤ B
  · have hnonneg := upperAuditWeights_bias_nonneg_of_le_lightScale
      rho P k hn hoverlap hpB
    have habs : |upperAuditWeights n rho P k - p| =
        p - upperAuditWeights n rho P k := by
      rw [abs_sub_comm, abs_of_nonneg hnonneg]
    rw [habs]
    by_cases hsmall : p ≤ B / 64
    · have hpoint := upperAuditWeights_bias_bound_very_light
        rho P k hn hoverlap hsmall
      have hexp := light_classifier_exp_le_inv K hKpos
      calc
        _ ≤ 6 * B / (K : ℝ) ^ 2 +
            p * Real.exp ((1 - Real.log 4) * (256 * K : ℕ)) := hpoint.2
        _ ≤ 6 * B / (K : ℝ) ^ 2 + p * (1 / (K : ℝ)) := by
          gcongr
        _ ≤ 6 * B / (K : ℝ) ^ 2 + 4 * p / (K : ℝ) := by
          have : 0 ≤ p / (K : ℝ) := div_nonneg hp0 hKr.le
          rw [mul_one_div]
          have hmul := mul_le_mul_of_nonneg_right
            (show (1 : ℝ) ≤ 4 by norm_num) this
          have hmul' : p / (K : ℝ) ≤ 4 * (p / (K : ℝ)) := by
            simpa only [one_mul] using hmul
          calc
            _ ≤ 6 * B / (K : ℝ) ^ 2 + 4 * (p / (K : ℝ)) :=
              add_le_add le_rfl hmul'
            _ = _ := by ring
    · have hpoint := upperAuditWeights_bias_bound_transition
        rho P k hn hoverlap (lt_of_not_ge hsmall) hpB
      have hexp := exp_neg_sixteen_mul_le_inv K hKpos
      calc
        _ ≤ 6 * B / (K : ℝ) ^ 2 + p * Real.exp (-16 * (K : ℝ)) := hpoint.2
        _ ≤ 6 * B / (K : ℝ) ^ 2 + p * (1 / (K : ℝ)) := by
          gcongr
        _ ≤ 6 * B / (K : ℝ) ^ 2 + 4 * p / (K : ℝ) := by
          have : 0 ≤ p / (K : ℝ) := div_nonneg hp0 hKr.le
          rw [mul_one_div]
          have hmul := mul_le_mul_of_nonneg_right
            (show (1 : ℝ) ≤ 4 by norm_num) this
          have hmul' : p / (K : ℝ) ≤ 4 * (p / (K : ℝ)) := by
            simpa only [one_mul] using hmul
          calc
            _ ≤ 6 * B / (K : ℝ) ^ 2 + 4 * (p / (K : ℝ)) :=
              add_le_add le_rfl hmul'
            _ = _ := by ring
  · have hpB' : B < p := lt_of_not_ge hpB
    let y := p / B
    have hy : 1 ≤ y := (one_le_div hB).mpr hpB'.le
    have hy0 : 0 ≤ y := le_trans zero_le_one hy
    have hp_eq : p = B * y := by
      dsimp [y]
      field_simp
    have hmB := blockMean_mul_lightScale n rho hn
    have hmBK : blockMean n * B = 4096 * (K : ℝ) := by
      simpa [B, K] using hmB
    have hexp8 : -blockMean n * p / 8 = -512 * (K : ℝ) * y := by
      rw [hp_eq]
      calc
        -blockMean n * (B * y) / 8 = -(blockMean n * B) * y / 8 := by ring
        _ = _ := by rw [hmBK]; ring
    have hexp4 : -blockMean n * p / 4 ≤ -16 * (K : ℝ) := by
      rw [hp_eq]
      rw [show -blockMean n * (B * y) / 4 =
        -(blockMean n * B) * y / 4 by ring, hmBK]
      have : (0 : ℝ) ≤ K := hKr.le
      nlinarith
    have hdecay := heavy_polynomial_decay K hKpos hy
    have hsq := exp_neg_sixteen_mul_le_inv_sq K hKpos
    have hinv := exp_neg_sixteen_mul_le_inv K hKpos
    have hpoly :
        Real.exp (-blockMean n * p / 8) *
            (2 * B * (K : ℝ) * (2 : ℝ) ^ (4 * K) * y ^ K) ≤
          2 * p / (K : ℝ) := by
      have hscaled := mul_le_mul_of_nonneg_left hdecay
        (mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hB.le) hKr.le)
      rw [hexp8]
      calc
        Real.exp (-512 * (K : ℝ) * y) *
            (2 * B * (K : ℝ) * (2 : ℝ) ^ (4 * K) * y ^ K) =
            (2 * B * (K : ℝ)) *
              (Real.exp (-512 * (K : ℝ) * y) *
                ((2 : ℝ) ^ (4 * K) * y ^ K)) := by ring
        _ ≤ (2 * B * (K : ℝ)) * Real.exp (-16 * (K : ℝ)) := hscaled
        _ ≤ (2 * B * (K : ℝ)) * (1 / (K : ℝ)) ^ 2 := by gcongr
        _ = 2 * B / (K : ℝ) := by field_simp
        _ ≤ 2 * p / (K : ℝ) := by gcongr
    have hexp8inv : Real.exp (-blockMean n * p / 8) ≤ 1 / (K : ℝ) := by
      rw [hexp8]
      calc
        _ ≤ Real.exp (-16 * (K : ℝ)) := by
          apply Real.exp_le_exp.mpr
          have : (0 : ℝ) ≤ K := hKr.le
          nlinarith [mul_nonneg this (sub_nonneg.mpr hy)]
        _ ≤ _ := hinv
    have hexp4inv : Real.exp (-blockMean n * p / 4) ≤ 1 / (K : ℝ) := by
      calc
        _ ≤ Real.exp (-16 * (K : ℝ)) := Real.exp_le_exp.mpr hexp4
        _ ≤ _ := hinv
    have hpoint := upperAuditWeights_abs_bias_bound_heavy_envelope
      rho P k hn hoverlap hpB'
    calc
      _ ≤ Real.exp (-blockMean n * P.cellMass k / 8) *
          (2 * lightScale n rho * (degree n rho : ℝ) *
              (2 : ℝ) ^ (4 * degree n rho) *
              (P.cellMass k / lightScale n rho) ^ degree n rho +
            P.cellMass k) +
          P.cellMass k * Real.exp (-blockMean n * P.cellMass k / 4) := hpoint
      _ ≤ 4 * P.cellMass k / (degree n rho : ℝ) := by
        rw [mul_add]
        have hpInv8 := mul_le_mul_of_nonneg_left hexp8inv hp0
        have hpInv4 := mul_le_mul_of_nonneg_left hexp4inv hp0
        dsimp [B, K, p, y] at hpoly hpInv8 hpInv4
        rw [mul_one_div] at hpInv8 hpInv4
        have hpInv8' : Real.exp (-blockMean n * P.cellMass k / 8) *
            P.cellMass k ≤ P.cellMass k / (degree n rho : ℝ) := by
          simpa [mul_comm] using hpInv8
        calc
          Real.exp (-blockMean n * P.cellMass k / 8) *
                (2 * lightScale n rho * (degree n rho : ℝ) *
                  (2 : ℝ) ^ (4 * degree n rho) *
                  (P.cellMass k / lightScale n rho) ^ degree n rho) +
              Real.exp (-blockMean n * P.cellMass k / 8) * P.cellMass k +
              P.cellMass k * Real.exp (-blockMean n * P.cellMass k / 4) ≤
            2 * P.cellMass k / (degree n rho : ℝ) +
              P.cellMass k / (degree n rho : ℝ) +
              P.cellMass k / (degree n rho : ℝ) :=
            add_le_add (add_le_add hpoly hpInv8') hpInv4
          _ = _ := by ring
      _ ≤ 6 * lightScale n rho / (degree n rho : ℝ) ^ 2 +
          4 * P.cellMass k / (degree n rho : ℝ) := by
        have : 0 ≤ 6 * lightScale n rho / (degree n rho : ℝ) ^ 2 := by
          positivity
        linarith

/-- Global partition sum, equation (28), with an explicit conservative constant. -/
lemma audit_weight_bias_bound_explicit {n : ℕ} (rho : ℝ) (P : Law n)
    (hn : 0 < n) (hoverlap : FixedOverlap P) :
    (∑ k : Fin n, |upperAuditWeights n rho P k - P.cellMass k|) ≤
      196612 / (degree n rho : ℝ) := by
  let K := degree n rho
  have hK : 2 ≤ K := by simp [K, degree]
  have hKr : (0 : ℝ) < K := by positivity
  calc
    _ ≤ ∑ k : Fin n,
        (6 * lightScale n rho / (K : ℝ) ^ 2 +
          4 * P.cellMass k / (K : ℝ)) := by
      gcongr with k
      exact upperAuditWeights_abs_bias_universal rho P k hn hoverlap
    _ = (n : ℝ) * (6 * lightScale n rho / (K : ℝ) ^ 2) +
          4 / (K : ℝ) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      simp_rw [show ∀ x : Fin n, 4 * P.cellMass x / (K : ℝ) =
        P.cellMass x * (4 / (K : ℝ)) by intro x; ring]
      rw [← Finset.sum_mul,
        DiscreteAteHeterogeneityFrontier.sum_cellMass_eq_one]
      ring
    _ ≤ 196608 / (K : ℝ) + 4 / (K : ℝ) := by
      have hratio := sampleSize_div_blockMean_le_eight n hn
      rw [lightScale]
      have hmain :
        (n : ℝ) * (6 * (4096 * (degree n rho : ℝ) / blockMean n) /
            (K : ℝ) ^ 2) =
            24576 * ((n : ℝ) / blockMean n) / (K : ℝ) := by
          dsimp [K]
          field_simp
          ring
      have hle : (n : ℝ) *
          (6 * (4096 * (degree n rho : ℝ) / blockMean n) / (K : ℝ) ^ 2) ≤
          196608 / (K : ℝ) := by
        rw [hmain]
        calc
          _ ≤ 24576 * 8 / (K : ℝ) := by gcongr
          _ = 196608 / (K : ℝ) := by ring
      exact add_le_add hle le_rfl
    _ = 196612 / (degree n rho : ℝ) := by
      dsimp [K]
      ring

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.ClassifierTail

/-! Pointwise bias envelopes for the three classifier mass regimes. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory Set

/-- Exact convex decomposition of the population audit-weight bias. -/
lemma cellMass_sub_upperAuditWeights {n : ℕ} (rho : ℝ) (P : Law n)
    (k : Fin n) :
    P.cellMass k - upperAuditWeights n rho P k =
      classificationProbability n rho P k *
          (P.cellMass k - lightAuditWeight n rho P k) +
        (1 - classificationProbability n rho P k) *
          (P.cellMass k - heavyAuditWeight n P k) := by
  simp only [upperAuditWeights]
  ring

/-- A convex combination cannot enlarge the sum of the two absolute errors. -/
lemma upperAuditWeights_abs_bias_le {n : ℕ} (rho : ℝ) (P : Law n)
    (k : Fin n) :
    |upperAuditWeights n rho P k - P.cellMass k| ≤
      classificationProbability n rho P k *
          |lightAuditWeight n rho P k - P.cellMass k| +
        (1 - classificationProbability n rho P k) *
          |heavyAuditWeight n P k - P.cellMass k| := by
  obtain ⟨ha0, ha1⟩ := classificationProbability_mem_Icc rho P k
  have hdecomp :
      upperAuditWeights n rho P k - P.cellMass k =
        classificationProbability n rho P k *
            (lightAuditWeight n rho P k - P.cellMass k) +
          (1 - classificationProbability n rho P k) *
            (heavyAuditWeight n P k - P.cellMass k) := by
    simp only [upperAuditWeights]
    ring
  rw [hdecomp]
  calc
    _ ≤ |classificationProbability n rho P k *
            (lightAuditWeight n rho P k - P.cellMass k)| +
          |(1 - classificationProbability n rho P k) *
            (heavyAuditWeight n P k - P.cellMass k)| := abs_add_le _ _
    _ = _ := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha0,
        abs_of_nonneg (sub_nonneg.mpr ha1)]

/-- In every range where the reciprocal-polynomial certificate applies, the
mixed audit weight remains below the cell mass. -/
lemma upperAuditWeights_bias_nonneg_of_le_lightScale {n : ℕ} (rho : ℝ)
    (P : Law n) (k : Fin n) (hn : 0 < n) (hoverlap : FixedOverlap P)
    (hlight : P.cellMass k ≤ lightScale n rho) :
    0 ≤ P.cellMass k - upperAuditWeights n rho P k := by
  rw [cellMass_sub_upperAuditWeights rho P k]
  obtain ⟨ha0, ha1⟩ := classificationProbability_mem_Icc rho P k
  have hL := (lightAuditWeight_bias_bound rho P k hn hoverlap hlight).1
  have hH := (heavyAuditWeight_bias_bound P k hn hoverlap).1
  positivity

/-- First mass regime in the proof of (28): `p ≤ B/64`. -/
lemma upperAuditWeights_bias_bound_very_light {n : ℕ} (rho : ℝ)
    (P : Law n) (k : Fin n) (hn : 0 < n) (hoverlap : FixedOverlap P)
    (hlight : P.cellMass k ≤ lightScale n rho / 64) :
    0 ≤ P.cellMass k - upperAuditWeights n rho P k ∧
      P.cellMass k - upperAuditWeights n rho P k ≤
        6 * lightScale n rho / (degree n rho : ℝ) ^ 2 +
          P.cellMass k *
            Real.exp ((1 - Real.log 4) * (256 * degree n rho : ℕ)) := by
  have hB : 0 < lightScale n rho := lightScale_pos n rho hn
  have hscale : P.cellMass k ≤ lightScale n rho := by
    have : lightScale n rho / 64 ≤ lightScale n rho := by nlinarith
    exact hlight.trans this
  have hL := lightAuditWeight_bias_bound rho P k hn hoverlap hscale
  have hH := heavyAuditWeight_bias_bound P k hn hoverlap
  obtain ⟨ha0, ha1⟩ := classificationProbability_mem_Icc rho P k
  have herr := light_classification_error_bound rho P k hn hlight
  have hexp_le_one :
      Real.exp (-blockMean n * P.cellMass k / 4) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have hp0 := (P.cellMass_range k).1
    have hm : 0 ≤ blockMean n := by
      simp only [blockMean]
      positivity
    nlinarith
  rw [cellMass_sub_upperAuditWeights rho P k]
  constructor
  · exact add_nonneg (mul_nonneg ha0 hL.1)
      (mul_nonneg (sub_nonneg.mpr ha1) hH.1)
  · calc
      _ ≤ classificationProbability n rho P k *
              (6 * lightScale n rho / (degree n rho : ℝ) ^ 2) +
            (1 - classificationProbability n rho P k) *
              (P.cellMass k *
                Real.exp (-blockMean n * P.cellMass k / 4)) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hL.2 ha0)
          (mul_le_mul_of_nonneg_left hH.2 (sub_nonneg.mpr ha1))
      _ ≤ 6 * lightScale n rho / (degree n rho : ℝ) ^ 2 +
            (1 - classificationProbability n rho P k) * P.cellMass k := by
        have hK : 0 < degree n rho := by simp [degree]
        have hbound0 : 0 ≤ 6 * lightScale n rho /
            (degree n rho : ℝ) ^ 2 := by positivity
        have hp0 := (P.cellMass_range k).1
        have hfirst : classificationProbability n rho P k *
              (6 * lightScale n rho / (degree n rho : ℝ) ^ 2) ≤
            6 * lightScale n rho / (degree n rho : ℝ) ^ 2 := by
          nlinarith
        have hsecond : (1 - classificationProbability n rho P k) *
              (P.cellMass k * Real.exp (-blockMean n * P.cellMass k / 4)) ≤
            (1 - classificationProbability n rho P k) * P.cellMass k := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_of_le_one_right hp0 hexp_le_one) (sub_nonneg.mpr ha1)
        linarith
      _ ≤ _ := by
        have hp0 := (P.cellMass_range k).1
        have h := add_le_add_left (mul_le_mul_of_nonneg_right herr hp0)
          (6 * lightScale n rho / (degree n rho : ℝ) ^ 2)
        nlinarith

/-- Second mass regime in the proof of (28): `B/64 < p ≤ B`. -/
lemma upperAuditWeights_bias_bound_transition {n : ℕ} (rho : ℝ)
    (P : Law n) (k : Fin n) (hn : 0 < n) (hoverlap : FixedOverlap P)
    (hlower : lightScale n rho / 64 < P.cellMass k)
    (hupper : P.cellMass k ≤ lightScale n rho) :
    0 ≤ P.cellMass k - upperAuditWeights n rho P k ∧
      P.cellMass k - upperAuditWeights n rho P k ≤
        6 * lightScale n rho / (degree n rho : ℝ) ^ 2 +
          P.cellMass k * Real.exp (-16 * (degree n rho : ℝ)) := by
  have hL := lightAuditWeight_bias_bound rho P k hn hoverlap hupper
  have hH := heavyAuditWeight_bias_bound P k hn hoverlap
  obtain ⟨ha0, ha1⟩ := classificationProbability_mem_Icc rho P k
  have hm : 0 < blockMean n := by
    simp only [blockMean, postPilotSize, pilotSize]
    have : 0 < n - n / 2 := by omega
    positivity
  have hexp : Real.exp (-blockMean n * P.cellMass k / 4) ≤
      Real.exp (-16 * (degree n rho : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hlower' := (div_lt_iff₀ (show (0 : ℝ) < 64 by norm_num)).mp hlower
    simp only [lightScale] at hlower'
    have hmul := (div_lt_iff₀ hm).mp hlower'
    nlinarith
  rw [cellMass_sub_upperAuditWeights rho P k]
  constructor
  · exact add_nonneg (mul_nonneg ha0 hL.1)
      (mul_nonneg (sub_nonneg.mpr ha1) hH.1)
  · calc
      _ ≤ classificationProbability n rho P k *
              (6 * lightScale n rho / (degree n rho : ℝ) ^ 2) +
            (1 - classificationProbability n rho P k) *
              (P.cellMass k * Real.exp (-blockMean n * P.cellMass k / 4)) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hL.2 ha0)
          (mul_le_mul_of_nonneg_left hH.2 (sub_nonneg.mpr ha1))
      _ ≤ 6 * lightScale n rho / (degree n rho : ℝ) ^ 2 +
            P.cellMass k * Real.exp (-16 * (degree n rho : ℝ)) := by
        have hK : 0 < degree n rho := by simp [degree]
        have hB : 0 < lightScale n rho := lightScale_pos n rho hn
        have hbound0 : 0 ≤ 6 * lightScale n rho /
            (degree n rho : ℝ) ^ 2 := by positivity
        have hp0 := (P.cellMass_range k).1
        have he0 : 0 ≤ Real.exp (-blockMean n * P.cellMass k / 4) :=
          Real.exp_nonneg _
        have hfirst : classificationProbability n rho P k *
              (6 * lightScale n rho / (degree n rho : ℝ) ^ 2) ≤
            6 * lightScale n rho / (degree n rho : ℝ) ^ 2 := by
          nlinarith
        have hsecond : (1 - classificationProbability n rho P k) *
              (P.cellMass k * Real.exp (-blockMean n * P.cellMass k / 4)) ≤
            P.cellMass k * Real.exp (-16 * (degree n rho : ℝ)) := by
          calc
            _ ≤ P.cellMass k *
                Real.exp (-blockMean n * P.cellMass k / 4) := by
              nlinarith [mul_nonneg hp0 he0]
            _ ≤ _ := mul_le_mul_of_nonneg_left hexp hp0
        linarith

/-- Third mass regime in the proof of (28).  This isolates precisely the
remaining coefficient-growth task: the light-weight error is multiplied by
the exponentially small heavy-side classifier probability. -/
lemma upperAuditWeights_abs_bias_bound_heavy {n : ℕ} (rho : ℝ)
    (P : Law n) (k : Fin n) (hn : 0 < n) (hoverlap : FixedOverlap P)
    (hheavy : lightScale n rho < P.cellMass k) :
    |upperAuditWeights n rho P k - P.cellMass k| ≤
      Real.exp (-blockMean n * P.cellMass k / 8) *
          |lightAuditWeight n rho P k - P.cellMass k| +
        P.cellMass k * Real.exp (-blockMean n * P.cellMass k / 4) := by
  have hconvex := upperAuditWeights_abs_bias_le rho P k
  obtain ⟨ha0, ha1⟩ := classificationProbability_mem_Icc rho P k
  have herr := heavy_classification_error_bound rho P k hn hheavy
  have hH := heavyAuditWeight_bias_bound P k hn hoverlap
  have habsH : |heavyAuditWeight n P k - P.cellMass k| =
      P.cellMass k - heavyAuditWeight n P k := by
    rw [abs_sub_comm, abs_of_nonneg hH.1]
  rw [habsH] at hconvex
  calc
    _ ≤ classificationProbability n rho P k *
          |lightAuditWeight n rho P k - P.cellMass k| +
        (1 - classificationProbability n rho P k) *
          (P.cellMass k - heavyAuditWeight n P k) := hconvex
    _ ≤ Real.exp (-blockMean n * P.cellMass k / 8) *
          |lightAuditWeight n rho P k - P.cellMass k| +
        P.cellMass k * Real.exp (-blockMean n * P.cellMass k / 4) := by
      have habs0 : 0 ≤ |lightAuditWeight n rho P k - P.cellMass k| := abs_nonneg _
      have hH0 := hH.1
      nlinarith

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

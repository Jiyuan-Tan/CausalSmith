module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedLinearPushforward

/-! # Density assembly for the beta-one affine mesh map -/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable def linearCellDensity (k : ℕ) (h eps c : ℝ) (y : ℝ) : ℝ≥0∞ :=
  ∑ i : Fin 7, (Set.Icc (linearCellLower k h eps c i)
    (linearCellUpper k h eps c i)).indicator (fun _ => linearCellWeight h eps c i) y

noncomputable def linearMeshDensity (q : ℕ) (h eps : ℝ) (c : ℕ → ℝ)
    (y : ℝ) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range q, ENNReal.ofReal h * linearCellDensity k h eps (c k) y

@[fun_prop]
lemma measurable_linearCellDensity (k : ℕ) (h eps c : ℝ) :
    Measurable (linearCellDensity k h eps c) := by
  unfold linearCellDensity
  exact Finset.measurable_sum _ fun i _ =>
    measurable_const.indicator measurableSet_Icc

@[fun_prop]
lemma measurable_linearMeshDensity (q : ℕ) (h eps : ℝ) (c : ℕ → ℝ) :
    Measurable (linearMeshDensity q h eps c) := by
  unfold linearMeshDensity
  fun_prop

lemma smul_linearCellMixture_eq_withDensity (r : ℝ≥0∞) (k : ℕ)
    (h eps c : ℝ) :
    r • intervalMixture (linearCellWeight h eps c)
        (linearCellLower k h eps c) (linearCellUpper k h eps c) =
      (volume : Measure ℝ).withDensity
        (fun y => r * linearCellDensity k h eps c y) := by
  rw [intervalMixture_def]
  ext s hs
  simp only [Measure.smul_apply, Measure.finsetSum_apply, withDensity_apply _ hs,
    linearCellDensity]
  rw [MeasureTheory.lintegral_const_mul, MeasureTheory.lintegral_finsetSum]
  · apply congrArg
    apply Finset.sum_congr rfl
    intro i hi
    rw [← withDensity_apply _ hs,
      MeasureTheory.withDensity_indicator measurableSet_Icc,
      MeasureTheory.withDensity_const, Measure.smul_apply]
  · exact fun i _ => measurable_const.indicator measurableSet_Icc
  · exact Finset.measurable_sum _ fun i _ =>
      measurable_const.indicator measurableSet_Icc

/-- A reciprocal mesh of beta-one cells has the explicit finite density. -/
lemma map_linear_mesh_eq_withDensity (q : ℕ) (hq : 0 < q) {h eps : ℝ}
    (hhq : h = (q : ℝ)⁻¹) (c : ℕ → ℝ)
    (hc : ∀ k, c k ∈ Set.Icc (-1 : ℝ) 1)
    (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 128)
    {F : ℝ → ℝ} (hF : Measurable F)
    (hcell : ∀ k < q, ∀ x ∈ Set.Icc ((k : ℝ) * h) (((k : ℝ) + 1) * h),
      F x = linearFoldedCell k h eps (c k) (x / h - k)) :
    Measure.map F ((volume : Measure ℝ).restrict (Set.Icc 0 1)) =
      (volume : Measure ℝ).withDensity (linearMeshDensity q h eps c) := by
  rw [map_eq_sum_linearFoldedCells q hq hhq c hF hcell]
  have hh : 0 < h := by rw [hhq]; positivity
  simp_rw [map_linearFoldedCell_eq_intervalMixture _ hh heps0 heps (hc _)]
  simp_rw [smul_linearCellMixture_eq_withDensity]
  ext s hs
  simp only [Measure.finsetSum_apply, withDensity_apply _ hs, linearMeshDensity]
  rw [MeasureTheory.lintegral_finsetSum]
  intro k hk
  exact (measurable_linearCellDensity k h eps (c k)).const_mul
    (ENNReal.ofReal h)

lemma linearCellWeight_physical_toReal {h eps c : ℝ}
    (hh : 0 < h) (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 128)
    (hc : c ∈ Set.Icc (-1 : ℝ) 1) (i : Fin 7) :
    (ENNReal.ofReal h * linearCellWeight h eps c i).toReal =
      h / (linearFoldedBranches h eps c i).slope := by
  have hs := linearFoldedBranches_slope_pos hh heps0 heps hc i
  simp [linearCellWeight, ENNReal.toReal_ofReal hh.le,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hs.le), div_eq_mul_inv]

/-- Every physical branch Jacobian differs from the baseline density two by
at most `256 * eps`, uniformly in the transverse coefficient. -/
lemma linearCellWeight_physical_error {h eps c : ℝ}
    (hh : 0 < h) (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 128)
    (hc : c ∈ Set.Icc (-1 : ℝ) 1) (i : Fin 7) :
    |(ENNReal.ofReal h * linearCellWeight h eps c i).toReal - 2| ≤
      256 * eps := by
  rw [linearCellWeight_physical_toReal hh heps0 heps hc i]
  have hec_lo : -(1 / 128 : ℝ) ≤ eps * c := by
    nlinarith [mul_le_mul_of_nonneg_left hc.1 heps0]
  have hec_hi : eps * c ≤ 1 / 128 := by
    nlinarith [mul_le_mul_of_nonneg_left hc.2 heps0]
  have hrec (t : ℝ) (htlo : -(1 / 4 : ℝ) ≤ t) (hthi : t ≤ 1 / 4)
      (htabs : |t| ≤ 32 * eps) :
      |1 / (1 / 2 + t) - 2| ≤ 256 * eps := by
    have hden : 0 < (1 / 2 : ℝ) + t := by linarith
    rw [show 1 / (1 / 2 + t) - 2 = (-2 * t) / (1 / 2 + t) by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have hinv : ((1 / 2 : ℝ) + t) * ((1 / 2 : ℝ) + t)⁻¹ = 1 :=
        mul_inv_cancel₀ hden.ne'
      ring_nf at hinv ⊢
      nlinarith]
    rw [abs_div, abs_of_pos hden, abs_mul]
    norm_num
    apply (div_le_iff₀ hden).2
    nlinarith [abs_nonneg t]
  fin_cases i <;> simp [linearFoldedBranches]
  · rw [show h / (h / 2) = (2 : ℝ) by field_simp [hh.ne']]
    simpa using mul_nonneg (show (0 : ℝ) ≤ 256 by norm_num) heps0
  · rw [show h / (h / 2) = (2 : ℝ) by field_simp [hh.ne']]
    simpa using mul_nonneg (show (0 : ℝ) ≤ 256 by norm_num) heps0
  · rw [show h / (h / 2 + 32 * eps * h * c) =
        1 / (1 / 2 + 32 * (eps * c)) by field_simp [hh.ne']]
    apply hrec
    · nlinarith
    · nlinarith
    · have ht : |32 * (eps * c)| = 32 * eps * |c| := by
        rw [abs_mul, abs_mul, abs_of_nonneg heps0]
        norm_num; ring
      have hcabs : |c| ≤ 1 := (abs_le).2 hc
      rw [ht]
      nlinarith [mul_nonneg heps0 (abs_nonneg c)]
  · rw [show h / (h / 2) = (2 : ℝ) by field_simp [hh.ne']]
    simpa using mul_nonneg (show (0 : ℝ) ≤ 256 by norm_num) heps0
  · rw [show h / (h / 2 - 32 * eps * h * c) =
        1 / (1 / 2 + 32 * (eps * (-c))) by
          rw [show h / (h / 2 - 32 * eps * h * c) =
            1 / (1 / 2 - 32 * eps * c) by field_simp [hh.ne']]
          congr 2 <;> ring]
    apply hrec
    · nlinarith
    · nlinarith
    · have ht : |32 * (eps * -c)| = 32 * eps * |c| := by
        rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg heps0]
        norm_num; ring
      have hcabs : |c| ≤ 1 := (abs_le).2 hc
      rw [ht]
      nlinarith [mul_nonneg heps0 (abs_nonneg c)]
  · rw [show h / (h / 2) = (2 : ℝ) by field_simp [hh.ne']]
    simpa using mul_nonneg (show (0 : ℝ) ≤ 256 by norm_num) heps0
  · rw [show h / (h / 2) = (2 : ℝ) by field_simp [hh.ne']]
    simpa using mul_nonneg (show (0 : ℝ) ≤ 256 by norm_num) heps0

end CausalSmith.Experimentation.PilotscorePairingFrontier

module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedLinearDensity

/-! # Uniform density bounds for beta-one affine cells -/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable def linearCellCountDensity (k : ℕ) (h eps c : ℝ) (y : ℝ) : ℝ≥0∞ :=
  ∑ i : Fin 7, (Set.Icc (linearCellLower k h eps c i)
    (linearCellUpper k h eps c i)).indicator (fun _ => 1) y

@[fun_prop]
lemma measurable_linearCellCountDensity (k : ℕ) (h eps c : ℝ) :
    Measurable (linearCellCountDensity k h eps c) := by
  unfold linearCellCountDensity
  exact Finset.measurable_sum _ fun i _ =>
    measurable_const.indicator measurableSet_Icc

lemma linearCell_interval_partition (k : ℕ) {h eps c : ℝ}
    (hh : 0 < h) (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 128)
    (hc : c ∈ Set.Icc (-1 : ℝ) 1) :
    ∑ i : Fin 7, (volume : Measure ℝ).restrict
        (Set.Icc (linearCellLower k h eps c i) (linearCellUpper k h eps c i)) =
      volume.restrict (Set.Icc (1 / 4 + (k : ℝ) * h / 2)
        (1 / 4 + ((k : ℝ) + 1) * h / 2)) := by
  let b0 : ℝ := 1 / 4 + (k : ℝ) * h / 2
  let b1 : ℝ := b0 + h / 8
  let b2 : ℝ := b0 + 13 * h / 64
  let b3 : ℝ := b0 + 7 * h / 32 + eps * h * c
  let b4 : ℝ := b0 + 9 * h / 32 + eps * h * c
  let b5 : ℝ := b0 + 19 * h / 64
  let b6 : ℝ := b0 + 3 * h / 8
  let b7 : ℝ := b0 + h / 2
  have hec_lo : -(1 / 128 : ℝ) ≤ eps * c := by
    nlinarith [mul_le_mul_of_nonneg_left hc.1 heps0]
  have hec_hi : eps * c ≤ 1 / 128 := by
    nlinarith [mul_le_mul_of_nonneg_left hc.2 heps0]
  have h01 : b0 ≤ b1 := by dsimp [b1]; nlinarith
  have h12 : b1 ≤ b2 := by dsimp [b1, b2]; nlinarith
  have h23 : b2 ≤ b3 := by
    dsimp [b2, b3]
    have hz : 0 ≤ (1 / 64 : ℝ) + eps * c := by nlinarith
    nlinarith [mul_nonneg hh.le hz]
  have h34 : b3 ≤ b4 := by dsimp [b3, b4]; nlinarith
  have h45 : b4 ≤ b5 := by
    dsimp [b4, b5]
    nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hec_hi)]
  have h56 : b5 ≤ b6 := by dsimp [b5, b6]; nlinarith
  have h67 : b6 ≤ b7 := by dsimp [b6, b7]; nlinarith
  have hs1 := volume_restrict_Icc_split h01 (h12.trans (h23.trans
    (h34.trans (h45.trans (h56.trans h67)))))
  have hs2 := volume_restrict_Icc_split h12 (h23.trans
    (h34.trans (h45.trans (h56.trans h67))))
  have hs3 := volume_restrict_Icc_split h23 (h34.trans
    (h45.trans (h56.trans h67)))
  have hs4 := volume_restrict_Icc_split h34 (h45.trans (h56.trans h67))
  have hs5 := volume_restrict_Icc_split h45 (h56.trans h67)
  have hs6 := volume_restrict_Icc_split h56 h67
  change (∑ i : Fin 7, volume.restrict (Set.Icc _ _)) = _
  simp [Fin.sum_univ_succ, linearCellLower, linearCellUpper,
    linearFoldedBranches, b0, b1, b2, b3, b4, b5, b6, b7]
  dsimp [b0, b1, b2, b3, b4, b5, b6, b7] at hs1 hs2 hs3 hs4 hs5 hs6
  ring_nf at hs1 hs2 hs3 hs4 hs5 hs6 ⊢
  rw [hs1, hs2, hs3, hs4, hs5, hs6]

lemma linearCellCountDensity_ae_eq_indicator (k : ℕ) {h eps c : ℝ}
    (hh : 0 < h) (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 128)
    (hc : c ∈ Set.Icc (-1 : ℝ) 1) :
    linearCellCountDensity k h eps c =ᵐ[volume]
      (Set.Icc (1 / 4 + (k : ℝ) * h / 2)
        (1 / 4 + ((k : ℝ) + 1) * h / 2)).indicator (fun _ => 1) := by
  have hfinite : ∫⁻ y, (Set.Icc (1 / 4 + (k : ℝ) * h / 2)
      (1 / 4 + ((k : ℝ) + 1) * h / 2)).indicator
        (fun _ => (1 : ℝ≥0∞)) y ∂(volume : Measure ℝ) ≠ ∞ := by
    rw [lintegral_indicator measurableSet_Icc]
    simp
  symm
  apply (withDensity_eq_iff
    (measurable_const.indicator measurableSet_Icc).aemeasurable
    (measurable_linearCellCountDensity k h eps c).aemeasurable hfinite).1
  symm
  rw [show (volume : Measure ℝ).withDensity (linearCellCountDensity k h eps c) =
        ∑ i : Fin 7, volume.restrict (Set.Icc (linearCellLower k h eps c i)
          (linearCellUpper k h eps c i)) by
      ext s hs
      simp only [withDensity_apply _ hs, linearCellCountDensity]
      rw [Measure.finsetSum_apply, MeasureTheory.lintegral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [← withDensity_apply _ hs,
          MeasureTheory.withDensity_indicator measurableSet_Icc,
          MeasureTheory.withDensity_const]
        simp
      · exact fun i _ => measurable_const.indicator measurableSet_Icc]
  rw [linearCell_interval_partition k hh heps0 heps hc,
    MeasureTheory.withDensity_indicator measurableSet_Icc,
    MeasureTheory.withDensity_const]
  simp

lemma linearCellDensity_error_scaled (k : ℕ) {h eps c y : ℝ}
    (hh : 0 < h) (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 128)
    (hc : c ∈ Set.Icc (-1 : ℝ) 1) :
    |(ENNReal.ofReal h * linearCellDensity k h eps c y).toReal -
        2 * (linearCellCountDensity k h eps c y).toReal| ≤
      256 * eps * (linearCellCountDensity k h eps c y).toReal := by
  let S (i : Fin 7) := Set.Icc (linearCellLower k h eps c i)
    (linearCellUpper k h eps c i)
  let a (i : Fin 7) : ℝ := (S i).indicator (fun _ =>
    (ENNReal.ofReal h * linearCellWeight h eps c i).toReal) y
  let b (i : Fin 7) : ℝ := (S i).indicator (fun _ => 1) y
  have hreal : (ENNReal.ofReal h * linearCellDensity k h eps c y).toReal =
      ∑ i : Fin 7, a i := by
    unfold linearCellDensity
    rw [Finset.mul_sum, ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro i hi
      by_cases hy : y ∈ S i <;> simp [a, S, hy]
    · intro i hi
      by_cases hy : y ∈ S i
      · simp only [S, hy, Set.indicator_of_mem]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
      · simp [S, hy]
  have hcountReal : (linearCellCountDensity k h eps c y).toReal =
      ∑ i : Fin 7, b i := by
    unfold linearCellCountDensity
    rw [ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro i hi
      by_cases hy : y ∈ S i <;> simp [b, S, hy]
    · intro i hi
      by_cases hy : y ∈ S i <;> simp [S, hy]
  have hi (i : Fin 7) : |a i - 2 * b i| ≤ 256 * eps * b i := by
    by_cases hy : y ∈ S i
    · simpa [a, b, hy] using
        (linearCellWeight_physical_error hh heps0 heps hc i)
    · simp [a, b, hy]
  have hlo (i : Fin 7) : (2 - 256 * eps) * b i ≤ a i := by
    have := (abs_le.mp (hi i)).1
    linarith
  have hupp (i : Fin 7) : a i ≤ (2 + 256 * eps) * b i := by
    have := (abs_le.mp (hi i)).2
    linarith
  rw [hreal, hcountReal, abs_le]
  constructor
  · calc
      -(256 * eps * (∑ i : Fin 7, b i)) =
          (2 - 256 * eps) * (∑ i : Fin 7, b i) -
            2 * (∑ i : Fin 7, b i) := by ring
      _ = (∑ i : Fin 7, (2 - 256 * eps) * b i) -
            2 * (∑ i : Fin 7, b i) := by
        rw [Finset.mul_sum]
      _ ≤ (∑ i : Fin 7, a i) - 2 * (∑ i : Fin 7, b i) := by
        gcongr with i
        exact hlo i
  · calc
      (∑ i : Fin 7, a i) - 2 * (∑ i : Fin 7, b i) ≤
          (∑ i : Fin 7, (2 + 256 * eps) * b i) -
            2 * (∑ i : Fin 7, b i) := by
        gcongr with i
        exact hupp i
      _ = (2 + 256 * eps) * (∑ i : Fin 7, b i) -
            2 * (∑ i : Fin 7, b i) := by
        rw [← Finset.mul_sum]
      _ = 256 * eps * (∑ i : Fin 7, b i) := by ring

lemma linearCellDensity_error_of_count_eq_one (k : ℕ) {h eps c y : ℝ}
    (hh : 0 < h) (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 128)
    (hc : c ∈ Set.Icc (-1 : ℝ) 1)
    (hcount : linearCellCountDensity k h eps c y = 1) :
    |(ENNReal.ofReal h * linearCellDensity k h eps c y).toReal - 2| ≤
      256 * eps := by
  have h := linearCellDensity_error_scaled k hh heps0 heps hc (y := y)
  rw [hcount] at h
  norm_num at h ⊢
  exact h

-- keep: reusable almost-everywhere cell-density error bound for linear folds
lemma linearCellDensity_error_ae (k : ℕ) {h eps c : ℝ}
    (hh : 0 < h) (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 128)
    (hc : c ∈ Set.Icc (-1 : ℝ) 1) :
    ∀ᵐ y ∂(volume : Measure ℝ).restrict
        (Set.Icc (1 / 4 + (k : ℝ) * h / 2)
          (1 / 4 + ((k : ℝ) + 1) * h / 2)),
      |(ENNReal.ofReal h * linearCellDensity k h eps c y).toReal - 2| ≤
        256 * eps := by
  filter_upwards [ae_restrict_of_ae
      (linearCellCountDensity_ae_eq_indicator k hh heps0 heps hc),
    ae_restrict_mem measurableSet_Icc] with y hycount hy
  apply linearCellDensity_error_of_count_eq_one k hh heps0 heps hc
  norm_num at hycount hy ⊢
  rw [hycount]
  apply Set.indicator_of_mem
  norm_num
  exact hy

end CausalSmith.Experimentation.PilotscorePairingFrontier

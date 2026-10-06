module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedLinearBounds

/-! # Uniform density bounds over the full beta-one mesh -/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory
open scoped ENNReal BigOperators

lemma volume_restrict_shifted_mesh_partition (q : ℕ) (s : ℝ) {a : ℝ}
    (ha : 0 ≤ a) :
    (volume : Measure ℝ).restrict (Set.Icc s (s + (q : ℝ) * a)) =
      ∑ k ∈ Finset.range q,
        volume.restrict (Set.Icc (s + (k : ℝ) * a)
          (s + ((k : ℝ) + 1) * a)) := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hq : s ≤ s + (q : ℝ) * a := by
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ q by positivity) ha]
      have hstep : s + (q : ℝ) * a ≤ s + ((q : ℝ) + 1) * a := by
        gcongr
        norm_num
      rw [show s + ((q + 1 : ℕ) : ℝ) * a =
        s + ((q : ℝ) + 1) * a by norm_num]
      rw [volume_restrict_Icc_split hq hstep, ih, Finset.sum_range_succ]

@[no_expose]
noncomputable def linearMeshCountDensity (q : ℕ) (h eps : ℝ)
    (c : ℕ → ℝ) (y : ℝ) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range q, linearCellCountDensity k h eps (c k) y

@[fun_prop]
lemma measurable_linearMeshCountDensity (q : ℕ) (h eps : ℝ) (c : ℕ → ℝ) :
    Measurable (linearMeshCountDensity q h eps c) := by
  unfold linearMeshCountDensity
  fun_prop

lemma linearMeshCountDensity_ae_eq_indicator (q : ℕ) (hq : 0 < q)
    {h eps : ℝ} (hhq : h = (q : ℝ)⁻¹) (c : ℕ → ℝ)
    (hc : ∀ k, c k ∈ Set.Icc (-1 : ℝ) 1)
    (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 128) :
    linearMeshCountDensity q h eps c =ᵐ[volume]
      scoreInterval.indicator (fun _ => 1) := by
  have hh : 0 < h := by rw [hhq]; positivity
  have hfinite : ∫⁻ y, scoreInterval.indicator (fun _ => (1 : ℝ≥0∞)) y
      ∂(volume : Measure ℝ) ≠ ∞ := by
    unfold scoreInterval
    rw [lintegral_indicator measurableSet_Icc]
    simp
  symm
  apply (withDensity_eq_iff
    (measurable_const.indicator measurableSet_Icc).aemeasurable
    (measurable_linearMeshCountDensity q h eps c).aemeasurable hfinite).1
  symm
  rw [show (volume : Measure ℝ).withDensity (linearMeshCountDensity q h eps c) =
      ∑ k ∈ Finset.range q, volume.restrict
        (Set.Icc (1 / 4 + (k : ℝ) * h / 2)
          (1 / 4 + ((k : ℝ) + 1) * h / 2)) by
    ext s hs
    simp only [withDensity_apply _ hs, linearMeshCountDensity]
    rw [MeasureTheory.lintegral_finsetSum, Measure.finsetSum_apply]
    · apply Finset.sum_congr rfl
      intro k hk
      have hae := linearCellCountDensity_ae_eq_indicator k hh heps0 heps (hc k)
      rw [lintegral_congr_ae (hae.filter_mono (ae_mono Measure.restrict_le_self)),
        ← withDensity_apply _ hs, MeasureTheory.withDensity_indicator measurableSet_Icc,
        MeasureTheory.withDensity_const]
      simp
    · exact fun k _ => measurable_linearCellCountDensity k h eps (c k)]
  have hpart := volume_restrict_shifted_mesh_partition q (1 / 4 : ℝ)
    (show 0 ≤ h / 2 by positivity)
  have hqh : (q : ℝ) * (h / 2) = 1 / 2 := by
    rw [hhq]
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    field_simp [hqR.ne']
  rw [hqh] at hpart
  ring_nf at hpart ⊢
  rw [MeasureTheory.withDensity_indicator measurableSet_Icc,
    MeasureTheory.withDensity_const]
  simp only [one_smul]
  simpa [mul_comm, add_comm, add_left_comm, add_assoc] using hpart.symm

lemma linearMeshDensity_error_scaled (q : ℕ) {h eps y : ℝ} (c : ℕ → ℝ)
    (hh : 0 < h) (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 128)
    (hc : ∀ k, c k ∈ Set.Icc (-1 : ℝ) 1) :
    |(linearMeshDensity q h eps c y).toReal -
        2 * (linearMeshCountDensity q h eps c y).toReal| ≤
      256 * eps * (linearMeshCountDensity q h eps c y).toReal := by
  let p (k : ℕ) := (ENNReal.ofReal h * linearCellDensity k h eps (c k) y).toReal
  let z (k : ℕ) := (linearCellCountDensity k h eps (c k) y).toReal
  have hp : (linearMeshDensity q h eps c y).toReal =
      ∑ k ∈ Finset.range q, p k := by
    unfold linearMeshDensity
    rw [ENNReal.toReal_sum]
    intro k hk
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by
      unfold linearCellDensity
      exact ENNReal.sum_ne_top.mpr fun i hi => by
        by_cases hy : y ∈ Set.Icc (linearCellLower k h eps (c k) i)
            (linearCellUpper k h eps (c k) i) <;>
          simp [hy, linearCellWeight])
  have hz : (linearMeshCountDensity q h eps c y).toReal =
      ∑ k ∈ Finset.range q, z k := by
    unfold linearMeshCountDensity
    rw [ENNReal.toReal_sum]
    intro k hk
    unfold linearCellCountDensity
    exact ENNReal.sum_ne_top.mpr fun i hi => by
      by_cases hy : y ∈ Set.Icc (linearCellLower k h eps (c k) i)
          (linearCellUpper k h eps (c k) i) <;> simp [hy]
  have hk (k : ℕ) : |p k - 2 * z k| ≤ 256 * eps * z k :=
    linearCellDensity_error_scaled k hh heps0 heps (hc k)
  rw [hp, hz]
  rw [show (∑ k ∈ Finset.range q, p k) -
      2 * (∑ k ∈ Finset.range q, z k) =
      ∑ k ∈ Finset.range q, (p k - 2 * z k) by
    rw [Finset.mul_sum, Finset.sum_sub_distrib]]
  calc
    |∑ k ∈ Finset.range q, (p k - 2 * z k)| ≤
        ∑ k ∈ Finset.range q, |p k - 2 * z k| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range q, 256 * eps * z k := by
      gcongr with k hkmem
      exact hk k
    _ = 256 * eps * (∑ k ∈ Finset.range q, z k) := by
      rw [Finset.mul_sum]

lemma linearMeshDensity_error_ae (q : ℕ) (hq : 0 < q)
    {h eps : ℝ} (hhq : h = (q : ℝ)⁻¹) (c : ℕ → ℝ)
    (hc : ∀ k, c k ∈ Set.Icc (-1 : ℝ) 1)
    (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 128) :
    ∀ᵐ y ∂(volume : Measure ℝ).restrict scoreInterval,
      |(linearMeshDensity q h eps c y).toReal - 2| ≤ 256 * eps := by
  have hh : 0 < h := by rw [hhq]; positivity
  filter_upwards [ae_restrict_of_ae
      (linearMeshCountDensity_ae_eq_indicator q hq hhq c hc heps0 heps),
    ae_restrict_mem measurableSet_Icc] with y hycount hy
  have herr := linearMeshDensity_error_scaled q c hh heps0 heps hc (y := y)
  have hone : linearMeshCountDensity q h eps c y = 1 := by
    rw [hycount]
    simp [hy]
  rw [hone] at herr
  norm_num at herr ⊢
  exact herr

lemma linearCell_interval_inside_cell (k : ℕ) {h eps c : ℝ}
    (hh : 0 < h) (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 128)
    (hc : c ∈ Set.Icc (-1 : ℝ) 1) (i : Fin 7) :
    1 / 4 + (k : ℝ) * h / 2 ≤ linearCellLower k h eps c i ∧
      linearCellUpper k h eps c i ≤ 1 / 4 + ((k : ℝ) + 1) * h / 2 := by
  have hec_lo : -(1 / 128 : ℝ) ≤ eps * c := by
    nlinarith [mul_le_mul_of_nonneg_left hc.1 heps0]
  have hec_hi : eps * c ≤ 1 / 128 := by
    nlinarith [mul_le_mul_of_nonneg_left hc.2 heps0]
  fin_cases i <;> constructor <;>
    simp [linearCellLower, linearCellUpper, linearFoldedBranches] <;>
    nlinarith [mul_pos hh (show (0 : ℝ) < 1 / 128 by norm_num)]

lemma linearMeshDensity_eq_zero_off (q : ℕ) (hq : 0 < q)
    {h eps y : ℝ} (hhq : h = (q : ℝ)⁻¹) (c : ℕ → ℝ)
    (hc : ∀ k, c k ∈ Set.Icc (-1 : ℝ) 1)
    (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 128)
    (hy : y ∉ scoreInterval) :
    linearMeshDensity q h eps c y = 0 := by
  have hh : 0 < h := by rw [hhq]; positivity
  unfold linearMeshDensity linearCellDensity
  apply Finset.sum_eq_zero
  intro k hk
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro i hi
  apply Set.indicator_of_notMem
  intro hyi
  have hinside := linearCell_interval_inside_cell k hh heps0 heps (hc k) i
  have hkq : k < q := Finset.mem_range.mp hk
  have hk0 : 0 ≤ (k : ℝ) * h := mul_nonneg (by positivity) hh.le
  have hkend : ((k : ℝ) + 1) * h ≤ 1 := by
    rw [hhq]
    have hkR : (k : ℝ) + 1 ≤ q := by exact_mod_cast Nat.succ_le_of_lt hkq
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    calc
      ((k : ℝ) + 1) * (q : ℝ)⁻¹ ≤
          (q : ℝ) * (q : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right hkR (inv_nonneg.mpr hqR.le)
      _ = 1 := mul_inv_cancel₀ hqR.ne'
  apply hy
  unfold scoreInterval
  constructor
  · linarith [hyi.1, hinside.1]
  · linarith [hyi.2, hinside.2]

end CausalSmith.Experimentation.PilotscorePairingFrontier

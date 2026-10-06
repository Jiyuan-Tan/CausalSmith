module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedSmallMesh

/-! # Piecewise-affine pushforward for the beta-one branch -/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory
open scoped BigOperators Matrix ENNReal

noncomputable def linearFoldedCell (k : ℕ) (h eps c r : ℝ) : ℝ :=
  1 / 4 + ((k : ℝ) + r) * h / 2 + eps * h * c * foldedFirstBump r

lemma linearFoldedCell_def (k : ℕ) (h eps c r : ℝ) :
    linearFoldedCell k h eps c r =
      1 / 4 + ((k : ℝ) + r) * h / 2 + eps * h * c * foldedFirstBump r := rfl

@[fun_prop]
lemma measurable_linearFoldedCell (k : ℕ) (h eps c : ℝ) :
    Measurable (linearFoldedCell k h eps c) := by
  unfold linearFoldedCell foldedFirstBump
  fun_prop

noncomputable def linearFoldedBranches (h eps c : ℝ) : Fin 7 -> GridBranch := ![
  ⟨0, h / 8, h / 2, 1 / 4⟩,
  ⟨h / 8, 13 * h / 64, h / 2, 5 / 32⟩,
  ⟨13 * h / 64, 7 * h / 32 + eps * h * c,
    h / 2 + 32 * eps * h * c, 1 / 32⟩,
  ⟨7 * h / 32 + eps * h * c, 9 * h / 32 + eps * h * c,
    h / 2, 1 / 8⟩,
  ⟨9 * h / 32 + eps * h * c, 19 * h / 64,
    h / 2 - 32 * eps * h * c, 1 / 32⟩,
  ⟨19 * h / 64, 3 * h / 8, h / 2, 5 / 32⟩,
  ⟨3 * h / 8, h / 2, h / 2, 1 / 4⟩]

lemma linearFoldedBranches_slope_pos {h eps c : ℝ}
    (hh : 0 < h) (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 128)
    (hc : c ∈ Set.Icc (-1 : ℝ) 1) (i : Fin 7) :
    0 < (linearFoldedBranches h eps c i).slope := by
  have hec_lo : -(1 / 128 : ℝ) ≤ eps * c := by
    nlinarith [mul_le_mul_of_nonneg_left hc.1 heps0]
  have hec_hi : eps * c ≤ 1 / 128 := by
    nlinarith [mul_le_mul_of_nonneg_left hc.2 heps0]
  fin_cases i <;> simp [linearFoldedBranches] <;>
    nlinarith [mul_pos hh (show (0 : ℝ) < 1 / 4 by norm_num)]

noncomputable def linearDomainLower : Fin 7 -> ℝ :=
  ![0, 1 / 4, 13 / 32, 7 / 16, 9 / 16, 19 / 32, 3 / 4]

noncomputable def linearDomainUpper : Fin 7 -> ℝ :=
  ![1 / 4, 13 / 32, 7 / 16, 9 / 16, 19 / 32, 3 / 4, 1]

-- keep: reusable domain-order fact for the seven linear branches
lemma linearDomainLower_le_upper (i : Fin 7) :
    linearDomainLower i ≤ linearDomainUpper i := by
  fin_cases i <;> norm_num [linearDomainLower, linearDomainUpper]

lemma linearFoldedCell_affine (k : ℕ) {h eps c r : ℝ} (i : Fin 7)
    (hr : r ∈ Set.Icc (linearDomainLower i) (linearDomainUpper i)) :
    linearFoldedCell k h eps c r =
      1 / 4 + (k : ℝ) * h / 2 +
        (linearFoldedBranches h eps c i).lower +
        (linearFoldedBranches h eps c i).slope *
          (r - linearDomainLower i) := by
  fin_cases i <;> simp [linearDomainLower, linearDomainUpper,
    linearFoldedBranches, linearFoldedCell] at hr ⊢
  · rw [foldedFirstBump_eq_zero_of_le (hr.2.trans (by norm_num))]
    ring
  · rw [foldedFirstBump_eq_zero_of_le hr.2]
    ring
  · rw [foldedFirstBump_eq_ramp_up hr.1 hr.2]
    ring
  · rw [foldedFirstBump_eq_one hr.1 hr.2]
    ring
  · rw [foldedFirstBump_eq_ramp_down hr.1 hr.2]
    ring
  · rw [foldedFirstBump_eq_zero_of_ge hr.1]
    ring
  · rw [foldedFirstBump_eq_zero_of_ge
      ((by norm_num : (19 / 32 : ℝ) ≤ 3 / 4).trans hr.1)]
    ring

lemma map_linearFoldedCell_branch (k : ℕ) {h eps c : ℝ}
    (hh : 0 < h) (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 128)
    (hc : c ∈ Set.Icc (-1 : ℝ) 1) (i : Fin 7) :
    Measure.map (linearFoldedCell k h eps c)
        (volume.restrict (Set.Icc (linearDomainLower i) (linearDomainUpper i))) =
      ENNReal.ofReal ((linearFoldedBranches h eps c i).slope)⁻¹ •
        volume.restrict (Set.Icc
          (1 / 4 + (k : ℝ) * h / 2 +
            (linearFoldedBranches h eps c i).lower)
          (1 / 4 + (k : ℝ) * h / 2 +
            (linearFoldedBranches h eps c i).upper)) := by
  have hs := linearFoldedBranches_slope_pos hh heps0 heps hc i
  calc
    Measure.map (linearFoldedCell k h eps c)
        (volume.restrict (Set.Icc (linearDomainLower i) (linearDomainUpper i))) =
      Measure.map (fun r : ℝ =>
        1 / 4 + (k : ℝ) * h / 2 +
          (linearFoldedBranches h eps c i).lower +
          (linearFoldedBranches h eps c i).slope *
            (r - linearDomainLower i))
        (volume.restrict (Set.Icc (linearDomainLower i) (linearDomainUpper i))) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact linearFoldedCell_affine k i hr
    _ = _ := by
      let b := linearFoldedBranches h eps c i
      let l := linearDomainLower i
      let u := linearDomainUpper i
      let a := 1 / 4 + (k : ℝ) * h / 2 + b.lower - b.slope * l
      have hfun : (fun r : ℝ =>
          1 / 4 + (k : ℝ) * h / 2 + b.lower + b.slope * (r - l)) =
          (fun r : ℝ => a + b.slope * r) := by
        funext r
        dsimp [a]
        ring
      rw [hfun, map_affine_restrict_Icc_of_pos a b.slope l u hs]
      congr 3
      · dsimp [a, b, l]
        ring
      · have hlen : b.upper - b.lower = b.slope * (u - l) := by
          dsimp [b, u, l]
          fin_cases i <;> simp [linearFoldedBranches, linearDomainLower,
            linearDomainUpper] <;> ring
        dsimp [a]
        linarith

noncomputable def linearCellWeight (h eps c : ℝ) (i : Fin 7) : ℝ≥0∞ :=
  ENNReal.ofReal ((linearFoldedBranches h eps c i).slope)⁻¹

noncomputable def linearCellLower (k : ℕ) (h eps c : ℝ) (i : Fin 7) : ℝ :=
  1 / 4 + (k : ℝ) * h / 2 + (linearFoldedBranches h eps c i).lower

noncomputable def linearCellUpper (k : ℕ) (h eps c : ℝ) (i : Fin 7) : ℝ :=
  1 / 4 + (k : ℝ) * h / 2 + (linearFoldedBranches h eps c i).upper

/-- Exact seven-piece density representation on one rescaled mesh cell. -/
lemma map_linearFoldedCell_eq_intervalMixture (k : ℕ) {h eps c : ℝ}
    (hh : 0 < h) (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 128)
    (hc : c ∈ Set.Icc (-1 : ℝ) 1) :
    Measure.map (linearFoldedCell k h eps c)
        (volume.restrict (Set.Icc (0 : ℝ) 1)) =
      intervalMixture (linearCellWeight h eps c)
        (linearCellLower k h eps c) (linearCellUpper k h eps c) := by
  rw [map_volume_unit_seven_partition _
    (measurable_linearFoldedCell k h eps c)]
  have hm0 := map_linearFoldedCell_branch k hh heps0 heps hc (0 : Fin 7)
  have hm1 := map_linearFoldedCell_branch k hh heps0 heps hc (1 : Fin 7)
  have hm2 := map_linearFoldedCell_branch k hh heps0 heps hc (2 : Fin 7)
  have hm3 := map_linearFoldedCell_branch k hh heps0 heps hc (3 : Fin 7)
  have hm4 := map_linearFoldedCell_branch k hh heps0 heps hc (4 : Fin 7)
  have hm5 := map_linearFoldedCell_branch k hh heps0 heps hc (5 : Fin 7)
  have hm6 := map_linearFoldedCell_branch k hh heps0 heps hc (6 : Fin 7)
  simp [linearDomainLower, linearDomainUpper] at hm0 hm1 hm2 hm3 hm4 hm5 hm6
  norm_num at hm0 hm1 hm2 hm3 hm4 hm5 hm6
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, intervalMixture_def]
  simp [Fin.sum_univ_succ, linearCellWeight, linearCellLower, linearCellUpper]
  norm_num
  abel

lemma map_linearFoldedCell_rescaled (k : ℕ) {h eps c : ℝ} (hh : 0 < h) :
    Measure.map (fun x : ℝ => linearFoldedCell k h eps c (x / h - k))
        (volume.restrict (Set.Icc ((k : ℝ) * h) (((k : ℝ) + 1) * h))) =
      ENNReal.ofReal h •
        Measure.map (linearFoldedCell k h eps c)
          (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  simpa using map_rescaled_mesh_interval k (l := 0) (u := 1) hh
    (linearFoldedCell k h eps c) (measurable_linearFoldedCell k h eps c)

/-- Assemble the beta-one affine cells over a reciprocal mesh. -/
lemma map_eq_sum_linearFoldedCells (q : ℕ) (hq : 0 < q) {h eps : ℝ}
    (hhq : h = (q : ℝ)⁻¹) (c : ℕ → ℝ) {F : ℝ → ℝ} (hF : Measurable F)
    (hcell : ∀ k < q, ∀ x ∈ Set.Icc ((k : ℝ) * h) (((k : ℝ) + 1) * h),
      F x = linearFoldedCell k h eps (c k) (x / h - k)) :
    Measure.map F ((volume : Measure ℝ).restrict (Set.Icc 0 1)) =
      ∑ k ∈ Finset.range q, ENNReal.ofReal h •
        Measure.map (linearFoldedCell k h eps (c k))
          (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  rw [map_volume_reciprocal_mesh_partition q hq F hF]
  apply Finset.sum_congr rfl
  intro k hk
  have hkq : k < q := Finset.mem_range.mp hk
  rw [← hhq]
  calc
    Measure.map F
        (volume.restrict (Set.Icc ((k : ℝ) * h) (((k : ℝ) + 1) * h))) =
      Measure.map (fun x : ℝ => linearFoldedCell k h eps (c k) (x / h - k))
        (volume.restrict (Set.Icc ((k : ℝ) * h) (((k : ℝ) + 1) * h))) := by
          apply Measure.map_congr
          filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
          exact hcell k hkq x hx
    _ = _ := map_linearFoldedCell_rescaled k (by rw [hhq]; positivity)

end CausalSmith.Experimentation.PilotscorePairingFrontier

module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedIntervalPartition
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedSignedPushforward

/-! # Exact seven-branch pushforward of one folded mesh cell -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory
lemma map_perturbed_unit_cell_signed (k : ℕ) {h a ε c : ℝ}
    (hh : 0 < h) (ha : 0 ≤ a) (hscale : 4 ≤ a / h)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 64) (hc : c ∈ Set.Icc (-1 : ℝ) 1) :
    Measure.map (perturbedTriangularCell k h a ε c)
        (volume.restrict (Set.Icc (0 : ℝ) 1)) =
      ENNReal.ofReal (h + 4 * a)⁻¹ •
        volume.restrict (Set.Icc ((k : ℝ) * h) ((k : ℝ) * h + h / 4 + a)) +
      ENNReal.ofReal (4 * a - h)⁻¹ •
        volume.restrict (Set.Icc
          ((k : ℝ) * h + 13 * h / 32 + 3 * a / 8)
          ((k : ℝ) * h + h / 4 + a)) +
      ENNReal.ofReal (4 * a - h - 32 * ε * a * c)⁻¹ •
        volume.restrict (Set.Icc
          ((k : ℝ) * h + 7 * h / 16 + a / 4 + ε * a * c)
          ((k : ℝ) * h + 13 * h / 32 + 3 * a / 8)) +
      ENNReal.ofReal (4 * a - h)⁻¹ •
        volume.restrict (Set.Icc
          ((k : ℝ) * h + 9 * h / 16 - a / 4 + ε * a * c)
          ((k : ℝ) * h + 7 * h / 16 + a / 4 + ε * a * c)) +
      ENNReal.ofReal (4 * a - h + 32 * ε * a * c)⁻¹ •
        volume.restrict (Set.Icc
          ((k : ℝ) * h + 19 * h / 32 - 3 * a / 8)
          ((k : ℝ) * h + 9 * h / 16 - a / 4 + ε * a * c)) +
      ENNReal.ofReal (4 * a - h)⁻¹ •
        volume.restrict (Set.Icc
          ((k : ℝ) * h + 3 * h / 4 - a)
          ((k : ℝ) * h + 19 * h / 32 - 3 * a / 8)) +
      ENNReal.ofReal (h + 4 * a)⁻¹ •
        volume.restrict (Set.Icc
          ((k : ℝ) * h + 3 * h / 4 - a) (((k : ℝ) + 1) * h)) := by
  rw [map_volume_unit_seven_partition _
    (measurable_perturbedTriangularCell k h a ε c)]
  rw [map_perturbed_first k hh ha,
    map_perturbed_middle_left k hh hscale,
    map_perturbed_ramp_up_signed k hh hscale hε0 hε hc,
    map_perturbed_plateau k hh hscale,
    map_perturbed_ramp_down_signed k hh hscale hε0 hε hc,
    map_perturbed_middle_right k hh hscale,
    map_perturbed_last k hh ha]

lemma map_perturbed_mesh_cell_rescaled (k : ℕ) {h a ε c : ℝ} (hh : 0 < h) :
    Measure.map
        (fun x : ℝ => perturbedTriangularCell k h a ε c (x / h - k))
        (volume.restrict
          (Set.Icc ((k : ℝ) * h) (((k : ℝ) + 1) * h))) =
      ENNReal.ofReal h •
        Measure.map (perturbedTriangularCell k h a ε c)
          (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  simpa using map_rescaled_mesh_interval k (l := 0) (u := 1) hh
    (perturbedTriangularCell k h a ε c)
    (measurable_perturbedTriangularCell k h a ε c)

/-- Assemble arbitrary signed/transverse coefficients cell by cell.  The
coefficient function `c` has no periodicity or regularity requirement. -/
lemma map_eq_sum_perturbed_cells (q : ℕ) (hq : 0 < q) {h a ε : ℝ}
    (hhq : h = (q : ℝ)⁻¹) (c : ℕ → ℝ) {F : ℝ → ℝ} (hF : Measurable F)
    (hcell : ∀ k < q, ∀ x ∈ Set.Icc ((k : ℝ) * h) (((k : ℝ) + 1) * h),
      F x = perturbedTriangularCell k h a ε (c k) (x / h - k)) :
    Measure.map F ((volume : Measure ℝ).restrict (Set.Icc 0 1)) =
      ∑ k ∈ Finset.range q,
        ENNReal.ofReal h •
          Measure.map (perturbedTriangularCell k h a ε (c k))
            (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  rw [map_volume_reciprocal_mesh_partition q hq F hF]
  apply Finset.sum_congr rfl
  intro k hk
  have hkq : k < q := Finset.mem_range.mp hk
  rw [← hhq]
  calc
    Measure.map F
        (volume.restrict (Set.Icc ((k : ℝ) * h) (((k : ℝ) + 1) * h))) =
      Measure.map
        (fun x : ℝ => perturbedTriangularCell k h a ε (c k) (x / h - k))
        (volume.restrict (Set.Icc ((k : ℝ) * h) (((k : ℝ) + 1) * h))) := by
          apply Measure.map_congr
          filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
          exact hcell k hkq x hx
    _ = _ := map_perturbed_mesh_cell_rescaled k (by rw [hhq]; positivity)

end CausalSmith.Experimentation.PilotscorePairingFrontier

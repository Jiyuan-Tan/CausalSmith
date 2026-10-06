module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedPushforward

/-! # Affine pushforwards for the perturbed folded branch -/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory

@[no_expose]
noncomputable def perturbedTriangularCell
    (k : ℕ) (h a ε c r : ℝ) : ℝ :=
  ((k : ℝ) + r) * h + a * triangularWave ((k : ℝ) + r) +
    ε * a * c * foldedFirstBump r

lemma perturbedTriangularCell_def (k : ℕ) (h a ε c r : ℝ) :
    perturbedTriangularCell k h a ε c r =
      ((k : ℝ) + r) * h + a * triangularWave ((k : ℝ) + r) +
        ε * a * c * foldedFirstBump r := by
  unfold perturbedTriangularCell
  rfl

@[fun_prop]
lemma measurable_perturbedTriangularCell (k : ℕ) (h a ε c : ℝ) :
    Measurable (perturbedTriangularCell k h a ε c) := by
  unfold perturbedTriangularCell foldedFirstBump
  fun_prop

lemma perturbedTriangularCell_eq_of_bump_zero (k : ℕ) (h a ε c r : ℝ)
    (hr : foldedFirstBump r = 0) :
    perturbedTriangularCell k h a ε c r =
      ((k : ℝ) + r) * h + a * triangularWave ((k : ℝ) + r) := by
  simp [perturbedTriangularCell, hr]

lemma perturbedTriangularCell_ramp_up (k : ℕ) (h a ε c r : ℝ)
    (hr0 : 13 / 32 ≤ r) (hr1 : r ≤ 7 / 16) :
    perturbedTriangularCell k h a ε c r =
      (k : ℝ) * h + 2 * a - 13 * ε * a * c +
        (h - 4 * a + 32 * ε * a * c) * r := by
  rw [perturbedTriangularCell, triangular_inner_middle k h a r (by linarith) (by linarith),
    foldedFirstBump_eq_ramp_up hr0 hr1]
  ring

lemma perturbedTriangularCell_plateau (k : ℕ) (h a ε c r : ℝ)
    (hr0 : 7 / 16 ≤ r) (hr1 : r ≤ 9 / 16) :
    perturbedTriangularCell k h a ε c r =
      (k : ℝ) * h + 2 * a + ε * a * c + (h - 4 * a) * r := by
  rw [perturbedTriangularCell, triangular_inner_middle k h a r (by linarith) (by linarith),
    foldedFirstBump_eq_one hr0 hr1]
  ring

lemma perturbedTriangularCell_ramp_down (k : ℕ) (h a ε c r : ℝ)
    (hr0 : 9 / 16 ≤ r) (hr1 : r ≤ 19 / 32) :
    perturbedTriangularCell k h a ε c r =
      (k : ℝ) * h + 2 * a + 19 * ε * a * c -
        (4 * a - h + 32 * ε * a * c) * r := by
  rw [perturbedTriangularCell, triangular_inner_middle k h a r (by linarith) (by linarith),
    foldedFirstBump_eq_ramp_down hr0 hr1]
  ring

lemma perturbed_ramp_up_slope_neg {h a ε c : ℝ}
    (hh : 0 < h) (hscale : 4 ≤ a / h)
    (hε : ε ≤ 1 / 64) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    h - 4 * a + 32 * ε * a * c < 0 := by
  have ha4 : 4 * h ≤ a := (le_div_iff₀ hh).mp hscale
  have ha0 : 0 ≤ a := le_trans (by positivity : 0 ≤ 4 * h) ha4
  have hεc : ε * c ≤ (1 / 64 : ℝ) := by
    calc
      ε * c ≤ (1 / 64) * 1 := mul_le_mul hε hc.2 hc.1 (by norm_num)
      _ = 1 / 64 := by ring
  have hpert : 32 * ε * a * c ≤ a / 2 := by
    calc
      32 * ε * a * c = 32 * (ε * c) * a := by ring
      _ ≤ 32 * (1 / 64) * a := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hεc (by norm_num)) ha0
      _ = a / 2 := by ring
  nlinarith

lemma perturbed_ramp_down_slope_neg {h a ε c : ℝ}
    (hh : 0 < h) (hscale : 4 ≤ a / h)
    (hε0 : 0 ≤ ε) (hc0 : 0 ≤ c) :
    h - 4 * a - 32 * ε * a * c < 0 := by
  have ha4 : 4 * h ≤ a := (le_div_iff₀ hh).mp hscale
  have ha0 : 0 ≤ a := le_trans (by positivity : 0 ≤ 4 * h) ha4
  have hprod : 0 ≤ 32 * ε * a * c := by positivity
  nlinarith

-- keep: reusable ramp-up pushforward formula for perturbed folded branches
lemma map_perturbed_ramp_up (k : ℕ) {h a ε c : ℝ}
    (hh : 0 < h) (hscale : 4 ≤ a / h)
    (hε : ε ≤ 1 / 64) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    Measure.map (perturbedTriangularCell k h a ε c)
        (volume.restrict (Set.Icc (13 / 32 : ℝ) (7 / 16))) =
      ENNReal.ofReal (4 * a - h - 32 * ε * a * c)⁻¹ •
        volume.restrict (Set.Icc
          ((k : ℝ) * h + 7 * h / 16 + a / 4 + ε * a * c)
          ((k : ℝ) * h + 13 * h / 32 + 3 * a / 8)) := by
  have hs : h - 4 * a + 32 * ε * a * c < 0 :=
    perturbed_ramp_up_slope_neg hh hscale hε hc
  calc
    Measure.map (perturbedTriangularCell k h a ε c)
        (volume.restrict (Set.Icc (13 / 32 : ℝ) (7 / 16))) =
      Measure.map
        (fun r : ℝ => (k : ℝ) * h + 2 * a - 13 * ε * a * c +
          (h - 4 * a + 32 * ε * a * c) * r)
        (volume.restrict (Set.Icc (13 / 32 : ℝ) (7 / 16))) := by
          apply Measure.map_congr
          filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
          exact perturbedTriangularCell_ramp_up k h a ε c r hr.1 hr.2
    _ = _ := by
      convert map_affine_restrict_Icc_of_neg
        ((k : ℝ) * h + 2 * a - 13 * ε * a * c)
        (h - 4 * a + 32 * ε * a * c) (13 / 32) (7 / 16)
        hs (by norm_num) using 1
      all_goals ring_nf

lemma map_perturbed_plateau (k : ℕ) {h a ε c : ℝ}
    (hh : 0 < h) (hscale : 4 ≤ a / h) :
    Measure.map (perturbedTriangularCell k h a ε c)
        (volume.restrict (Set.Icc (7 / 16 : ℝ) (9 / 16))) =
      ENNReal.ofReal (4 * a - h)⁻¹ •
        volume.restrict (Set.Icc
          ((k : ℝ) * h + 9 * h / 16 - a / 4 + ε * a * c)
          ((k : ℝ) * h + 7 * h / 16 + a / 4 + ε * a * c)) := by
  have hs : h - 4 * a < 0 := triangular_middle_slope_negative hh hscale
  calc
    Measure.map (perturbedTriangularCell k h a ε c)
        (volume.restrict (Set.Icc (7 / 16 : ℝ) (9 / 16))) =
      Measure.map
        (fun r : ℝ => (k : ℝ) * h + 2 * a + ε * a * c + (h - 4 * a) * r)
        (volume.restrict (Set.Icc (7 / 16 : ℝ) (9 / 16))) := by
          apply Measure.map_congr
          filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
          exact perturbedTriangularCell_plateau k h a ε c r hr.1 hr.2
    _ = _ := by
      convert map_affine_restrict_Icc_of_neg
        ((k : ℝ) * h + 2 * a + ε * a * c) (h - 4 * a)
        (7 / 16) (9 / 16) hs (by norm_num) using 1
      all_goals ring_nf

-- keep: reusable ramp-down pushforward formula for perturbed folded branches
lemma map_perturbed_ramp_down (k : ℕ) {h a ε c : ℝ}
    (hh : 0 < h) (hscale : 4 ≤ a / h)
    (hε0 : 0 ≤ ε) (hc0 : 0 ≤ c) :
    Measure.map (perturbedTriangularCell k h a ε c)
        (volume.restrict (Set.Icc (9 / 16 : ℝ) (19 / 32))) =
      ENNReal.ofReal (4 * a - h + 32 * ε * a * c)⁻¹ •
        volume.restrict (Set.Icc
          ((k : ℝ) * h + 19 * h / 32 - 3 * a / 8)
          ((k : ℝ) * h + 9 * h / 16 - a / 4 + ε * a * c)) := by
  have hs : h - 4 * a - 32 * ε * a * c < 0 :=
    perturbed_ramp_down_slope_neg hh hscale hε0 hc0
  calc
    Measure.map (perturbedTriangularCell k h a ε c)
        (volume.restrict (Set.Icc (9 / 16 : ℝ) (19 / 32))) =
      Measure.map
        (fun r : ℝ => (k : ℝ) * h + 2 * a + 19 * ε * a * c -
          (4 * a - h + 32 * ε * a * c) * r)
        (volume.restrict (Set.Icc (9 / 16 : ℝ) (19 / 32))) := by
          apply Measure.map_congr
          filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
          exact perturbedTriangularCell_ramp_down k h a ε c r hr.1 hr.2
    _ = _ := by
      convert map_affine_restrict_Icc_of_neg
        ((k : ℝ) * h + 2 * a + 19 * ε * a * c)
        (h - 4 * a - 32 * ε * a * c) (9 / 16) (19 / 32)
        hs (by norm_num) using 1
      all_goals ring_nf

lemma map_perturbed_first (k : ℕ) {h a ε c : ℝ}
    (hh : 0 < h) (ha : 0 ≤ a) :
    Measure.map (perturbedTriangularCell k h a ε c)
        (volume.restrict (Set.Icc (0 : ℝ) (1 / 4))) =
      ENNReal.ofReal (h + 4 * a)⁻¹ •
        volume.restrict (Set.Icc ((k : ℝ) * h)
          ((k : ℝ) * h + h / 4 + a)) := by
  calc
    Measure.map (perturbedTriangularCell k h a ε c)
        (volume.restrict (Set.Icc (0 : ℝ) (1 / 4))) =
      Measure.map
        (fun r : ℝ => ((k : ℝ) + r) * h +
          a * triangularWave ((k : ℝ) + r))
        (volume.restrict (Set.Icc (0 : ℝ) (1 / 4))) := by
          apply Measure.map_congr
          filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
          apply perturbedTriangularCell_eq_of_bump_zero
          exact foldedFirstBump_eq_zero_of_le (hr.2.trans (by norm_num))
    _ = _ := map_triangular_inner_first k hh ha

lemma map_perturbed_middle_left (k : ℕ) {h a ε c : ℝ}
    (hh : 0 < h) (hscale : 4 ≤ a / h) :
    Measure.map (perturbedTriangularCell k h a ε c)
        (volume.restrict (Set.Icc (1 / 4 : ℝ) (13 / 32))) =
      ENNReal.ofReal (4 * a - h)⁻¹ •
        volume.restrict (Set.Icc
          ((k : ℝ) * h + 13 * h / 32 + 3 * a / 8)
          ((k : ℝ) * h + h / 4 + a)) := by
  have hs := triangular_middle_slope_negative hh hscale
  calc
    Measure.map (perturbedTriangularCell k h a ε c)
        (volume.restrict (Set.Icc (1 / 4 : ℝ) (13 / 32))) =
      Measure.map
        (fun r : ℝ => (k : ℝ) * h + 2 * a + (h - 4 * a) * r)
        (volume.restrict (Set.Icc (1 / 4 : ℝ) (13 / 32))) := by
          apply Measure.map_congr
          filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
          rw [perturbedTriangularCell_eq_of_bump_zero k h a ε c r
            (foldedFirstBump_eq_zero_of_le hr.2),
            triangular_inner_middle k h a r hr.1 (by linarith [hr.2])]
    _ = _ := by
      convert map_affine_restrict_Icc_of_neg
        ((k : ℝ) * h + 2 * a) (h - 4 * a) (1 / 4) (13 / 32)
        hs (by norm_num) using 1
      all_goals ring_nf

lemma map_perturbed_middle_right (k : ℕ) {h a ε c : ℝ}
    (hh : 0 < h) (hscale : 4 ≤ a / h) :
    Measure.map (perturbedTriangularCell k h a ε c)
        (volume.restrict (Set.Icc (19 / 32 : ℝ) (3 / 4))) =
      ENNReal.ofReal (4 * a - h)⁻¹ •
        volume.restrict (Set.Icc
          ((k : ℝ) * h + 3 * h / 4 - a)
          ((k : ℝ) * h + 19 * h / 32 - 3 * a / 8)) := by
  have hs := triangular_middle_slope_negative hh hscale
  calc
    Measure.map (perturbedTriangularCell k h a ε c)
        (volume.restrict (Set.Icc (19 / 32 : ℝ) (3 / 4))) =
      Measure.map
        (fun r : ℝ => (k : ℝ) * h + 2 * a + (h - 4 * a) * r)
        (volume.restrict (Set.Icc (19 / 32 : ℝ) (3 / 4))) := by
          apply Measure.map_congr
          filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
          rw [perturbedTriangularCell_eq_of_bump_zero k h a ε c r
            (foldedFirstBump_eq_zero_of_ge hr.1),
            triangular_inner_middle k h a r (by linarith [hr.1]) hr.2]
    _ = _ := by
      convert map_affine_restrict_Icc_of_neg
        ((k : ℝ) * h + 2 * a) (h - 4 * a) (19 / 32) (3 / 4)
        hs (by norm_num) using 1
      all_goals ring_nf

lemma map_perturbed_last (k : ℕ) {h a ε c : ℝ}
    (hh : 0 < h) (ha : 0 ≤ a) :
    Measure.map (perturbedTriangularCell k h a ε c)
        (volume.restrict (Set.Icc (3 / 4 : ℝ) 1)) =
      ENNReal.ofReal (h + 4 * a)⁻¹ •
        volume.restrict (Set.Icc
          ((k : ℝ) * h + 3 * h / 4 - a) (((k : ℝ) + 1) * h)) := by
  calc
    Measure.map (perturbedTriangularCell k h a ε c)
        (volume.restrict (Set.Icc (3 / 4 : ℝ) 1)) =
      Measure.map
        (fun r : ℝ => ((k : ℝ) + r) * h +
          a * triangularWave ((k : ℝ) + r))
        (volume.restrict (Set.Icc (3 / 4 : ℝ) 1)) := by
          apply Measure.map_congr
          filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
          apply perturbedTriangularCell_eq_of_bump_zero
          exact foldedFirstBump_eq_zero_of_ge
            ((by norm_num : (19 / 32 : ℝ) ≤ 3 / 4).trans hr.1)
    _ = _ := map_triangular_inner_last k hh ha

end CausalSmith.Experimentation.PilotscorePairingFrontier

module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedPerturbedPushforward

/-! # Affine pushforwards uniform over either hypercube sign -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory

lemma perturbed_ramp_up_slope_neg_signed {h a ε c : ℝ}
    (hh : 0 < h) (hscale : 4 ≤ a / h)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 64) (hc : c ∈ Set.Icc (-1 : ℝ) 1) :
    h - 4 * a + 32 * ε * a * c < 0 := by
  have ha4 : 4 * h ≤ a := (le_div_iff₀ hh).mp hscale
  have ha0 : 0 ≤ a := le_trans (by positivity : 0 ≤ 4 * h) ha4
  have hεc : ε * c ≤ (1 / 64 : ℝ) := by
    have : ε * c ≤ ε := mul_le_of_le_one_right hε0 hc.2
    linarith
  have hpert : 32 * ε * a * c ≤ a / 2 := by
    calc
      32 * ε * a * c = 32 * (ε * c) * a := by ring
      _ ≤ 32 * (1 / 64) * a := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hεc (by norm_num)) ha0
      _ = a / 2 := by ring
  nlinarith

lemma perturbed_ramp_down_slope_neg_signed {h a ε c : ℝ}
    (hh : 0 < h) (hscale : 4 ≤ a / h)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 64) (hc : c ∈ Set.Icc (-1 : ℝ) 1) :
    h - 4 * a - 32 * ε * a * c < 0 := by
  have ha4 : 4 * h ≤ a := (le_div_iff₀ hh).mp hscale
  have ha0 : 0 ≤ a := le_trans (by positivity : 0 ≤ 4 * h) ha4
  have hεc : -(ε * c) ≤ (1 / 64 : ℝ) := by
    have hnegc : -c ≤ 1 := by linarith [hc.1]
    have : ε * (-c) ≤ ε := mul_le_of_le_one_right hε0 hnegc
    linarith
  have hpert : -(32 * ε * a * c) ≤ a / 2 := by
    calc
      -(32 * ε * a * c) = 32 * (-(ε * c)) * a := by ring
      _ ≤ 32 * (1 / 64) * a := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hεc (by norm_num)) ha0
      _ = a / 2 := by ring
  nlinarith

lemma map_perturbed_ramp_up_signed (k : ℕ) {h a ε c : ℝ}
    (hh : 0 < h) (hscale : 4 ≤ a / h)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 64) (hc : c ∈ Set.Icc (-1 : ℝ) 1) :
    Measure.map (perturbedTriangularCell k h a ε c)
        (volume.restrict (Set.Icc (13 / 32 : ℝ) (7 / 16))) =
      ENNReal.ofReal (4 * a - h - 32 * ε * a * c)⁻¹ •
        volume.restrict (Set.Icc
          ((k : ℝ) * h + 7 * h / 16 + a / 4 + ε * a * c)
          ((k : ℝ) * h + 13 * h / 32 + 3 * a / 8)) := by
  have hs := perturbed_ramp_up_slope_neg_signed hh hscale hε0 hε hc
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

lemma map_perturbed_ramp_down_signed (k : ℕ) {h a ε c : ℝ}
    (hh : 0 < h) (hscale : 4 ≤ a / h)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 64) (hc : c ∈ Set.Icc (-1 : ℝ) 1) :
    Measure.map (perturbedTriangularCell k h a ε c)
        (volume.restrict (Set.Icc (9 / 16 : ℝ) (19 / 32))) =
      ENNReal.ofReal (4 * a - h + 32 * ε * a * c)⁻¹ •
        volume.restrict (Set.Icc
          ((k : ℝ) * h + 19 * h / 32 - 3 * a / 8)
          ((k : ℝ) * h + 9 * h / 16 - a / 4 + ε * a * c)) := by
  have hs := perturbed_ramp_down_slope_neg_signed hh hscale hε0 hε hc
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

end CausalSmith.Experimentation.PilotscorePairingFrontier

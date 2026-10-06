module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedBranches
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Pushforward calculations for the affine folded branches -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory

lemma map_affine_volume (c s : ℝ) (hs : s ≠ 0) :
    Measure.map (fun x : ℝ => c + s * x) volume =
      ENNReal.ofReal |s⁻¹| • volume := by
  have hcomp : (fun x : ℝ => c + s * x) = (fun y : ℝ => c + y) ∘ (fun x : ℝ => s * x) := rfl
  rw [hcomp, ← Measure.map_map (measurable_const_add c) (measurable_const_mul s)]
  rw [Real.map_volume_mul_left hs, Measure.map_smul, map_add_left_eq_self]

lemma map_affine_restrict (c s : ℝ) (hs : s ≠ 0)
    (S : Set ℝ) (hS : MeasurableSet S) :
    Measure.map (fun x : ℝ => c + s * x) (volume.restrict S) =
      ENNReal.ofReal |s⁻¹| • volume.restrict ((fun x : ℝ => c + s * x) '' S) := by
  let f : ℝ → ℝ := fun x => c + s * x
  have hf : Measurable f := measurable_const.add (measurable_const.mul measurable_id)
  have hfinj : Function.Injective f := by
    intro x y hxy
    dsimp [f] at hxy
    exact (mul_left_cancel₀ hs (add_left_cancel hxy))
  let e : ℝ ≃ₜ ℝ := (Homeomorph.mulLeft₀ s hs).trans (Homeomorph.addLeft c)
  have heq : (e : ℝ → ℝ) = f := rfl
  have himage : MeasurableSet (f '' S) := by
    rw [← heq]
    exact e.toMeasurableEquiv.measurableSet_image.mpr hS
  have hrestrict := Measure.restrict_map (μ := volume) hf himage
  rw [Set.preimage_image_eq S hfinj] at hrestrict
  calc
    Measure.map f (volume.restrict S) =
        (Measure.map f volume).restrict (f '' S) := hrestrict.symm
    _ = (ENNReal.ofReal |s⁻¹| • volume).restrict (f '' S) := by
      rw [show Measure.map f volume = ENNReal.ofReal |s⁻¹| • volume by
        simpa [f] using map_affine_volume c s hs]
    _ = ENNReal.ofReal |s⁻¹| • volume.restrict (f '' S) := by
      rw [Measure.restrict_smul]

lemma map_affine_restrict_Icc_of_pos (c s l u : ℝ) (hs : 0 < s) :
    Measure.map (fun x : ℝ => c + s * x) (volume.restrict (Set.Icc l u)) =
      ENNReal.ofReal s⁻¹ •
        volume.restrict (Set.Icc (c + s * l) (c + s * u)) := by
  rw [map_affine_restrict c s hs.ne' (Set.Icc l u) measurableSet_Icc]
  have hmono : StrictMono (fun x : ℝ => c + s * x) := by
    intro x y hxy
    simpa [add_comm] using add_lt_add_left (mul_lt_mul_of_pos_left hxy hs) c
  have hcont : Continuous (fun x : ℝ => c + s * x) :=
    continuous_const.add (continuous_const.mul continuous_id)
  rw [hcont.image_Icc_of_strictMono hmono]
  rw [abs_of_pos (inv_pos.mpr hs)]

lemma map_affine_restrict_Icc_of_neg (c s l u : ℝ) (hs : s < 0) (hlu : l ≤ u) :
    Measure.map (fun x : ℝ => c + s * x) (volume.restrict (Set.Icc l u)) =
      ENNReal.ofReal (-s)⁻¹ •
        volume.restrict (Set.Icc (c + s * u) (c + s * l)) := by
  rw [map_affine_restrict c s hs.ne (Set.Icc l u) measurableSet_Icc]
  have hanti : Antitone (fun x : ℝ => c + s * x) := by
    intro x y hxy
    simpa [add_comm] using add_le_add_left (mul_le_mul_of_nonpos_left hxy hs.le) c
  have hcont : Continuous (fun x : ℝ => c + s * x) :=
    continuous_const.add (continuous_const.mul continuous_id)
  rw [hcont.continuousOn.image_Icc_of_antitoneOn hlu (hanti.antitoneOn _)]
  have habs : |s⁻¹| = (-s)⁻¹ := by
    rw [abs_of_neg (inv_lt_zero.mpr hs), neg_inv]
  rw [habs]

lemma map_triangular_inner_first (k : ℕ) {h a : ℝ} (hh : 0 < h) (ha : 0 ≤ a) :
    Measure.map
        (fun r : ℝ => ((k : ℝ) + r) * h + a * triangularWave ((k : ℝ) + r))
        (volume.restrict (Set.Icc (0 : ℝ) (1 / 4))) =
      ENNReal.ofReal (h + 4 * a)⁻¹ •
        volume.restrict (Set.Icc ((k : ℝ) * h)
          ((k : ℝ) * h + h / 4 + a)) := by
  have hs : 0 < h + 4 * a := triangular_outer_slope_positive hh ha
  calc
    Measure.map
        (fun r : ℝ => ((k : ℝ) + r) * h + a * triangularWave ((k : ℝ) + r))
        (volume.restrict (Set.Icc (0 : ℝ) (1 / 4))) =
      Measure.map (fun r : ℝ => (k : ℝ) * h + (h + 4 * a) * r)
        (volume.restrict (Set.Icc (0 : ℝ) (1 / 4))) := by
          apply Measure.map_congr
          filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
          exact triangular_inner_first k h a r hr.1 hr.2
    _ = ENNReal.ofReal (h + 4 * a)⁻¹ •
        volume.restrict (Set.Icc ((k : ℝ) * h)
          ((k : ℝ) * h + h / 4 + a)) := by
          convert map_affine_restrict_Icc_of_pos ((k : ℝ) * h) (h + 4 * a)
            0 (1 / 4) hs using 1
          all_goals ring_nf

-- keep: reusable middle-branch pushforward identity for triangular folds
lemma map_triangular_inner_middle (k : ℕ) {h a : ℝ} (hh : 0 < h)
    (hscale : 4 ≤ a / h) :
    Measure.map
        (fun r : ℝ => ((k : ℝ) + r) * h + a * triangularWave ((k : ℝ) + r))
        (volume.restrict (Set.Icc (1 / 4 : ℝ) (3 / 4))) =
      ENNReal.ofReal (4 * a - h)⁻¹ •
        volume.restrict (Set.Icc ((k : ℝ) * h + 3 * h / 4 - a)
          ((k : ℝ) * h + h / 4 + a)) := by
  have hs : h - 4 * a < 0 := triangular_middle_slope_negative hh hscale
  calc
    Measure.map
        (fun r : ℝ => ((k : ℝ) + r) * h + a * triangularWave ((k : ℝ) + r))
        (volume.restrict (Set.Icc (1 / 4 : ℝ) (3 / 4))) =
      Measure.map (fun r : ℝ => (k : ℝ) * h + 2 * a + (h - 4 * a) * r)
        (volume.restrict (Set.Icc (1 / 4 : ℝ) (3 / 4))) := by
          apply Measure.map_congr
          filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
          exact triangular_inner_middle k h a r hr.1 hr.2
    _ = ENNReal.ofReal (4 * a - h)⁻¹ •
        volume.restrict (Set.Icc ((k : ℝ) * h + 3 * h / 4 - a)
          ((k : ℝ) * h + h / 4 + a)) := by
          convert map_affine_restrict_Icc_of_neg ((k : ℝ) * h + 2 * a)
            (h - 4 * a) (1 / 4) (3 / 4) hs (by norm_num) using 1
          all_goals ring_nf

lemma map_triangular_inner_last (k : ℕ) {h a : ℝ} (hh : 0 < h) (ha : 0 ≤ a) :
    Measure.map
        (fun r : ℝ => ((k : ℝ) + r) * h + a * triangularWave ((k : ℝ) + r))
        (volume.restrict (Set.Icc (3 / 4 : ℝ) 1)) =
      ENNReal.ofReal (h + 4 * a)⁻¹ •
        volume.restrict (Set.Icc ((k : ℝ) * h + 3 * h / 4 - a)
          (((k : ℝ) + 1) * h)) := by
  have hs : 0 < h + 4 * a := triangular_outer_slope_positive hh ha
  calc
    Measure.map
        (fun r : ℝ => ((k : ℝ) + r) * h + a * triangularWave ((k : ℝ) + r))
        (volume.restrict (Set.Icc (3 / 4 : ℝ) 1)) =
      Measure.map (fun r : ℝ => (k : ℝ) * h - 4 * a + (h + 4 * a) * r)
        (volume.restrict (Set.Icc (3 / 4 : ℝ) 1)) := by
          apply Measure.map_congr
          filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
          exact triangular_inner_last k h a r hr.1 hr.2
    _ = ENNReal.ofReal (h + 4 * a)⁻¹ •
        volume.restrict (Set.Icc ((k : ℝ) * h + 3 * h / 4 - a)
          (((k : ℝ) + 1) * h)) := by
          convert map_affine_restrict_Icc_of_pos ((k : ℝ) * h - 4 * a)
            (h + 4 * a) (3 / 4) 1 hs using 1
          all_goals ring_nf

end CausalSmith.Experimentation.PilotscorePairingFrontier

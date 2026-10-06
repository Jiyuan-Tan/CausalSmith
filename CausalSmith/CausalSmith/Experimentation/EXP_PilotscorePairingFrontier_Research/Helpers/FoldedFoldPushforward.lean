module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedPushforward

/-! # Pushforward through the three affine regions of `triangularFold` -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory

lemma map_triangularFold_restrict_middle (S : Set ℝ) (hS : MeasurableSet S)
    (hsub : S ⊆ Set.Icc (0 : ℝ) 1) :
    Measure.map triangularFold (volume.restrict S) = volume.restrict S := by
  calc
    Measure.map triangularFold (volume.restrict S) =
        Measure.map id (volume.restrict S) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem hS] with t ht
      simpa using triangularFold_eq_self (hsub ht)
    _ = volume.restrict S := Measure.map_id

lemma map_triangularFold_restrict_left (S : Set ℝ) (hS : MeasurableSet S)
    (hsub : S ⊆ Set.Icc (-1 : ℝ) 0) :
    Measure.map triangularFold (volume.restrict S) =
      volume.restrict ((fun t : ℝ => -t) '' S) := by
  calc
    Measure.map triangularFold (volume.restrict S) =
        Measure.map (fun t : ℝ => -t) (volume.restrict S) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem hS] with t ht
      exact triangularFold_eq_neg (hsub ht)
    _ = volume.restrict ((fun t : ℝ => -t) '' S) := by
      simpa using map_affine_restrict 0 (-1) (by norm_num) S hS

lemma map_triangularFold_restrict_right (S : Set ℝ) (hS : MeasurableSet S)
    (hsub : S ⊆ Set.Icc (1 : ℝ) 2) :
    Measure.map triangularFold (volume.restrict S) =
      volume.restrict ((fun t : ℝ => 2 - t) '' S) := by
  calc
    Measure.map triangularFold (volume.restrict S) =
        Measure.map (fun t : ℝ => 2 - t) (volume.restrict S) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem hS] with t ht
      exact triangularFold_eq_two_sub (hsub ht)
    _ = volume.restrict ((fun t : ℝ => 2 - t) '' S) := by
      simpa [sub_eq_add_neg] using map_affine_restrict 2 (-1) (by norm_num) S hS

end CausalSmith.Experimentation.PilotscorePairingFrontier

module
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedTargetConcentration

/-!
# Finite tail bound for the paired target

The variance of the balanced product-prior L1 target controls the mass of
parameters whose target is far from its exact prior mean.
-/

public section

namespace Causalean.Stat.Minimax.Multinomial.TwoSampleL1

open scoped BigOperators ENNReal

/-- Given [a scalar moment prior](hyp:P), [a positive balanced pair count](hyp:b,hb), [a bounded nonnegative tilt](hyp:t,ht,ht1), [a positive target radius δ with 128·t² ≤ b·δ²](hyp:δ,hδ,hscale), and [a prior side](hyp:side), [the product-prior mass of node vectors whose L1 distance between the base and tilted vectors lies farther than δ/4 from its prior mean is at most one eighth](goal). -/
theorem pairedProductTarget_bad_mass_le {L : ℕ} (P : ScalarMomentPriors L)
    (b : ℕ) (hb : 0 < b) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) (hscale : 128 * t ^ 2 ≤ (b : ℝ) * δ ^ 2)
    (side : Bool) :
    (∑ u : Fin b → Fin P.m,
      if δ / 4 <
          |simplexL1 (pairedBaseVector b hb)
              (pairedTiltVector b hb t ht ht1 (pairedNodeVector P u)
                (pairedNodeVector_abs_le_one P u)) -
            t * (∑ i : Fin P.m, scalarPriorWeight P side i * |P.node i|)|
      then pairedProductWeight P b side u else 0) ≤ (1 / 8 : ℝ≥0∞) := by
  classical
  let X : (Fin b → Fin P.m) → ℝ := fun u =>
    simplexL1 (pairedBaseVector b hb)
        (pairedTiltVector b hb t ht ht1 (pairedNodeVector P u)
          (pairedNodeVector_abs_le_one P u)) -
      t * (∑ i : Fin P.m, scalarPriorWeight P side i * |P.node i|)
  let w : (Fin b → Fin P.m) → ℝ≥0∞ := pairedProductWeight P b side
  have hwfinite (u : Fin b → Fin P.m) : w u ≠ ⊤ := by
    have hu : w u ≤ ∑ v : Fin b → Fin P.m, w v :=
      Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ u)
    rw [show (∑ v : Fin b → Fin P.m, w v) = 1 from
      pairedProductWeight_sum P b side] at hu
    exact ne_top_of_le_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hu
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hpoint (u : Fin b → Fin P.m) :
      (if δ / 4 < |X u| then (w u).toReal else 0) * δ ^ 2 ≤
        16 * ((w u).toReal * X u ^ 2) := by
    split_ifs with hbad
    · have hsquare : δ ^ 2 < 16 * X u ^ 2 := by
        nlinarith [sq_nonneg (|X u| - δ / 4), sq_abs (X u)]
      exact (mul_le_mul_of_nonneg_left hsquare.le
        (show 0 ≤ (w u).toReal from ENNReal.toReal_nonneg)).trans_eq
        (by ring)
    · nlinarith [show 0 ≤ (w u).toReal from ENNReal.toReal_nonneg,
        sq_nonneg (X u)]
  have hsum :
      (∑ u : Fin b → Fin P.m,
        if δ / 4 < |X u| then (w u).toReal else 0) * δ ^ 2 ≤
        16 * (t ^ 2 / (b : ℝ)) := by
    calc
      _ = ∑ u : Fin b → Fin P.m,
          (if δ / 4 < |X u| then (w u).toReal else 0) * δ ^ 2 := by
            rw [Finset.sum_mul]
      _ ≤ ∑ u : Fin b → Fin P.m, 16 * ((w u).toReal * X u ^ 2) :=
        Finset.sum_le_sum (by intro u _; exact hpoint u)
      _ = 16 * ∑ u : Fin b → Fin P.m, (w u).toReal * X u ^ 2 := by
        rw [Finset.mul_sum]
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_left
          (pairedProductTarget_variance_le P b hb t ht ht1 side) (by norm_num)
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  have hratio : t ^ 2 / (b : ℝ) ≤ δ ^ 2 / 128 := by
    apply (div_le_iff₀ hbpos).2
    nlinarith [hscale]
  have hreal :
      (∑ u : Fin b → Fin P.m,
        if δ / 4 < |X u| then (w u).toReal else 0) ≤ (1 / 8 : ℝ) := by
    have h := hsum.trans (mul_le_mul_of_nonneg_left hratio (by norm_num))
    nlinarith
  have hmass :
      (∑ u : Fin b → Fin P.m, if δ / 4 < |X u| then w u else 0) =
        ENNReal.ofReal (∑ u : Fin b → Fin P.m,
          if δ / 4 < |X u| then (w u).toReal else 0) := by
    rw [ENNReal.ofReal_sum_of_nonneg (by
      intro u _
      split_ifs <;> simp [ENNReal.toReal_nonneg])]
    apply Finset.sum_congr rfl
    intro u _
    split_ifs <;> simp [ENNReal.ofReal_toReal (hwfinite u)]
  change (∑ u : Fin b → Fin P.m, if δ / 4 < |X u| then w u else 0) ≤ 1 / 8
  rw [hmass]
  exact (ENNReal.ofReal_le_ofReal hreal).trans_eq (by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 8)]
    norm_num)

end Causalean.Stat.Minimax.Multinomial.TwoSampleL1

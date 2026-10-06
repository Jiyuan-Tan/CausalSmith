module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedScoreAlgebra

/-! # Affine branches of the triangular wave -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

private lemma floor_nat_add_frac (k : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Int.floor ((k : ℝ) + r) = (k : ℤ) := by
  rw [Int.floor_eq_iff]
  constructor <;> norm_num <;> linarith

lemma triangularWave_nat_add_first (k : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 4) :
    triangularWave ((k : ℝ) + r) = 4 * r := by
  have hf := floor_nat_add_frac k hr0 (hr1.trans_lt (by norm_num))
  unfold triangularWave
  rw [show (k : ℝ) + r - ↑⌊(k : ℝ) + r⌋ = r by rw [hf]; norm_num]
  rw [if_pos hr1]

lemma triangularWave_nat_add_middle (k : ℕ) {r : ℝ}
    (hr0 : 1 / 4 ≤ r) (hr1 : r ≤ 3 / 4) :
    triangularWave ((k : ℝ) + r) = 2 - 4 * r := by
  have hf := floor_nat_add_frac k (by linarith) (hr1.trans_lt (by norm_num))
  unfold triangularWave
  rw [show (k : ℝ) + r - ↑⌊(k : ℝ) + r⌋ = r by rw [hf]; norm_num]
  change (if r ≤ 1 / 4 then 4 * r else if r ≤ 3 / 4 then 2 - 4 * r
    else 4 * r - 4) = 2 - 4 * r
  split
  next h => linarith
  next h => rfl

lemma triangularWave_nat_add_last (k : ℕ) {r : ℝ}
    (hr0 : 3 / 4 ≤ r) (hr1 : r ≤ 1) :
    triangularWave ((k : ℝ) + r) = 4 * r - 4 := by
  rcases lt_or_eq_of_le hr1 with hlt | rfl
  · have hf := floor_nat_add_frac k (by linarith) hlt
    unfold triangularWave
    rw [show (k : ℝ) + r - ↑⌊(k : ℝ) + r⌋ = r by rw [hf]; norm_num]
    change (if r ≤ 1 / 4 then 4 * r else if r ≤ 3 / 4 then 2 - 4 * r
      else 4 * r - 4) = 4 * r - 4
    split
    next h => linarith
    next h =>
      split
      next h' => linarith
      next h' => rfl
  · norm_num [triangularWave]

lemma triangular_inner_first (k : ℕ) (h a r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 4) :
    ((k : ℝ) + r) * h + a * triangularWave ((k : ℝ) + r) =
      (k : ℝ) * h + (h + 4 * a) * r := by
  rw [triangularWave_nat_add_first k hr0 hr1]
  ring

lemma triangular_inner_middle (k : ℕ) (h a r : ℝ)
    (hr0 : 1 / 4 ≤ r) (hr1 : r ≤ 3 / 4) :
    ((k : ℝ) + r) * h + a * triangularWave ((k : ℝ) + r) =
      (k : ℝ) * h + 2 * a + (h - 4 * a) * r := by
  rw [triangularWave_nat_add_middle k hr0 hr1]
  ring

lemma triangular_inner_last (k : ℕ) (h a r : ℝ)
    (hr0 : 3 / 4 ≤ r) (hr1 : r ≤ 1) :
    ((k : ℝ) + r) * h + a * triangularWave ((k : ℝ) + r) =
      (k : ℝ) * h - 4 * a + (h + 4 * a) * r := by
  rw [triangularWave_nat_add_last k hr0 hr1]
  ring

lemma triangular_middle_slope_negative {h a : ℝ} (hh : 0 < h)
    (hscale : 4 ≤ a / h) : h - 4 * a < 0 := by
  have ha : 4 * h ≤ a := (le_div_iff₀ hh).mp hscale
  linarith

lemma triangular_outer_slope_positive {h a : ℝ} (hh : 0 < h) (ha : 0 ≤ a) :
    0 < h + 4 * a := by linarith

end CausalSmith.Experimentation.PilotscorePairingFrontier

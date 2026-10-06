module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.HeavyNoiseRate

/-! Exponential missing-arm summation for the heavy correction. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open scoped BigOperators

lemma mass_mul_heavy_exp_le {m p : ℝ} (hm : 0 < m) (hp : 0 ≤ p) :
    p * Real.exp (-m * p / 4) ≤ 4 / m := by
  let y := m * p / 4
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hcore := Real.mul_exp_neg_le_exp_neg_one y
  have hexp1 : Real.exp (-1) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by norm_num)
  have hscale : 0 ≤ 4 / m := by positivity
  calc
    p * Real.exp (-m * p / 4) = (4 / m) * (y * Real.exp (-y)) := by
      dsimp [y]
      field_simp
    _ ≤ (4 / m) * Real.exp (-1) := mul_le_mul_of_nonneg_left hcore hscale
    _ ≤ (4 / m) * 1 := mul_le_mul_of_nonneg_left hexp1 hscale
    _ = 4 / m := by ring

/-- Equation (41), with explicit constant four. -/
lemma sum_cellMass_sq_heavy_exp_le {n : ℕ} (P : Law n) (hn : 0 < n) :
    (∑ k : Fin n, P.cellMass k ^ 2 *
        Real.exp (-blockMean n * P.cellMass k / 4)) ≤
      4 / blockMean n := by
  have hm : 0 < blockMean n := blockMean_pos n hn
  calc
    _ = ∑ k : Fin n, P.cellMass k *
        (P.cellMass k * Real.exp (-blockMean n * P.cellMass k / 4)) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ ∑ k : Fin n, P.cellMass k * (4 / blockMean n) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left
        (mass_mul_heavy_exp_le hm (P.cellMass_range k).1)
        (P.cellMass_range k).1
    _ = 4 / blockMean n := by
      rw [← Finset.sum_mul,
        DiscreteAteHeterogeneityFrontier.sum_cellMass_eq_one]
      ring

/-- The complete missing-arm expression in (39), summed over cells. -/
lemma sum_heavy_missing_expression_le {n : ℕ} (P : Law n) (hn : 0 < n) :
    (∑ k : Fin n, (P.cellMass k ^ 2 +
        P.cellMass k / blockMean n) *
        Real.exp (-blockMean n * P.cellMass k / 4)) ≤
      5 / blockMean n := by
  have hm : 0 < blockMean n := blockMean_pos n hn
  have hexp (k : Fin n) :
      Real.exp (-blockMean n * P.cellMass k / 4) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have hp0 := (P.cellMass_range k).1
    nlinarith [mul_nonneg hm.le hp0]
  calc
    _ = (∑ k : Fin n, P.cellMass k ^ 2 *
          Real.exp (-blockMean n * P.cellMass k / 4)) +
        ∑ k : Fin n, (P.cellMass k / blockMean n) *
          Real.exp (-blockMean n * P.cellMass k / 4) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ 4 / blockMean n + ∑ k : Fin n, P.cellMass k / blockMean n := by
      apply add_le_add (sum_cellMass_sq_heavy_exp_le P hn)
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_of_le_one_right
        (div_nonneg (P.cellMass_range k).1 hm.le) (hexp k)
    _ = 5 / blockMean n := by
      rw [← Finset.sum_div,
        DiscreteAteHeterogeneityFrontier.sum_cellMass_eq_one]
      field_simp
      norm_num

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.BiasVariance

/-!
# Deterministic heavy-cell variance assembly

These bounds turn a within-stream heavy-correction variance estimate into the
cellwise and aggregate product-variance budget in equation (16).
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open scoped BigOperators

-- @node: heavyProductVariance_algebra_le
/-- Product-moment algebra bounds one heavy-cell correction variance from its
within-stream variance and centered-mean bounds. Given [the specified input `w`](hyp:w), [the specified input `m`](hyp:m), [the specified input `z`](hyp:z), [the specified input `hw`](hyp:hw), [the specified input `hm`](hyp:hm), [the specified input `hz`](hyp:hz), [the stated mathematical conclusion holds](goal). Given [the specified input `ν`](hyp:ν), [the specified input `μ`](hyp:μ), [the specified input `hμ`](hyp:hμ). Given [the specified input `hν`](hyp:hν). -/
lemma heavyProductVariance_algebra_le {w m z ν μ : ℝ}
    (hw : 0 ≤ w) (hm : 0 < m) (hz : 0 ≤ z)
    (hν : ν ≤ 4 / (1 + z)) (hμ : μ ^ 2 ≤ 1 / 4) :
    (w ^ 2 + w / m) * (ν + μ ^ 2) - (w * μ) ^ 2 ≤
      4 * w ^ 2 / (1 + z) + (17 / 4) * (w / m) := by
  have hwm : 0 ≤ w / m := div_nonneg hw hm.le
  have hcoef : 0 ≤ w ^ 2 + w / m := by positivity
  have hden : 0 < 1 + z := by linarith
  have hνmul := mul_le_mul_of_nonneg_left hν hcoef
  have hμmul := mul_le_mul_of_nonneg_left hμ hwm
  have hfrac : 4 * (w / m) / (1 + z) ≤ 4 * (w / m) := by
    rw [div_le_iff₀ hden]
    nlinarith
  calc
    (w ^ 2 + w / m) * (ν + μ ^ 2) - (w * μ) ^ 2 =
        (w ^ 2 + w / m) * ν + (w / m) * μ ^ 2 := by ring
    _ ≤ (w ^ 2 + w / m) * (4 / (1 + z)) +
        (w / m) * (1 / 4) := add_le_add hνmul hμmul
    _ = 4 * w ^ 2 / (1 + z) + 4 * (w / m) / (1 + z) +
        (w / m) / 4 := by ring
    _ ≤ 4 * w ^ 2 / (1 + z) + 4 * (w / m) + (w / m) / 4 := by
      linarith
    _ = 4 * w ^ 2 / (1 + z) + (17 / 4) * (w / m) := by ring

-- @node: heavyProductVariance_budget
/-- Summing the heavy-cell product-variance bounds costs at most a universal
multiple of the inverse stream intensity. Given [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the specified input `m`](hyp:m), [the specified input `hm`](hyp:hm), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
lemma heavyProductVariance_budget {d : ℕ} {q : ℝ}
    (P : FullLaw d) (h : LawClass d q P)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (m : ℝ) (hm : 0 < m) :
    (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      (4 * (missingCellMass P x a s) ^ 2 /
          (1 + m * arrivedCellMass P x a s) +
        (17 / 4 : ℝ) * (missingCellMass P x a s / m))) ≤
      17 / (4 * m) := by
  classical
  have hbase := missingCellMass_heavy_variance_budget P h hq m hm
  calc
    (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      (4 * (missingCellMass P x a s) ^ 2 /
          (1 + m * arrivedCellMass P x a s) +
        (17 / 4 : ℝ) * (missingCellMass P x a s / m))) ≤
        ∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
          (17 / 4 : ℝ) *
            (missingCellMass P x a s / m +
              (missingCellMass P x a s) ^ 2 /
                (1 + m * arrivedCellMass P x a s)) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro s hs
      have harr : 0 ≤ arrivedCellMass P x a s := arrivedCellMass_nonneg P x a s
      have hden : 0 < 1 + m * arrivedCellMass P x a s := by positivity
      have hquad : 0 ≤ (missingCellMass P x a s) ^ 2 /
          (1 + m * arrivedCellMass P x a s) := div_nonneg (sq_nonneg _) hden.le
      calc
        4 * (missingCellMass P x a s) ^ 2 /
              (1 + m * arrivedCellMass P x a s) +
            (17 / 4 : ℝ) * (missingCellMass P x a s / m) =
            4 * ((missingCellMass P x a s) ^ 2 /
              (1 + m * arrivedCellMass P x a s)) +
            (17 / 4 : ℝ) * (missingCellMass P x a s / m) := by ring
        _ ≤ (17 / 4 : ℝ) *
            (missingCellMass P x a s / m +
              (missingCellMass P x a s) ^ 2 /
                (1 + m * arrivedCellMass P x a s)) := by linarith
    _ = (17 / 4 : ℝ) *
        (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
          (missingCellMass P x a s / m +
            (missingCellMass P x a s) ^ 2 /
              (1 + m * arrivedCellMass P x a s))) := by
      simp only [Finset.mul_sum]
    _ ≤ (17 / 4 : ℝ) * (1 / m) :=
      mul_le_mul_of_nonneg_left hbase (by norm_num)
    _ = 17 / (4 * m) := by
      field_simp [ne_of_gt hm]

end CausalSmith.Stat.MarNearcompleteFrontier


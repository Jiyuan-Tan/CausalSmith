module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.ChebyshevBounds
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.CellBounds

/-! # Risk integrability for the finite observed-sample experiment -/

public section
namespace CausalSmith.Stat.MarNearcompleteFrontier
open MeasureTheory

/-- When [the target lies in the feasible treatment-effect interval](hyp:ht), [clipping an estimate to that interval cannot increase its squared error](goal). -/
lemma clipUnit_sq_error_le (z t : ℝ) (ht : t ∈ Set.Icc (-1) 1) :
    (clipUnit z - t) ^ 2 ≤ (z - t) ^ 2 := by
  rcases ht with ⟨htlo, hthi⟩
  by_cases hzlo : z < -1
  · rw [clipUnit, min_eq_right (by linarith), max_eq_left (le_of_lt hzlo)]
    nlinarith
  by_cases hzhi : 1 < z
  · rw [clipUnit, min_eq_left (le_of_lt hzhi), max_eq_right (by norm_num)]
    nlinarith
  rw [clipUnit, min_eq_right (by linarith), max_eq_right (by linarith)]

-- @node: missingWeight_sq_div_one_add_le
/-- The cellwise quadratic missing-mass term in equation (16) is absorbed by
its linear missing mass whenever the arrival-floor comparison
`w ≤ 2 * δ * t` holds. Given [the specified input `w`](hyp:w), [the specified input `t`](hyp:t), [the specified input `m`](hyp:m), [the specified input `hm`](hyp:hm), [the specified input `hw`](hyp:hw), [the specified input `ht`](hyp:ht), [the specified input `hwt`](hyp:hwt), [the stated mathematical conclusion holds](goal). Given [the specified input `δ`](hyp:δ), [the specified input `hδ`](hyp:hδ). -/
lemma missingWeight_sq_div_one_add_le {w t δ m : ℝ}
    (hm : 0 < m) (hw : 0 ≤ w) (ht : 0 ≤ t) (hδ : 0 ≤ δ)
    (hwt : w ≤ 2 * δ * t) :
    w ^ 2 / (1 + m * t) ≤ (2 * δ / m) * w := by
  have hden : 0 < 1 + m * t := by positivity
  rw [show (2 * δ / m) * w = (2 * δ * w) / m by ring]
  rw [div_le_div_iff₀ hden hm]
  have hmul := mul_le_mul_of_nonneg_left hwt (mul_nonneg hw hm.le)
  have hlin : 0 ≤ 2 * δ * w := by positivity
  nlinarith

/-- For [a law in the model class](hyp:h), [an admissible arrival floor](hyp:hq), and [a positive scale](hyp:hm), [the cellwise quadratic missing-mass terms are bounded by total missing mass and the arrival floor](goal). -/
lemma missingCellMass_variance_sum_le {d : ℕ} {q : ℝ} (P : FullLaw d)
    (h : LawClass d q P) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (m : ℝ) (hm : 0 < m) :
    (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      (missingCellMass P x a s) ^ 2 /
        (1 + m * arrivedCellMass P x a s)) ≤
      2 * (delta q) ^ 2 / m := by
  classical
  have hδ : 0 ≤ delta q := by
    unfold delta
    linarith [hq.2]
  have hfactor : 0 ≤ 2 * delta q / m := div_nonneg (by positivity) hm.le
  calc
    (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      (missingCellMass P x a s) ^ 2 /
        (1 + m * arrivedCellMass P x a s)) ≤
        ∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
          (2 * delta q / m) * missingCellMass P x a s := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro s hs
      have hb := missingCellMass_bounds P h hq x a s
      exact missingWeight_sq_div_one_add_le hm hb.1
        (arrivedCellMass_nonneg P x a s) hδ hb.2.2
    _ = (2 * delta q / m) *
        (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
          missingCellMass P x a s) := by
      simp only [Finset.mul_sum]
    _ ≤ (2 * delta q / m) * delta q :=
      mul_le_mul_of_nonneg_left (sum_missingCellMass_le_delta P h hq) hfactor
    _ = 2 * (delta q) ^ 2 / m := by ring

-- @node: missingCellMass_heavy_variance_budget
/-- The missing-cell terms in the heavy-branch variance sum are bounded by
one inverse stream intensity, uniformly over the alphabet. Given [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the specified input `m`](hyp:m), [the specified input `hm`](hyp:hm), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
lemma missingCellMass_heavy_variance_budget {d : ℕ} {q : ℝ}
    (P : FullLaw d) (h : LawClass d q P)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (m : ℝ) (hm : 0 < m) :
    (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      (missingCellMass P x a s / m +
        (missingCellMass P x a s) ^ 2 /
          (1 + m * arrivedCellMass P x a s))) ≤ 1 / m := by
  classical
  have hsum := sum_missingCellMass_le_delta P h hq
  have hvar := missingCellMass_variance_sum_le P h hq m hm
  have hδ0 : 0 ≤ delta q := by
    unfold delta
    linarith [hq.2]
  have hδhalf : delta q ≤ 1 / 2 := by
    unfold delta
    linarith [hq.1]
  have hpoly : delta q + 2 * (delta q) ^ 2 ≤ 1 := by
    nlinarith
  calc
    (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      (missingCellMass P x a s / m +
        (missingCellMass P x a s) ^ 2 /
          (1 + m * arrivedCellMass P x a s))) =
        (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
          missingCellMass P x a s) / m +
        (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
          (missingCellMass P x a s) ^ 2 /
            (1 + m * arrivedCellMass P x a s)) := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_div]
    _ ≤ delta q / m + 2 * (delta q) ^ 2 / m :=
      add_le_add ((div_le_div_iff_of_pos_right hm).2 hsum) hvar
    _ = (delta q + 2 * (delta q) ^ 2) / m := by ring
    _ ≤ 1 / m := (div_le_div_iff_of_pos_right hm).2 hpoly

end CausalSmith.Stat.MarNearcompleteFrontier

module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.T_KnownMarginalBoundary
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.T_InverseCountBaseline
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.ParametricLabelFloor

/-! The binary-covariate parametric endpoint. -/

public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

-- @node: prop:binary-alphabet-parametric-rate
/-- At alphabet size two, auxiliary annotation cannot improve the parametric order.  [the stated conditions](hyp:heps,heps2) [the stated conclusion](goal). -/
theorem binary_alphabet_parametric_rate {eps : Real}
    (heps : 0 < eps) (heps2 : eps < 1 / 2) :
    ∃ c C : Real, 0 < c ∧ c ≤ C ∧ ∀ (n m : Nat), 1 ≤ n →
      c / n ≤ minimaxRisk n m 2 eps ∧
        minimaxRisk n m 2 eps ≤ C / n := by
  obtain ⟨c, hc, hlower⟩ := parametric_label_floor
  obtain ⟨C, hC, hupper⟩ := inverse_count_baseline heps heps2
  refine ⟨c, max c (5 * C), hc, le_max_left _ _, ?_⟩
  intro n m hn
  constructor
  · exact hlower eps heps heps2 n m 2 hn (by omega)
  · have hu := (hupper n m 2 hn (by omega)).2.2
    have hn0 : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
    have hnm : (n : Real) ≤ (n + m : Nat) := by
      exact_mod_cast Nat.le_add_right n m
    have hnm0 : (0 : Real) < (n + m : Nat) := lt_of_lt_of_le hn0 hnm
    have hn_one : (1 : Real) ≤ n := by exact_mod_cast hn
    have hnm_one : (1 : Real) ≤ (n + m : Nat) := le_trans hn_one hnm
    calc
      minimaxRisk n m 2 eps
          ≤ C * min 1
            (1 / (n : Real) + (2 : Real) ^ 2 /
              ((n + m : Nat) : Real) ^ 2) := hu
      _ ≤ C * (1 / (n : Real) + (2 : Real) ^ 2 /
            ((n + m : Nat) : Real) ^ 2) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le
      _ ≤ C * (5 / (n : Real)) := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        rw [show (2 : Real) ^ 2 = 4 by norm_num]
        have hsquare : (n : Real) ≤ ((n + m : Nat) : Real) ^ 2 := by
          have hprod := mul_nonneg hnm0.le (sub_nonneg.mpr hnm_one)
          nlinarith
        have hdiv : 4 / ((n + m : Nat) : Real) ^ 2 ≤ 4 / (n : Real) := by
          exact (div_le_div_iff_of_pos_left (by norm_num)
            (sq_pos_of_pos hnm0) hn0).2 hsquare
        calc
          1 / (n : Real) + 4 / ((n + m : Nat) : Real) ^ 2
              ≤ 1 / (n : Real) + 4 / (n : Real) := by linarith
          _ = 5 / (n : Real) := by ring
      _ = (5 * C) / n := by ring
      _ ≤ max c (5 * C) / n := by
        exact (div_le_div_iff_of_pos_right hn0).2 (le_max_right _ _)

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

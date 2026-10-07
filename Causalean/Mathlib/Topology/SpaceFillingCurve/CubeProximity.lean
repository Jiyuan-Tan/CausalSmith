module
public import Causalean.Mathlib.Topology.SpaceFillingCurve.CurveCells

/-!
# Points in consecutive cells of a dyadic traversal are close

For a dyadic traversal of the d-dimensional cube at level n, which visits the 2^(d·n) closed
dyadic cells of side 2^(−n) in an order where consecutive cells share a face, any two points lying
in the same cell or in consecutive cells have squared Euclidean distance at most 4·d·2^(−2n).
This is the locality property of a space-filling-curve ordering: neighbours in the ordering are
neighbours in space.

## Main results

* `sqEuclideanDist_le_of_neighboring_cubeCells` — the squared-distance bound 4·d·(2^(−n))² for
  points in cells whose indices differ by at most one.
-/

public section

namespace Causalean.Mathlib.Topology.SpaceFillingCurve

/-- Given [a dimension and level](hyp:d,n), [a traversal and two cell indices that are equal or consecutive](hyp:T,k,l,hkl),
and [points localized in those cells](hyp:x,y,hx,hy), [their squared Euclidean distance is at most four times the dimension times the squared cell width `2^(-n)`](goal). -/
theorem sqEuclideanDist_le_of_neighboring_cubeCells {d n : ℕ}
    (T : DyadicTraversal d) (k l : Fin (2 ^ (d * n)))
    (hkl : k.val ≤ l.val + 1 ∧ l.val ≤ k.val + 1)
    (x y : Fin d → ℝ)
    (hx : dyadicCubeCell T n k x) (hy : dyadicCubeCell T n l y) :
    sqEuclideanDist x y ≤
      4 * (d : ℝ) * ((1 : ℝ) / (2 : ℝ) ^ n) ^ 2 := by
  -- Split into equal cells or either orientation of consecutive indices.
  -- In every coordinate the two cell points differ by at most two widths.
  -- For consecutive indices, `T.adjacent` says that one grid coordinate
  -- changes by one and all the rest agree. From `hx i` and `hy i`, multiply
  -- interval endpoints by the positive denominator `2^n` to get
  -- `|x i - y i| ≤ 2 / 2^n`; the equal-index case has the same bound.
  -- Bound each squared summand, then sum over `Fin d` and simplify its card.
  have hgrid (i : Fin d) :
      (T.cell n k i).val ≤ (T.cell n l i).val + 1 ∧
      (T.cell n l i).val ≤ (T.cell n k i).val + 1 := by
    by_cases heq : k = l
    · subst l
      exact ⟨by omega, by omega⟩
    · have hcases : l.val = k.val + 1 ∨ k.val = l.val + 1 := by
        have hne : k.val ≠ l.val := fun h => heq (Fin.ext h)
        omega
      rcases hcases with hnext | hprev
      · obtain ⟨j, hj, hs⟩ := T.adjacent n k l hnext
        by_cases hij : i = j
        · subst i
          rcases hj with h | h <;> omega
        · rw [hs i hij]
          exact ⟨by omega, by omega⟩
      · obtain ⟨j, hj, hs⟩ := T.adjacent n l k hprev
        by_cases hij : i = j
        · subst i
          rcases hj with h | h <;> omega
        · rw [hs i hij]
          exact ⟨by omega, by omega⟩
  have hq : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hcoord (i : Fin d) :
      -(2 / (2 : ℝ) ^ n) ≤ x i - y i ∧
        x i - y i ≤ 2 / (2 : ℝ) ^ n := by
    obtain ⟨hxl, hxu⟩ := hx i
    obtain ⟨hyl, hyu⟩ := hy i
    obtain ⟨hkl', hlk'⟩ := hgrid i
    have hkl'' : ((T.cell n k i).val : ℝ) ≤ (T.cell n l i).val + 1 := by
      exact_mod_cast hkl'
    have hlk'' : ((T.cell n l i).val : ℝ) ≤ (T.cell n k i).val + 1 := by
      exact_mod_cast hlk'
    have hxl' := (div_le_iff₀ hq).mp hxl
    have hxu' := (le_div_iff₀ hq).mp hxu
    have hyl' := (div_le_iff₀ hq).mp hyl
    have hyu' := (le_div_iff₀ hq).mp hyu
    have hleft : y i - x i ≤ 2 / (2 : ℝ) ^ n :=
      (le_div_iff₀ hq).2 (by nlinarith)
    have hright : x i - y i ≤ 2 / (2 : ℝ) ^ n :=
      (le_div_iff₀ hq).2 (by nlinarith)
    constructor <;> linarith
  calc
    sqEuclideanDist x y = ∑ i : Fin d, (x i - y i) ^ 2 := rfl
    _ ≤ ∑ _i : Fin d, (2 / (2 : ℝ) ^ n) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact sq_le_sq' (hcoord i).1 (hcoord i).2
    _ = 4 * (d : ℝ) * ((1 : ℝ) / (2 : ℝ) ^ n) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      ring

end Causalean.Mathlib.Topology.SpaceFillingCurve

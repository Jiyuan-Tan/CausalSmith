module
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Real.Basic

/-!
# Products of distances on an equispaced finite grid

The two sides of a deleted grid point give separate factorial products. These finite-product
identities isolate the arithmetic in the denominator of a Lagrange basis polynomial.
-/

public section

open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev

/-- The product of positive integer distances from `j` to the indices below it is `j!`.

Reflect `Finset.range j`, then use `Finset.prod_range_add_one_eq_factorial`. -/
theorem equispacedDistance_lower_factorial (j : ℕ) :
    (∏ i ∈ Finset.range j, ((j : ℝ) - (i : ℝ))) = (j.factorial : ℝ) := by
  calc
    (∏ i ∈ Finset.range j, ((j : ℝ) - (i : ℝ))) =
        ∏ i ∈ Finset.range j, (((j - 1 - i + 1 : ℕ) : ℝ)) := by
          apply Finset.prod_congr rfl
          intro i hi
          have hij : i < j := Finset.mem_range.mp hi
          rw [← Nat.cast_sub (Nat.le_of_lt hij)]
          congr 1
          omega
    _ = ∏ i ∈ Finset.range j, (((i + 1 : ℕ) : ℝ)) :=
      Finset.prod_range_reflect (fun i : ℕ => ((i + 1 : ℕ) : ℝ)) j
    _ = (j.factorial : ℝ) := by
      norm_cast
      exact Finset.prod_range_add_one_eq_factorial j

/-- The product of positive integer distances from `j` to the indices above it through `D`
is `(D-j)!`.

Translate `Finset.Ico (j+1) (D+1)` to `range (D-j)` and apply the factorial product formula. -/
theorem equispacedDistance_upper_factorial (D : ℕ) (j : Fin (D + 1)) :
    (∏ i ∈ Finset.Ico ((j : ℕ) + 1) (D + 1), ((i : ℝ) - (j : ℝ))) =
      ((D - (j : ℕ)).factorial : ℝ) := by
  rw [Finset.prod_Ico_eq_prod_range]
  have hj : (j : ℕ) ≤ D := Nat.lt_succ_iff.mp j.isLt
  have hsub : D + 1 - ((j : ℕ) + 1) = D - (j : ℕ) := by omega
  rw [hsub]
  calc
    _ = ∏ i ∈ Finset.range (D - (j : ℕ)), (((i + 1 : ℕ) : ℝ)) := by
          apply Finset.prod_congr rfl
          intro i hi
          push_cast
          ring
    _ = ((D - (j : ℕ)).factorial : ℝ) := by
      norm_cast
      exact Finset.prod_range_add_one_eq_factorial _

/-- For [a grid order D and a grid index j between 0 and D](hyp:D,j), [the product of the distances |j − i| over all grid indices i other than j equals the product of j − i over i below j times the product of i − j over i from j + 1 to D](goal).

Splitting the deleted finite grid at `j` expresses its absolute distance product as the
product over the indices below `j` and the indices above `j`.

Partition `univ.erase j` by `< j` and `j < ·`; use `Fin.sum_univ_eq_sum_range` or a finite
equivalence to reindex each part, then remove the absolute values by their sign.
-/
theorem equispacedDistance_erase_split (D : ℕ) (j : Fin (D + 1)) :
    (∏ i ∈ (Finset.univ : Finset (Fin (D + 1))).erase j,
      |(j : ℝ) - (i : ℝ)|) =
      (∏ i ∈ Finset.range (j : ℕ), ((j : ℝ) - (i : ℝ))) *
        (∏ i ∈ Finset.Ico ((j : ℕ) + 1) (D + 1), ((i : ℝ) - (j : ℝ))) := by
  classical
  have hdisj : Disjoint (Finset.range (j : ℕ))
      (Finset.Ico ((j : ℕ) + 1) (D + 1)) := by
    apply Finset.disjoint_left.mpr
    intro i hi₁ hi₂
    have h₁ := Finset.mem_range.mp hi₁
    have h₂ := (Finset.mem_Ico.mp hi₂).1
    omega
  calc
    (∏ i ∈ (Finset.univ : Finset (Fin (D + 1))).erase j,
        |(j : ℝ) - (i : ℝ)|) =
        ∏ i ∈ Finset.range (j : ℕ) ∪ Finset.Ico ((j : ℕ) + 1) (D + 1),
          |(j : ℝ) - (i : ℝ)| := by
            apply Finset.prod_bij (fun (i : Fin (D + 1)) _ => i.val)
            · intro i hi
              have hne : i ≠ j := (Finset.mem_erase.mp hi).1
              have hlt : (i : ℕ) < D + 1 := i.isLt
              simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
              omega
            · intro i hi k hk heq
              exact Fin.ext heq
            · intro k hk
              have hmem : k < D + 1 := by
                rcases Finset.mem_union.mp hk with h | h
                · have hj : (j : ℕ) < D + 1 := j.isLt
                  exact lt_trans (Finset.mem_range.mp h) hj
                · exact (Finset.mem_Ico.mp h).2
              refine ⟨⟨k, hmem⟩, ?_, rfl⟩
              simp only [Finset.mem_erase, Finset.mem_univ, and_true]
              rcases Finset.mem_union.mp hk with h | h
              · have hlt := Finset.mem_range.mp h
                exact Fin.ne_of_val_ne (by omega : k ≠ (j : ℕ))
              · have hgt := (Finset.mem_Ico.mp h).1
                exact Fin.ne_of_val_ne (by omega : k ≠ (j : ℕ))
            · intro i hi
              rfl
    _ = (∏ i ∈ Finset.range (j : ℕ), |(j : ℝ) - (i : ℝ)|) *
        (∏ i ∈ Finset.Ico ((j : ℕ) + 1) (D + 1), |(j : ℝ) - (i : ℝ)|) := by
          exact Finset.prod_union hdisj
    _ = (∏ i ∈ Finset.range (j : ℕ), ((j : ℝ) - (i : ℝ))) *
        (∏ i ∈ Finset.Ico ((j : ℕ) + 1) (D + 1), ((i : ℝ) - (j : ℝ))) := by
          congr 1
          · apply Finset.prod_congr rfl
            intro i hi
            rw [abs_of_nonneg]
            exact sub_nonneg.mpr (by exact_mod_cast (Finset.mem_range.mp hi).le)
          · apply Finset.prod_congr rfl
            intro i hi
            rw [abs_sub_comm, abs_of_nonneg]
            exact sub_nonneg.mpr (by exact_mod_cast (Nat.le_of_lt (by
              have hgt := (Finset.mem_Ico.mp hi).1
              omega : (j : ℕ) < i)))

end Causalean.Mathlib.Analysis.Approximation.Chebyshev


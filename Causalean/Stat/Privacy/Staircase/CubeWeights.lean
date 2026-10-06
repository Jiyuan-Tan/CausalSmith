module
public import Mathlib

/-!
# Finite cube product weights

Independent two-point weights on four coordinates express every point of the unit cube
as a convex combination of its sixteen vertices. These identities are the algebraic
input to the measurable staircase selector.
-/

@[expose] public section

noncomputable section

namespace Causalean.Stat.Privacy.Staircase

/-- The product weight of a subset selects `t i` on its members and `1 - t i`
on its complement. -/
def cubeWeight (t : Fin 4 → ℝ) (S : Finset (Fin 4)) : ℝ :=
  ∏ i : Fin 4, if i ∈ S then t i else 1 - t i

/-- Every cube vertex has nonnegative product weight when all four coordinates
lie in the unit interval. -/
theorem cubeWeight_nonneg (t : Fin 4 → ℝ)
    (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) (S : Finset (Fin 4)) :
    0 ≤ cubeWeight t S := by
  unfold cubeWeight
  apply Finset.prod_nonneg
  intro i _
  split
  · exact (ht i).1
  · linarith [(ht i).2]

/-- The product weights of all sixteen cube vertices sum to one.

Proof hint: expand `∏ i, (t i + (1 - t i))` with `Finset.prod_add`;
its powerset is `Finset.univ` here. -/
theorem cubeWeight_sum (t : Fin 4 → ℝ) :
    (∑ S : Finset (Fin 4), cubeWeight t S) = 1 := by
  have hweight (S : Finset (Fin 4)) :
      cubeWeight t S = (∏ j ∈ S, t j) * ∏ j ∈ Sᶜ, (1 - t j) := by
    have h : (Finset.univ.filter (fun j : Fin 4 => j ∉ S)) = Sᶜ := by
      ext j
      simp
    simp [cubeWeight, Finset.prod_ite, h]
  calc
    (∑ S : Finset (Fin 4), cubeWeight t S) =
        ∏ j : Fin 4, (t j + (1 - t j)) := by
          rw [Fintype.prod_add]
          simp only [hweight]
    _ = 1 := by simp

/-- Given [four unit-cube coordinates](hyp:t) and [one selected coordinate](hyp:i), the
[weighted coordinate indicator has expectation equal to that coordinate](goal) under the product
weights on the sixteen cube vertices.

Proof hint: split the sum by membership of `i`, factor out `t i`, and apply
`cubeWeight_sum` to the remaining three coordinates. -/
theorem cubeWeight_coordinate (t : Fin 4 → ℝ) (i : Fin 4) :
    (∑ S : Finset (Fin 4), cubeWeight t S * (if i ∈ S then 1 else 0)) = t i := by
  let g : Fin 4 → ℝ := fun j => if j = i then 0 else 1 - t j
  have hterm (S : Finset (Fin 4)) :
      cubeWeight t S * (if i ∈ S then 1 else 0) =
        ∏ j : Fin 4, if j ∈ S then t j else g j := by
    by_cases hi : i ∈ S
    · simp only [if_pos hi, mul_one]
      unfold cubeWeight
      apply Finset.prod_congr rfl
      intro j _
      by_cases hji : j = i <;> simp [g, hji, hi]
    · simp only [if_neg hi, mul_zero]
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [g, hi])).symm
  have hweight (S : Finset (Fin 4)) :
      (∏ j : Fin 4, if j ∈ S then t j else g j) =
        (∏ j ∈ S, t j) * ∏ j ∈ Sᶜ, g j := by
    have h : (Finset.univ.filter (fun j : Fin 4 => j ∉ S)) = Sᶜ := by
      ext j
      simp
    simp [Finset.prod_ite, h]
  calc
    (∑ S : Finset (Fin 4), cubeWeight t S * (if i ∈ S then 1 else 0)) =
        ∏ j : Fin 4, (t j + g j) := by
          rw [Fintype.prod_add]
          simp only [← hweight, ← hterm]
    _ = t i := by
      have h : (fun j : Fin 4 => t j + g j) =
          (fun j => if j = i then t i else 1) := by
        funext j
        by_cases hji : j = i <;> simp [g, hji]
      rw [h]
      simp [Finset.prod_ite_eq']

end Causalean.Stat.Privacy.Staircase

module
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Constructions

/-!
# Four-state simplex rounding

Floor the first three simplex coordinates and assign their discarded mass to
the fourth coordinate. The decoded row has total-variation error at most 3/M.
-/

public section

namespace CausalSmith.Stat.PomdpBinaryhiddenRate

open scoped BigOperators
open Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation

/-- Flooring a unit-interval reward gives a grid coordinate with error at most 1/M. [Under the listed formal conditions](hyp:hM,hx), [the stated conclusion holds](goal).-/
-- @node: reward_grid_rounding
lemma reward_grid_rounding {M : Nat} (hM : 0 < M) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ u : Fin (M + 1), 0 ≤ x - (u.val : ℝ) / M ∧
      x - (u.val : ℝ) / M ≤ (M : ℝ)⁻¹ := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hfloor : Nat.floor ((M : ℝ) * x) ≤ M :=
    Nat.floor_le_of_le (by nlinarith [hx.2])
  refine ⟨⟨Nat.floor ((M : ℝ) * x), by omega⟩, ?_, ?_⟩
  · have hf := Nat.floor_le (mul_nonneg hMr.le hx.1)
    dsimp only
    exact sub_nonneg.mpr ((div_le_iff₀ hMr).mpr (by nlinarith))
  · have hf := Nat.lt_floor_add_one ((M : ℝ) * x)
    dsimp only
    rw [← one_div]
    apply (le_div_iff₀ hMr).mpr
    have he : (x - (Nat.floor ((M : ℝ) * x) : ℝ) / M) * M =
        x * M - Nat.floor ((M : ℝ) * x) := by field_simp
    rw [he]
    linarith

/-- Rounding three coordinates down and using a residual fourth coordinate
preserves the simplex, with total-variation error at most 3/M. [Under the listed formal conditions](hyp:hM,hp), [the stated conclusion holds](goal).-/
-- @node: simplex_grid_rounding
lemma simplex_grid_rounding {M : Nat} (hM : 0 < M)
    (p : Fin 4 → ℝ) (hp : IsProbabilityVector p) :
    ∃ u ∈ simplexGrid M,
      (1 / 2 : ℝ) * ∑ i : Fin 4, |p i - (u i).val / (M : ℝ)| ≤ 3 / M := by
  classical
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hsum : p 0 + p 1 + p 2 + p 3 = 1 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hp.2
  have hunit (i : Fin 4) : p i ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨hp.1 i, ?_⟩
    calc
      p i ≤ ∑ j : Fin 4, p j := Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)
      _ = 1 := hp.2
  obtain ⟨u0, h0, e0⟩ := reward_grid_rounding hM (hunit 0)
  obtain ⟨u1, h1, e1⟩ := reward_grid_rounding hM (hunit 1)
  obtain ⟨u2, h2, e2⟩ := reward_grid_rounding hM (hunit 2)
  have hcount : u0.val + u1.val + u2.val ≤ M := by
    have hdiv : ((u0.val + u1.val + u2.val : Nat) : ℝ) / M ≤ 1 := by
      simp only [Nat.cast_add, add_div]
      linarith [hp.1 3]
    exact_mod_cast (div_le_one hMr).mp hdiv
  let u3 : Fin (M + 1) := ⟨M - (u0.val + u1.val + u2.val), by omega⟩
  let u : Fin 4 → Fin (M + 1) := ![u0, u1, u2, u3]
  have hu : u ∈ simplexGrid M := by
    simp only [simplexGrid, Finset.mem_filter, Finset.mem_univ, true_and, IsGridRow]
    simp [u, u3, Fin.sum_univ_succ]
    omega
  have hres : p 3 - (u3.val : ℝ) / M =
      -((p 0 - (u0.val : ℝ) / M) + (p 1 - (u1.val : ℝ) / M) +
        (p 2 - (u2.val : ℝ) / M)) := by
    dsimp [u3]
    rw [Nat.cast_sub hcount]
    simp only [Nat.cast_add]
    field_simp
    nlinarith [hsum]
  refine ⟨u, hu, ?_⟩
  simp [Fin.sum_univ_succ, u]
  rw [abs_of_nonneg h0, abs_of_nonneg h1, abs_of_nonneg h2, hres,
    abs_neg, abs_of_nonneg (by linarith :
      0 ≤ (p 0 - (u0.val : ℝ) / M) + (p 1 - (u1.val : ℝ) / M) +
        (p 2 - (u2.val : ℝ) / M))]
  rw [← one_div] at e0 e1 e2
  linear_combination e0 + e1 + e2

end CausalSmith.Stat.PomdpBinaryhiddenRate

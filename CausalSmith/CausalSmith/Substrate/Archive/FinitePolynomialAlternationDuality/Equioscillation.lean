/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import CausalSmith.Substrate.Archive.FinitePolynomialAlternationDuality.BestApproximation
public import CausalSmith.Substrate.Archive.FinitePolynomialAlternationDuality.ExtremalPerturbation
public import CausalSmith.Substrate.Archive.FinitePolynomialAlternationDuality.ExtremalSignPolynomial

/-!
# Equioscillation of a best bounded-degree approximant

This module isolates the necessity direction of the classical Chebyshev
alternation theorem.  The downstream certificate module adds the canonical
normalized Lagrange weights to these extrema.
-/

@[expose] public section

open Polynomial Set

namespace CausalSmith.Substrate.FinitePolynomialAlternationDuality

/-- An equioscillation witness records a best degree-`L` polynomial and
`L+2` ordered interval points where its residual has the common optimal
magnitude with alternating signs. -/
structure EquioscillationWitness
    (f : ℝ → ℝ) (r s : ℝ) (L : ℕ) where
  approximant : Polynomial ℝ
  approximant_degree : approximant.natDegree ≤ L
  approximant_best :
    uniformApproxError f r s approximant = bestUniformApproxError f r s L
  nodes : Fin (L + 2) → ℝ
  nodes_strictMono : StrictMono nodes
  nodes_mem : ∀ i, nodes i ∈ Set.Icc r s
  orientation : ℝ
  orientation_eq : orientation = 1 ∨ orientation = -1
  equioscillation : ∀ i,
    f (nodes i) - approximant.eval (nodes i) =
      orientation * (-1 : ℝ) ^ (i : ℕ) * bestUniformApproxError f r s L

/-- Every continuous real target on a nondegenerate compact interval has a
best degree-`L` polynomial whose residual equioscillates at `L+2` strictly
ordered interval points. -/
theorem exists_equioscillationWitness
    {f : ℝ → ℝ} {r s : ℝ} (hrs : r < s)
    (hf : ContinuousOn f (Set.Icc r s)) (L : ℕ) :
    Nonempty (EquioscillationWitness f r s L) := by
  classical
  obtain ⟨Q, hQdegree, hQbest⟩ := exists_bestPolynomial hrs hf L
  let g : ℝ → ℝ := fun x ↦ f x - Q.eval x
  have hg : ContinuousOn g (Set.Icc r s) :=
    hf.sub Q.continuous.continuousOn
  have hgError : intervalSupNorm g r s = bestUniformApproxError f r s L := by
    simpa [g, uniformApproxError] using hQbest
  have hErrorNonneg : 0 ≤ bestUniformApproxError f r s L :=
    bestUniformApproxError_nonneg hrs hf L
  by_cases hErrorZero : bestUniformApproxError f r s L = 0
  · let nodes : Fin (L + 2) → ℝ := fun i ↦
      r + (i : ℝ) * (s - r) / (L + 1 : ℝ)
    have hdenom : 0 < (L + 1 : ℝ) := by positivity
    have hnodesMono : StrictMono nodes := by
      intro i j hij
      have hijReal : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
      dsimp [nodes]
      have hlength : 0 < s - r := sub_pos.mpr hrs
      simpa [add_comm] using add_lt_add_left
        (div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hijReal hlength) hdenom) r
    have hnodesMem : ∀ i, nodes i ∈ Set.Icc r s := by
      intro i
      have hi : (i : ℕ) ≤ L + 1 := by omega
      have hiReal : (i : ℝ) ≤ (L + 1 : ℝ) := by exact_mod_cast hi
      have hiNonneg : (0 : ℝ) ≤ (i : ℝ) := by positivity
      have hlength : 0 < s - r := sub_pos.mpr hrs
      dsimp [nodes]
      constructor
      · have : 0 ≤ (i : ℝ) * (s - r) / (L + 1 : ℝ) := by positivity
        linarith
      · have hfrac : (i : ℝ) / (L + 1 : ℝ) ≤ 1 := by
          exact (div_le_one hdenom).2 hiReal
        calc
          r + (i : ℝ) * (s - r) / (L + 1 : ℝ) =
              r + ((i : ℝ) / (L + 1 : ℝ)) * (s - r) := by ring
          _ ≤ r + 1 * (s - r) := by gcongr
          _ = s := by ring
    have hgZero : ∀ x ∈ Set.Icc r s, g x = 0 := by
      intro x hx
      have hsup : intervalSupNorm g r s ≤ 0 := by rw [hgError, hErrorZero]
      have habs := (intervalSupNorm_le_iff hg hrs.le).mp hsup x hx
      exact abs_eq_zero.mp (le_antisymm habs (abs_nonneg _))
    exact ⟨
      { approximant := Q
        approximant_degree := hQdegree
        approximant_best := hQbest
        nodes := nodes
        nodes_strictMono := hnodesMono
        nodes_mem := hnodesMem
        orientation := 1
        orientation_eq := Or.inl rfl
        equioscillation := by
          intro i
          rw [hErrorZero]
          simp only [mul_zero]
          exact hgZero (nodes i) (hnodesMem i) }⟩
  · have hErrorPos : 0 < bestUniformApproxError f r s L :=
      lt_of_le_of_ne hErrorNonneg (Ne.symm hErrorZero)
    have hAlternates : ∃ nodes orientation,
        IsAlternatingExtrema g r s L nodes orientation := by
      by_contra hno
      obtain ⟨P, hPdegree, hPsign⟩ :=
        exists_signPolynomial_of_no_alternatingExtrema hrs hg L
          (by simpa [hgError] using hErrorPos) hno
      obtain ⟨t, ht, himprove⟩ :=
        exists_strict_uniformImprovement hrs.le hg
          (by simpa [hgError] using hErrorPos) hPsign
      let R : Polynomial ℝ := Q + C t * P
      have hRdegree : R.natDegree ≤ L := by
        calc
          R.natDegree ≤ max Q.natDegree (C t * P).natDegree := by
            dsimp [R]
            exact natDegree_add_le _ _
          _ ≤ L := by
            apply max_le hQdegree
            calc
              (C t * P).natDegree ≤ (C t).natDegree + P.natDegree :=
                natDegree_mul_le
              _ ≤ L := by simpa using hPdegree
      have hResidual :
          uniformApproxError f r s R =
            intervalSupNorm (fun x ↦ g x - t * P.eval x) r s := by
        unfold uniformApproxError
        congr 2
        funext x
        simp [R, g]
        ring
      have hRlower := bestUniformApproxError_le hrs hf hRdegree
      have hRstrict : uniformApproxError f r s R <
          bestUniformApproxError f r s L := by
        rw [hResidual, ← hgError]
        exact himprove
      exact (not_lt_of_ge hRlower) hRstrict
    obtain ⟨nodes, orientation, hmono, hmem, horientation, halternates⟩ := hAlternates
    exact ⟨
      { approximant := Q
        approximant_degree := hQdegree
        approximant_best := hQbest
        nodes := nodes
        nodes_strictMono := hmono
        nodes_mem := hmem
        orientation := orientation
        orientation_eq := horientation
        equioscillation := by
          intro i
          change g (nodes i) = _
          rw [halternates i, hgError] }⟩

end CausalSmith.Substrate.FinitePolynomialAlternationDuality

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.BestApproximation
import Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.Equioscillation
import Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.LagrangeWeights

/-!
# Finite Chebyshev alternation and moment-dual certificates

This module packages the classical alternation theorem for degree-bounded
uniform approximation on a compact real interval.  The alternating extrema are
combined with normalized signed Lagrange weights to obtain a finite moment
functional that attains the best approximation error.
-/

open Polynomial Set

namespace Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

/-- An alternation dual certificate consists of a best degree-`L` approximant,
`L+2` ordered extrema of its residual, and the normalized signed Lagrange
weights on those nodes, with the exact oriented target evaluation. [the stated inputs](hyp:f,r,s,L) establish the described certificate. -/
structure AlternationDualCertificate
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
  weights : Fin (L + 2) → ℝ
  weights_eq : ∀ i, weights i = normalizedLagrangeWeight nodes i
  weights_alternate : ∀ i,
    weights i = (-1 : ℝ) ^ (L + 1 - (i : ℕ)) * |weights i|
  weights_normalized : ∑ i, |weights i| = 1
  moments_zero : ∀ j, j ≤ L → ∑ i, weights i * nodes i ^ j = 0
  target_eq :
    ∑ i, weights i * f (nodes i) =
      orientation * (-1 : ℝ) ^ (L + 1) * bestUniformApproxError f r s L

/-- Every continuous real target on a nondegenerate compact interval admits a
finite Chebyshev alternation dual certificate for degree-`L` approximation. [the stated inputs](hyp:f,r,s,hrs,hf,L) establish [the stated conclusion](goal). -/
theorem exists_alternationDualCertificate
    {f : ℝ → ℝ} {r s : ℝ} (hrs : r < s)
    (hf : ContinuousOn f (Set.Icc r s)) (L : ℕ) :
    Nonempty (AlternationDualCertificate f r s L) := by
  classical
  obtain ⟨E⟩ := exists_equioscillationWitness hrs hf L
  let w : Fin (L + 2) → ℝ := normalizedLagrangeWeight E.nodes
  have hwinj : Function.Injective E.nodes := E.nodes_strictMono.injective
  have hwalt (i : Fin (L + 2)) :
      w i = (-1 : ℝ) ^ (L + 1 - (i : ℕ)) * |w i| :=
    normalizedLagrangeWeight_alternates E.nodes_strictMono i
  have hpow (i : Fin (L + 2)) :
      (-1 : ℝ) ^ (L + 1 - (i : ℕ)) * (-1 : ℝ) ^ (i : ℕ) =
        (-1 : ℝ) ^ (L + 1) := by
    rw [← pow_add, Nat.sub_add_cancel]
    omega
  have hpoly : ∑ i, w i * E.approximant.eval (E.nodes i) = 0 :=
    sum_normalizedLagrangeWeight_mul_eval_eq_zero hwinj E.approximant_degree
  have htarget : ∑ i, w i * f (E.nodes i) =
      E.orientation * (-1 : ℝ) ^ (L + 1) * bestUniformApproxError f r s L := by
    calc
      ∑ i, w i * f (E.nodes i) =
          (∑ i, w i * (f (E.nodes i) - E.approximant.eval (E.nodes i))) +
            ∑ i, w i * E.approximant.eval (E.nodes i) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = ∑ i, w i * (f (E.nodes i) - E.approximant.eval (E.nodes i)) := by
        rw [hpoly, add_zero]
      _ = ∑ i, (E.orientation * (-1 : ℝ) ^ (L + 1) *
          bestUniformApproxError f r s L) * |w i| := by
        apply Finset.sum_congr rfl
        intro i _
        rw [E.equioscillation i]
        calc
          w i * (E.orientation * (-1 : ℝ) ^ (i : ℕ) *
              bestUniformApproxError f r s L) =
              E.orientation *
                ((-1 : ℝ) ^ (L + 1 - (i : ℕ)) * (-1 : ℝ) ^ (i : ℕ)) *
                bestUniformApproxError f r s L * |w i| := by
            conv_lhs => rw [hwalt i]
            ring
          _ = (E.orientation * (-1 : ℝ) ^ (L + 1) *
              bestUniformApproxError f r s L) * |w i| := by
            rw [hpow i]
      _ = (E.orientation * (-1 : ℝ) ^ (L + 1) *
          bestUniformApproxError f r s L) * ∑ i, |w i| := by
        rw [Finset.mul_sum]
      _ = E.orientation * (-1 : ℝ) ^ (L + 1) *
          bestUniformApproxError f r s L := by
        rw [sum_abs_normalizedLagrangeWeight_eq_one hwinj, mul_one]
  exact ⟨
    { approximant := E.approximant
      approximant_degree := E.approximant_degree
      approximant_best := E.approximant_best
      nodes := E.nodes
      nodes_strictMono := E.nodes_strictMono
      nodes_mem := E.nodes_mem
      orientation := E.orientation
      orientation_eq := E.orientation_eq
      equioscillation := E.equioscillation
      weights := w
      weights_eq := fun _ ↦ rfl
      weights_alternate := hwalt
      weights_normalized := sum_abs_normalizedLagrangeWeight_eq_one hwinj
      moments_zero := fun _ hj ↦
        sum_normalizedLagrangeWeight_mul_pow_eq_zero hwinj hj
      target_eq := htarget }⟩

/-- A finite moment dual packages `L+2` ordered interval nodes and normalized
signed weights that annihilate moments through degree `L` and separate the
target by exactly its best uniform approximation error. [the stated inputs](hyp:f,r,s,L) establish the described certificate. -/
structure FiniteMomentDual (f : ℝ → ℝ) (r s : ℝ) (L : ℕ) where
  nodes : Fin (L + 2) → ℝ
  nodes_strictMono : StrictMono nodes
  nodes_mem : ∀ i, nodes i ∈ Set.Icc r s
  weights : Fin (L + 2) → ℝ
  weights_normalized : ∑ i, |weights i| = 1
  moments_zero : ∀ j, j ≤ L → ∑ i, weights i * nodes i ^ j = 0
  target_abs_eq :
    |∑ i, weights i * f (nodes i)| = bestUniformApproxError f r s L

/-- Forgetting the best approximant and orientation from an alternation
certificate yields the paper-independent finite moment-dual package. [the stated inputs](hyp:f,r,s,L,A) establish [the defined object](goal). -/
noncomputable def AlternationDualCertificate.toFiniteMomentDual
    {f : ℝ → ℝ} {r s : ℝ} {L : ℕ}
    (A : AlternationDualCertificate f r s L) : FiniteMomentDual f r s L := by
  have hrs : r ≤ s :=
    (A.nodes_mem (0 : Fin (L + 2))).1.trans
      (A.nodes_mem (0 : Fin (L + 2))).2
  have hE : 0 ≤ bestUniformApproxError f r s L := by
    rw [← A.approximant_best]
    exact uniformApproxError_nonneg hrs A.approximant
  refine
    { nodes := A.nodes
      nodes_strictMono := A.nodes_strictMono
      nodes_mem := A.nodes_mem
      weights := A.weights
      weights_normalized := A.weights_normalized
      moments_zero := A.moments_zero
      target_abs_eq := ?_ }
  rw [A.target_eq]
  rcases A.orientation_eq with h | h <;> rw [h] <;>
    simp [abs_mul, abs_of_nonneg hE]

/-- Every continuous real target on a nondegenerate compact interval admits
`L+2` ordered, normalized finite weights annihilating moments through degree
`L` and attaining the best approximation error in absolute value. [the stated inputs](hyp:f,r,s,hrs,hf,L) establish [the stated conclusion](goal). -/
theorem exists_finiteMomentDual
    {f : ℝ → ℝ} {r s : ℝ} (hrs : r < s)
    (hf : ContinuousOn f (Set.Icc r s)) (L : ℕ) :
    Nonempty (FiniteMomentDual f r s L) := by
  exact Nonempty.map AlternationDualCertificate.toFiniteMomentDual
    (exists_alternationDualCertificate hrs hf L)

end Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Basic
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Equioscillation
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Finite Chebyshev alternation and moment-dual certificates

This module constructs normalized signed Lagrange weights, packages the classical
alternation theorem as finite moment-dual certificates, and specializes the
construction to pole-separated rational targets.
-/

@[expose] public section

open Polynomial Set

namespace Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

/-! ## Normalized signed Lagrange weights -/


/-- The normalized signed Lagrange weight at a node is its barycentric nodal
weight divided by the sum of the absolute barycentric weights.
[The inputs](hyp:n,nodes,i) determine [this weight](goal). -/
noncomputable def normalizedLagrangeWeight {n : ℕ}
    (nodes : Fin n → ℝ) (i : Fin n) : ℝ :=
  Lagrange.nodalWeight Finset.univ nodes i /
    ∑ k : Fin n, |Lagrange.nodalWeight Finset.univ nodes k|

/-- For `L+2` distinct real nodes, the normalized signed Lagrange weights have
total absolute mass one. [The inputs](hyp:L,nodes,hnodes) imply [this normalization](goal). -/
theorem sum_abs_normalizedLagrangeWeight_eq_one
    {L : ℕ} {nodes : Fin (L + 2) → ℝ} (hnodes : Function.Injective nodes) :
    ∑ i, |normalizedLagrangeWeight nodes i| = 1 := by
  classical
  let Z := ∑ k : Fin (L + 2), |Lagrange.nodalWeight Finset.univ nodes k|
  have hweight : Lagrange.nodalWeight Finset.univ nodes (0 : Fin (L + 2)) ≠ 0 :=
    Lagrange.nodalWeight_ne_zero hnodes.injOn (Finset.mem_univ _)
  have hZ : 0 < Z := by
    apply Finset.sum_pos'
    · exact fun k _ ↦ abs_nonneg _
    · exact ⟨0, Finset.mem_univ _, abs_pos.mpr hweight⟩
  change ∑ i, |Lagrange.nodalWeight Finset.univ nodes i / Z| = 1
  simp_rw [abs_div, abs_of_pos hZ]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  exact mul_inv_cancel₀ (ne_of_gt hZ)

/-- For `L+2` strictly increasing real nodes, the normalized Lagrange weight
at index `i` has sign `(-1)^(L+1-i)`. [The inputs](hyp:L,nodes,hnodes,i) imply
[this alternating-sign identity](goal). -/
theorem normalizedLagrangeWeight_alternates
    {L : ℕ} {nodes : Fin (L + 2) → ℝ} (hnodes : StrictMono nodes)
    (i : Fin (L + 2)) :
    normalizedLagrangeWeight nodes i =
      (-1 : ℝ) ^ (L + 1 - (i : ℕ)) * |normalizedLagrangeWeight nodes i| := by
  classical
  have hfactor (k : Fin (L + 2))
      (hk : k ∈ (Finset.univ : Finset (Fin (L + 2))).erase i) :
      (nodes i - nodes k)⁻¹ =
        (if i < k then (-1 : ℝ) else 1) * |(nodes i - nodes k)⁻¹| := by
    by_cases hik : i < k
    · rw [if_pos hik, abs_of_neg]
      · ring
      · exact inv_neg''.mpr (sub_neg.mpr (hnodes hik))
    · rw [if_neg hik, one_mul, abs_of_pos]
      have hki : k < i :=
        lt_of_le_of_ne (le_of_not_gt hik) (Finset.ne_of_mem_erase hk)
      exact inv_pos.mpr (sub_pos.mpr (hnodes hki))
  have hsign :
      (∏ k ∈ (Finset.univ : Finset (Fin (L + 2))).erase i,
        if i < k then (-1 : ℝ) else 1) =
          (-1 : ℝ) ^ (L + 1 - (i : ℕ)) := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const, one_pow, mul_one]
    have hfilter :
        ((Finset.univ : Finset (Fin (L + 2))).erase i).filter (fun k ↦ i < k) =
          Finset.Ioi i := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
        Finset.mem_Ioi]
      constructor
      · exact fun h ↦ h.2
      · exact fun h ↦ ⟨⟨ne_of_gt h, trivial⟩, h⟩
    rw [hfilter, Fin.card_Ioi]
    rw [show L + 2 - 1 - (i : ℕ) = L + 1 - (i : ℕ) by omega]
  have hweight :
      Lagrange.nodalWeight Finset.univ nodes i =
        (-1 : ℝ) ^ (L + 1 - (i : ℕ)) *
          |Lagrange.nodalWeight Finset.univ nodes i| := by
    rw [Lagrange.nodalWeight]
    calc
      (∏ k ∈ Finset.univ.erase i, (nodes i - nodes k)⁻¹) =
          ∏ k ∈ Finset.univ.erase i,
            ((if i < k then (-1 : ℝ) else 1) * |(nodes i - nodes k)⁻¹|) := by
              apply Finset.prod_congr rfl
              intro k hk
              exact hfactor k hk
      _ = (∏ k ∈ Finset.univ.erase i, if i < k then (-1 : ℝ) else 1) *
          (∏ k ∈ Finset.univ.erase i, |(nodes i - nodes k)⁻¹|) := by
            rw [Finset.prod_mul_distrib]
      _ = (-1 : ℝ) ^ (L + 1 - (i : ℕ)) *
          |∏ k ∈ Finset.univ.erase i, (nodes i - nodes k)⁻¹| := by
            rw [hsign, Finset.abs_prod]
  let Z := ∑ k : Fin (L + 2), |Lagrange.nodalWeight Finset.univ nodes k|
  have hnodeInjective : Function.Injective nodes := hnodes.injective
  have hweight_ne : Lagrange.nodalWeight Finset.univ nodes i ≠ 0 :=
    Lagrange.nodalWeight_ne_zero hnodeInjective.injOn (Finset.mem_univ _)
  have hZ : 0 < Z := by
    apply Finset.sum_pos'
    · exact fun k _ ↦ abs_nonneg _
    · exact ⟨i, Finset.mem_univ _, abs_pos.mpr hweight_ne⟩
  change Lagrange.nodalWeight Finset.univ nodes i / Z =
    (-1 : ℝ) ^ (L + 1 - (i : ℕ)) *
      |Lagrange.nodalWeight Finset.univ nodes i / Z|
  rw [abs_div, abs_of_pos hZ]
  nth_rewrite 1 [hweight]
  ring

/-- For `L+2` distinct real nodes, the normalized signed Lagrange weights
annihilate the monomial `x^j` whenever `j ≤ L`.
[The inputs](hyp:L,j,nodes,hnodes,hj) imply [this vanishing moment](goal). -/
theorem sum_normalizedLagrangeWeight_mul_pow_eq_zero
    {L j : ℕ} {nodes : Fin (L + 2) → ℝ}
    (hnodes : Function.Injective nodes) (hj : j ≤ L) :
    ∑ i, normalizedLagrangeWeight nodes i * nodes i ^ j = 0 := by
  classical
  let Z := ∑ k : Fin (L + 2), |Lagrange.nodalWeight Finset.univ nodes k|
  have hdegree : (X ^ j : Polynomial ℝ).degree <
      (Finset.univ : Finset (Fin (L + 2))).card := by
    rw [degree_X_pow]
    norm_cast
    simpa using (show j < L + 2 by omega)
  have hcoeff := Lagrange.coeff_eq_sum
    (s := (Finset.univ : Finset (Fin (L + 2)))) (v := nodes)
    hnodes.injOn (P := (X ^ j : Polynomial ℝ)) hdegree
  have hsum : ∑ i : Fin (L + 2),
      Lagrange.nodalWeight Finset.univ nodes i * nodes i ^ j = 0 := by
    simpa [Lagrange.nodalWeight, div_eq_mul_inv, Finset.prod_inv_distrib,
      mul_comm, ne_of_gt (lt_of_le_of_lt hj (Nat.lt_succ_self L))] using hcoeff.symm
  change ∑ i : Fin (L + 2),
    (Lagrange.nodalWeight Finset.univ nodes i / Z) * nodes i ^ j = 0
  simp_rw [div_mul_eq_mul_div, div_eq_mul_inv]
  rw [← Finset.sum_mul, hsum, zero_mul]

/-- For `L+2` distinct real nodes, the normalized signed Lagrange weights
annihilate the values of every real polynomial of degree at most `L`.
[The inputs](hyp:L,nodes,hnodes,Q,hQ) imply [this weighted cancellation](goal). -/
theorem sum_normalizedLagrangeWeight_mul_eval_eq_zero
    {L : ℕ} {nodes : Fin (L + 2) → ℝ}
    (hnodes : Function.Injective nodes) {Q : Polynomial ℝ}
    (hQ : Q.natDegree ≤ L) :
    ∑ i, normalizedLagrangeWeight nodes i * Q.eval (nodes i) = 0 := by
  classical
  let Z := ∑ k : Fin (L + 2), |Lagrange.nodalWeight Finset.univ nodes k|
  have hdegree : Q.degree < (Finset.univ : Finset (Fin (L + 2))).card := by
    apply lt_of_le_of_lt Q.degree_le_natDegree
    norm_cast
    simpa using (show Q.natDegree < L + 2 by omega)
  have hcoeff := Lagrange.coeff_eq_sum
    (s := (Finset.univ : Finset (Fin (L + 2)))) (v := nodes)
    hnodes.injOn (P := Q) hdegree
  have hcoeffzero : Q.coeff (L + 1) = 0 :=
    Q.coeff_eq_zero_of_natDegree_lt (by omega)
  have hsum : ∑ i : Fin (L + 2),
      Lagrange.nodalWeight Finset.univ nodes i * Q.eval (nodes i) = 0 := by
    simpa [Lagrange.nodalWeight, div_eq_mul_inv, Finset.prod_inv_distrib,
      mul_comm, hcoeffzero] using hcoeff.symm
  change ∑ i : Fin (L + 2),
    (Lagrange.nodalWeight Finset.univ nodes i / Z) * Q.eval (nodes i) = 0
  simp_rw [div_mul_eq_mul_div, div_eq_mul_inv]
  rw [← Finset.sum_mul, hsum, zero_mul]

/-! ## Alternation and finite moment duality -/


/-- An alternation dual certificate for [a target on an interval at a chosen
degree](hyp:f,r,s,L) records
[a best polynomial](hyp:approximant,approximant_degree,approximant_best),
[ordered interval nodes](hyp:nodes,nodes_strictMono,nodes_mem), [an alternating residual
orientation](hyp:orientation,orientation_eq,equioscillation), [the associated Lagrange
weights](hyp:weights,weights_eq), and the facts that those weights [alternate and are
normalized](hyp:weights_alternate,weights_normalized), [annihilate all relevant
moments](hyp:moments_zero), and give [the exact oriented target evaluation](hyp:target_eq). -/
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
finite Chebyshev alternation dual certificate for degree-`L` approximation.
[The inputs](hyp:f,r,s,hrs,hf,L) guarantee [such a certificate](goal). -/
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

/-- A finite moment dual certificate for [a target on an interval at a chosen
degree](hyp:f,r,s,L) records [strictly ordered nodes in the
interval](hyp:nodes,nodes_strictMono,nodes_mem) and [normalized signed weights that annihilate
moments through that degree and separate the target by exactly its best uniform approximation
error](hyp:weights,weights_normalized,moments_zero,target_abs_eq). -/
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
certificate yields the paper-independent finite moment-dual package.
[The inputs](hyp:f,r,s,L,A) determine [that package](goal). -/
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
`L` and attaining the best approximation error in absolute value.
[The inputs](hyp:f,r,s,hrs,hf,L) guarantee [such weights](goal). -/
theorem exists_finiteMomentDual
    {f : ℝ → ℝ} {r s : ℝ} (hrs : r < s)
    (hf : ContinuousOn f (Set.Icc r s)) (L : ℕ) :
    Nonempty (FiniteMomentDual f r s L) := by
  exact Nonempty.map AlternationDualCertificate.toFiniteMomentDual
    (exists_alternationDualCertificate hrs hf L)

/-! ## Pole-separated rational targets -/


/-- The rational target with parameter `a` is the function `x ↦ x/(x+a)`.
[The inputs](hyp:a,x) determine [its value](goal). -/
noncomputable def rationalTarget (a : ℝ) (x : ℝ) : ℝ := x / (x + a)

/-- If the pole `-a` is outside a closed interval, the rational target
`x ↦ x/(x+a)` is continuous on that interval.
[The inputs](hyp:a,r,s,hpole) imply [this continuity](goal). -/
theorem continuousOn_rationalTarget {a r s : ℝ}
    (hpole : -a ∉ Set.Icc r s) :
    ContinuousOn (rationalTarget a) (Set.Icc r s) := by
  unfold rationalTarget
  apply continuousOn_id.div (continuousOn_id.add continuousOn_const)
  intro x hx hzero
  apply hpole
  change x + a = 0 at hzero
  have hxa : x = -a := by linarith
  simpa [hxa] using hx

/-- On a nondegenerate interval avoiding `-a`, there are `L+2` ordered,
normalized finite weights that match moments through degree `L` and whose
rational-target separation is the exact best degree-`L` uniform error.
[The inputs](hyp:a,r,s,hrs,hpole,L) guarantee [such a certificate](goal). -/
theorem exists_rationalFiniteMomentDual
    {a r s : ℝ} (hrs : r < s) (hpole : -a ∉ Set.Icc r s) (L : ℕ) :
    Nonempty (FiniteMomentDual (rationalTarget a) r s L) := by
  exact exists_finiteMomentDual hrs (continuousOn_rationalTarget hpole) L

end Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

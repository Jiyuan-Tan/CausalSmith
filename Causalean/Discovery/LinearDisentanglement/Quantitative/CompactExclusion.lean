/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Discovery.LinearDisentanglement.Quantitative.Definitions
import Causalean.Mathlib.Topology.CompactExclusion

/-!
# Compact exclusion for simultaneous congruence

This module specializes the generic compact-exclusion API of
`Causalean.Mathlib.Topology.CompactExclusion` to real square matrices.  It shows that the
simultaneous-congruence residual is continuous, so on a compact candidate set whose only
zero-residual candidate is a reference matrix, the residual has a strictly positive attained
minimum outside any open neighborhood of the reference.  It also restates the uniform
compact-correspondence dichotomy and residual tolerance for parameter-matrix correspondences, with
distance measured by the Euclidean operator norm.
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace Causalean.Discovery.LinearDisentanglement.Quantitative

open Causalean.Mathlib.Topology.CompactExclusion

/-- For [a finite real matrix family](hyp:A) and [its prescribed diagonal shifts](hyp:s),
[the simultaneous-congruence residual is continuous as a function of the candidate
matrix](goal). -/
-- Proof route: matrix multiplication, transpose, subtraction, diagonal constants, and
-- the norm are continuous in finite dimension; close under the finite nonempty `sup'`.
theorem continuous_simultaneousCongruenceResidual {d : ℕ} {E : Type*}
    [Fintype E] [Nonempty E]
    (A : E → SqMatrix d) (s : E → Fin d → ℝ) :
    Continuous (simultaneousCongruenceResidual A s) := by
  classical
  unfold simultaneousCongruenceResidual
  have h : Continuous
      (Finset.univ.sup' Finset.univ_nonempty
        (fun e B => ‖congruenceDefect (A e) (s e) B‖)) := by
    apply Continuous.finset_sup' Finset.univ_nonempty
    intro e _
    apply Continuous.norm
    unfold congruenceDefect
    fun_prop
  rw [show (fun B => Finset.univ.sup' Finset.univ_nonempty
      (fun e => ‖congruenceDefect (A e) (s e) B‖)) =
      Finset.univ.sup' Finset.univ_nonempty
        (fun e B => ‖congruenceDefect (A e) (s e) B‖) by
    funext B
    exact (Finset.sup'_apply Finset.univ_nonempty
      (fun e B => ‖congruenceDefect (A e) (s e) B‖) B).symm]
  exact h

/-- For [a finite nonempty real matrix family](hyp:A), [its diagonal shifts](hyp:s), [a
candidate set of matrices](hyp:K), [an open local chart](hyp:U), and [a reference matrix](hyp:B₀),
if [the candidate set is compact](hyp:hK), [the chart is open](hyp:hU), [the reference is a
candidate](hyp:hB₀K), [the reference lies in the chart](hyp:hB₀U), [the far candidates are
nonempty](hyp:hfar), and [only the reference has zero residual among candidates](hyp:hzero),
then [the far candidates have a strictly positive attained simultaneous-congruence residual
minimum](goal). -/
theorem exists_simultaneousCongruence_exclusionRadius {d : ℕ} {E : Type*}
    [Fintype E] [Nonempty E]
    (A : E → SqMatrix d) (s : E → Fin d → ℝ)
    (K U : Set (SqMatrix d)) (B₀ : SqMatrix d)
    (hK : IsCompact K) (hU : IsOpen U) (hB₀K : B₀ ∈ K) (hB₀U : B₀ ∈ U)
    (hfar : (K \ U).Nonempty)
    (hzero : ∀ B ∈ K, simultaneousCongruenceResidual A s B = 0 → B = B₀) :
    Nonempty (PositiveExclusionRadius K U (simultaneousCongruenceResidual A s)) := by
  exact exists_positiveExclusionRadius K U
    (simultaneousCongruenceResidual A s) B₀
    hK hU hB₀K hB₀U hfar
    (continuous_simultaneousCongruenceResidual A s)
    (fun B _ => simultaneousCongruenceResidual_nonneg A s B)
    hzero

/-- Given [a parameter-matrix correspondence](hyp:K), [a reference matrix section](hyp:B₀),
[a residual](hyp:r), and [a radius function](hyp:ρ), if [the correspondence is compact](hyp:hK),
[the reference matrix section is continuous](hyp:hB₀), [the residual is continuous](hyp:hr_cont),
[the radius function is continuous](hyp:hρ_cont), [every radius is strictly positive](hyp:hρ_pos),
[the residual is nonnegative on feasible pairs](hyp:hr_nonneg), and
[only the reference matrix has zero residual among feasible pairs](hyp:hr_zero), then
[either no operator-norm-far pair exists or one attains a strictly positive uniform residual
minimum](goal). -/
theorem sqMatrix_uniformCompactCorrespondence_dichotomy
    {P : Type*} [TopologicalSpace P] [T2Space P] {d : ℕ}
    (K : Set (P × SqMatrix d)) (B₀ : P → SqMatrix d)
    (r : P × SqMatrix d → ℝ) (ρ : P → ℝ)
    (hK : IsCompact K) (hB₀ : Continuous B₀) (hr_cont : Continuous r)
    (hρ_cont : Continuous ρ) (hρ_pos : ∀ p, 0 < ρ p)
    (hr_nonneg : ∀ z ∈ K, 0 ≤ r z)
    (hr_zero : ∀ p B, (p, B) ∈ K → r (p, B) = 0 → B = B₀ p) :
    farFeasibleSet K B₀ ρ = ∅ ∨
      Nonempty (UniformPositiveExclusionRadius K B₀ ρ r) := by
  exact uniformCompactCorrespondence_dichotomy K B₀ r ρ hK hB₀ hr_cont hρ_cont hρ_pos
    hr_nonneg hr_zero

/-- Given [a parameter-matrix correspondence](hyp:K), [a reference matrix section](hyp:B₀),
[a residual](hyp:r), and [a radius function](hyp:ρ), if [the correspondence is compact](hyp:hK),
[the reference matrix section is continuous](hyp:hB₀), [the residual is continuous](hyp:hr_cont),
[the radius function is continuous](hyp:hρ_cont), [every radius is strictly positive](hyp:hρ_pos),
[the residual is nonnegative on feasible pairs](hyp:hr_nonneg), and
[only the reference matrix has zero residual among feasible pairs](hyp:hr_zero), then
[one positive residual tolerance puts every feasible pair at or below it strictly inside its
parameter-dependent Euclidean operator-norm reference ball](goal). -/
theorem exists_sqMatrix_uniformExclusionTolerance
    {P : Type*} [TopologicalSpace P] [T2Space P] {d : ℕ}
    (K : Set (P × SqMatrix d)) (B₀ : P → SqMatrix d)
    (r : P × SqMatrix d → ℝ) (ρ : P → ℝ)
    (hK : IsCompact K) (hB₀ : Continuous B₀) (hr_cont : Continuous r)
    (hρ_cont : Continuous ρ) (hρ_pos : ∀ p, 0 < ρ p)
    (hr_nonneg : ∀ z ∈ K, 0 ≤ r z)
    (hr_zero : ∀ p B, (p, B) ∈ K → r (p, B) = 0 → B = B₀ p) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ p B, (p, B) ∈ K → r (p, B) ≤ ε₀ →
      ‖B - B₀ p‖ < ρ p := by
  simpa only [dist_eq_norm] using
    (exists_uniformExclusionTolerance_le K B₀ r ρ hK hB₀ hr_cont hρ_cont hρ_pos
      hr_nonneg hr_zero)

end Causalean.Discovery.LinearDisentanglement.Quantitative

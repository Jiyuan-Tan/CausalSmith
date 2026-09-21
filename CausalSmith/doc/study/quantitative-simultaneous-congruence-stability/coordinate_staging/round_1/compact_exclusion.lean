/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Discovery.LinearDisentanglement.Quantitative.Definitions

/-!
# Compact exclusion away from an isolated exact solution

This module packages the non-effective compactness argument used after a local quantitative
estimate: a continuous nonnegative residual with a unique zero on a compact normalized
candidate set has a strictly positive, attained minimum outside any open neighborhood of
that zero, provided the outside set is nonempty.
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace Causalean.Discovery.LinearDisentanglement.Quantitative

/-- A positive exclusion radius is a positive lower bound for a residual on the part of
`K` outside `U`, together with a candidate where that lower bound is attained. -/
structure PositiveExclusionRadius {X : Type*} (K U : Set X) (r : X → ℝ) where
  /-- The strictly positive residual radius. -/
  radius : ℝ
  /-- The exclusion radius is strictly positive. -/
  radius_pos : 0 < radius
  /-- Every candidate in `K` outside `U` has residual at least the radius. -/
  lower_bound : ∀ x, x ∈ K → x ∉ U → radius ≤ r x
  /-- Some candidate in `K` outside `U` attains the radius. -/
  attained : ∃ x, x ∈ K ∧ x ∉ U ∧ r x = radius

/-- For [a compact candidate set](hyp:K), [an open local neighborhood](hyp:U), [a continuous
residual](hyp:r), and [a reference point](hyp:x₀), if [the candidate set is compact](hyp:hK),
[the neighborhood is open](hyp:hU), [the reference belongs to the candidate set](hyp:hxK),
[the reference belongs to the neighborhood](hyp:hxU), [the far set is nonempty](hyp:hfar),
[the residual is continuous](hyp:hr_cont), [the residual is nonnegative on candidates](hyp:hr_nonneg),
and [its only zero among candidates is the reference](hyp:hr_zero), then [the far set has a
strictly positive attained residual minimum](goal). -/
-- Proof route: `K \ U = K ∩ Uᶜ` is compact.  Apply `IsCompact.exists_isMinOn` to `r`
-- on this nonempty far set.  Nonnegativity makes the minimum nonnegative; equality to
-- zero forces its minimizer to be `x₀`, contradicting `x₀ ∈ U`.
theorem exists_positiveExclusionRadius {X : Type*} [TopologicalSpace X]
    (K U : Set X) (r : X → ℝ) (x₀ : X)
    (hK : IsCompact K) (hU : IsOpen U) (hxK : x₀ ∈ K) (hxU : x₀ ∈ U)
    (hfar : (K \ U).Nonempty) (hr_cont : Continuous r)
    (hr_nonneg : ∀ x ∈ K, 0 ≤ r x)
    (hr_zero : ∀ x ∈ K, r x = 0 → x = x₀) :
    Nonempty (PositiveExclusionRadius K U r) := by
  have hcompact : IsCompact (K \ U) := by
    rw [Set.sdiff_eq]
    exact hK.inter_right hU.isClosed_compl
  obtain ⟨x, hx, hmin⟩ :=
    hcompact.exists_isMinOn hfar hr_cont.continuousOn
  have hxK' : x ∈ K := hx.1
  have hxU' : x ∉ U := hx.2
  have hnonneg : 0 ≤ r x := hr_nonneg x hxK'
  have hpos : 0 < r x := lt_of_le_of_ne hnonneg fun hzero => by
    have heq : x = x₀ := hr_zero x hxK' hzero.symm
    exact hxU' (heq ▸ hxU)
  exact ⟨{
    radius := r x
    radius_pos := hpos
    lower_bound := by
      intro y hyK hyU
      exact hmin ⟨hyK, hyU⟩
    attained := ⟨x, hxK', hxU', rfl⟩
  }⟩

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

/-- For [a finite real matrix family](hyp:A), [its diagonal shifts](hyp:s), [a compact
normalized candidate set](hyp:K), [an open local chart](hyp:U), and [a reference matrix](hyp:B₀),
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

end Causalean.Discovery.LinearDisentanglement.Quantitative

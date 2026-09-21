/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Discovery.LinearDisentanglement.CollinearAmbiguity.SmallParameter
import Mathlib.Algebra.Order.Star.Real

/-!
# Constructive ambiguity from an affine-collinear shift pair

This module gives a paper-independent non-identifiability witness for a finite family of
positive-definite covariance matrices.  If two selected coordinates of all diagonal
shifts lie on one affine line, an arbitrarily small nonzero normalized two-row
deformation produces a distinct invertible diagonalizer and a second exact
positive-definite/nonnegative representation of the same family.
-/

noncomputable section

open scoped Matrix

namespace Causalean.Discovery.LinearDisentanglement.CollinearAmbiguity

open Causalean.Discovery.LinearDisentanglement.Quantitative

/-- Given [two distinct selected coordinates](hyp:hij), [a unit-diagonal reference
diagonalizer](hyp:hdiag), [its invertibility](hyp:hunit), [an admissible selected
two-cycle](hyp:hcycle), [a positive-definite invariant](hyp:hΩ), [coordinatewise
nonnegative shifts](hyp:hs), and [a positive parameter bound](hyp:hr), [an
affine-collinearity certificate produces a distinct normalized invertible diagonalizer, a
symmetric positive-definite invariant, and nonnegative shifts representing the identical
finite covariance family](goal). -/
theorem exists_collinear_simultaneous_congruence_ambiguity
    {d : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (B₀ Ω₀ : SqMatrix d) (s : E → Fin d → ℝ) {i j : Fin d}
    (hij : i ≠ j) (hdiag : UnitDiagonal B₀) (hunit : IsUnit B₀.det)
    (hcycle : PairCycleAdmissible B₀ i j) (hΩ : Ω₀.PosDef)
    (hs : ∀ e k, 0 ≤ s e k) (cert : AffineLineCertificate s i j)
    {r : ℝ} (hr : 0 < r) :
    ∃ (t : ℝ) (B₁ Ω₁ : SqMatrix d) (s₁ : E → Fin d → ℝ),
      0 < |t| ∧ |t| < r ∧
      B₁ = deformedDiagonalizer B₀ i j cert.u cert.v t ∧
      Ω₁ = deformedInvariant B₀ Ω₀ i j cert.u cert.v cert.c t ∧
      s₁ = (fun e ↦ deformedShift B₀ i j cert.u cert.v t (s e)) ∧
      UnitDiagonal B₁ ∧ IsUnit B₁.det ∧ PairCycleAdmissible B₁ i j ∧
      B₁ ≠ B₀ ∧ Ω₁.IsSymm ∧ Ω₁.PosDef ∧
      (∀ e k, 0 ≤ s₁ e k) ∧
      (∀ e, (representedCovariance B₀ Ω₀ (s e)).PosDef) ∧
      ∀ e,
        representedCovariance B₁ Ω₁ (s₁ e) =
          representedCovariance B₀ Ω₀ (s e) := by
  rcases exists_small_admissible_parameter B₀ Ω₀ hij hdiag hunit hcycle hΩ
      s cert hs hr with
    ⟨t, ht0, htr, _hfirst, _hsecond, _hdet, hTunit, hB₁unit,
      hB₁diag, hB₁cycle, hB₁ne, hΩ₁pos, hs₁⟩
  refine ⟨t,
    deformedDiagonalizer B₀ i j cert.u cert.v t,
    deformedInvariant B₀ Ω₀ i j cert.u cert.v cert.c t,
    (fun e ↦ deformedShift B₀ i j cert.u cert.v t (s e)),
    ht0, htr, rfl, rfl, rfl, hB₁diag, hB₁unit, hB₁cycle, hB₁ne, ?_,
    hΩ₁pos, hs₁, ?_, ?_⟩
  · have hΩsymm : Ω₀.IsSymm := by
      rw [← Matrix.isHermitian_iff_isSymm]
      exact hΩ.isHermitian
    exact deformedInvariant_isSymm B₀ Ω₀ hij hΩsymm
      cert.u cert.v cert.c t
  · intro e
    exact representedCovariance_posDef B₀ Ω₀ (s e) hunit hΩ (hs e)
  · intro e
    exact representedCovariance_deformation_eq B₀ Ω₀ hij s cert t e hunit hTunit

/-- Given [two distinct selected coordinates](hyp:hij) and [coordinatewise nonnegative
shifts](hyp:hs), [the prescribed affine-collinear shift family has a positive-definite
interior covariance example with two distinct compatible normalized diagonalizers](goal). -/
theorem exists_interior_collinear_ambiguity_example
    {d : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (s : E → Fin d → ℝ) {i j : Fin d} (hij : i ≠ j)
    (hs : ∀ e k, 0 ≤ s e k) (cert : AffineLineCertificate s i j) :
    ∃ (Sigma : E → SqMatrix d) (B₀ B₁ Ω₀ Ω₁ : SqMatrix d)
        (s₁ : E → Fin d → ℝ),
      B₀ = 1 ∧ Ω₀ = 1 ∧
      UnitDiagonal B₀ ∧ IsUnit B₀.det ∧ PairCycleAdmissible B₀ i j ∧
      UnitDiagonal B₁ ∧ IsUnit B₁.det ∧ PairCycleAdmissible B₁ i j ∧
      B₁ ≠ B₀ ∧ Ω₀.PosDef ∧ Ω₁.IsSymm ∧ Ω₁.PosDef ∧
      (∀ e k, 0 ≤ s₁ e k) ∧
      (∀ e, (Sigma e).PosDef) ∧
      RepresentsCovarianceFamily Sigma B₀ Ω₀ s ∧
      RepresentsCovarianceFamily Sigma B₁ Ω₁ s₁ := by
  have hdiag₀ : UnitDiagonal (1 : SqMatrix d) := by
    intro k
    simp
  have hunit₀ : IsUnit (1 : SqMatrix d).det := by
    simp
  have hcycle₀ : PairCycleAdmissible (1 : SqMatrix d) i j := by
    simp [PairCycleAdmissible, hij]
  have hΩ₀ : (1 : SqMatrix d).PosDef := Matrix.PosDef.one
  rcases exists_collinear_simultaneous_congruence_ambiguity
      (1 : SqMatrix d) (1 : SqMatrix d) s hij hdiag₀ hunit₀ hcycle₀ hΩ₀
      hs cert (r := 1) (by norm_num) with
    ⟨t, B₁, Ω₁, s₁, _ht0, _htr, _hB₁eq, _hΩ₁eq, _hs₁eq,
      hB₁diag, hB₁unit, hB₁cycle, hB₁ne, hΩ₁symm, hΩ₁pos,
      hs₁, hSigmaPos, hrepEq⟩
  refine ⟨(fun e ↦ representedCovariance (1 : SqMatrix d) (1 : SqMatrix d) (s e)),
    1, B₁, 1, Ω₁, s₁, rfl, rfl, hdiag₀, hunit₀, hcycle₀,
    hB₁diag, hB₁unit, hB₁cycle, hB₁ne, hΩ₀, hΩ₁symm, hΩ₁pos,
    hs₁, hSigmaPos, ?_, ?_⟩
  · intro e
    rfl
  · intro e
    exact (hrepEq e).symm

end Causalean.Discovery.LinearDisentanglement.CollinearAmbiguity

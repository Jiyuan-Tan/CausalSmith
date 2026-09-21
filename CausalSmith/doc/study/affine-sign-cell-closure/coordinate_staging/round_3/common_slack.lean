/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Optimization.AffineSignCellClosure.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! # Common-slack strict feasibility

This module gives the bounded Phase-I common-slack characterization of strict feasibility:
one positive margin is shared by all strict affine inequalities, while weak inequalities stay
weak.
-/

open Set

namespace Causalean.Mathlib.Optimization.AffineSignCellClosure

/-- Given [an affine constraint system](hyp:Γ), [a coordinate vector](hyp:x), and [a real
slack](hyp:δ), the [common-slack feasibility condition](goal) is given by [the slack lying
between zero and one](step:1), [the slack being at most one](step:2), and [weak constraints
remaining at zero while strict constraints are at most the negative slack](step:3).

A point and slack satisfy the bounded common-slack formulation. -/
def commonSlackFeasible {n : ℕ} (Γ : AffineSystem n) (x : Fin n → ℝ) (δ : ℝ) : Prop :=
  0 ≤ δ ∧ δ ≤ 1 ∧ ∀ c ∈ Γ,
    c.fn.eval x ≤ match c.kind with | .weak => 0 | .strict => -δ

/-- Given [an affine constraint system](hyp:Γ), its [feasible slack set](goal) is given by
[the slacks for which some coordinate vector is common-slack feasible](step:1).

The set of feasible common-slack values. -/
def commonSlackSet {n : ℕ} (Γ : AffineSystem n) : Set ℝ :=
  {δ | ∃ x, commonSlackFeasible Γ x δ}

/-- Given [an affine constraint system](hyp:Γ), its [common-slack value](goal) is given by
[the supremum of its feasible slack set](step:1).

The Phase-I common-slack value. -/
noncomputable def commonSlackValue {n : ℕ} (Γ : AffineSystem n) : ℝ :=
  sSup (commonSlackSet Γ)

/-- Given [an affine constraint system](hyp:Γ), [its feasible slack set is bounded above](goal). -/
theorem bddAbove_commonSlackSet {n : ℕ} (Γ : AffineSystem n) :
    BddAbove (commonSlackSet Γ) := by
  refine ⟨1, ?_⟩
  intro δ hδ
  rcases hδ with ⟨x, hx⟩
  exact hx.2.1

/-- Given [a strictly feasible point](hyp:hx), [there is a positive common slack for that
same point](goal). -/
theorem positiveSlackWitness_of_strictPoint {n : ℕ} {Γ : AffineSystem n}
    {x : Fin n → ℝ} (hx : x ∈ strictCell Γ) :
    ∃ δ : ℝ, 0 < δ ∧ commonSlackFeasible Γ x δ := by
  induction Γ with
  | nil =>
      refine ⟨1, by norm_num, ?_⟩
      simp [commonSlackFeasible]
  | cons c Γ ih =>
      have hc : c.strictHolds x := hx c (by simp)
      have hΓ : x ∈ strictCell Γ := by
        intro d hd
        exact hx d (by simp [hd])
      rcases ih hΓ with ⟨δ, hδ, hfeas⟩
      rcases hfeas with ⟨hδ0, hδ1, htail⟩
      cases hk : c.kind with
      | weak =>
          refine ⟨δ, hδ, hδ0, hδ1, ?_⟩
          intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · simpa [Constraint.strictHolds, hk] using hc
          · exact htail d hd
      | strict =>
          let ε := min δ (-c.fn.eval x)
          have hneg : 0 < -c.fn.eval x := by
            have hc' : c.fn.eval x < 0 := by simpa [Constraint.strictHolds, hk] using hc
            exact neg_pos.mpr hc'
          have hε : 0 < ε := lt_min hδ hneg
          have hε_head : ε ≤ -c.fn.eval x := min_le_right _ _
          refine ⟨ε, hε, le_of_lt hε, (min_le_left _ _).trans hδ1, ?_⟩
          intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · simp only [hk]
            linarith
          · have hd' := htail d hd
            cases hdk : d.kind with
            | weak => simpa [hdk] using hd'
            | strict =>
                have hε_le : ε ≤ δ := min_le_left _ _
                simp only [hdk] at hd' ⊢
                linarith

/-- Given [a positive slack](hyp:hδ) and [a common-slack feasible point](hyp:hx), [that point
belongs to the strict cell](goal). -/
theorem strictPoint_of_positiveSlack {n : ℕ} {Γ : AffineSystem n}
    {x : Fin n → ℝ} {δ : ℝ} (hδ : 0 < δ) (hx : commonSlackFeasible Γ x δ) :
    x ∈ strictCell Γ := by
  intro c hc
  have hcx := hx.2.2 c hc
  cases hk : c.kind with
  | weak => simpa [Constraint.strictHolds, hk] using hcx
  | strict =>
      simp only [hk] at hcx
      simp only [Constraint.strictHolds, hk]
      linarith

/-- Given [a positive slack](hyp:hδ) and [a common-slack feasible point](hyp:hx), [the
common-slack value is positive](goal). -/
theorem commonSlackValue_pos_of_witness {n : ℕ} {Γ : AffineSystem n}
    {x : Fin n → ℝ} {δ : ℝ} (hδ : 0 < δ) (hx : commonSlackFeasible Γ x δ) :
    0 < commonSlackValue Γ := by
  have hmem : δ ∈ commonSlackSet Γ := ⟨x, hx⟩
  have hle : δ ≤ commonSlackValue Γ := by
    unfold commonSlackValue
    exact le_csSup (bddAbove_commonSlackSet Γ) hmem
  exact hδ.trans_le hle

/-- Given [a positive common-slack value](hyp:hval), [some feasible slack is positive](goal). -/
theorem positiveSlackWitness_of_commonSlackValue_pos {n : ℕ} {Γ : AffineSystem n}
    (hval : 0 < commonSlackValue Γ) : ∃ δ : ℝ, 0 < δ ∧ δ ∈ commonSlackSet Γ := by
  have hne : (commonSlackSet Γ).Nonempty := by
    by_contra h
    have hempty : commonSlackSet Γ = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [commonSlackValue, hempty, Real.sSup_empty] at hval
    exact (lt_irrefl 0 hval)
  have hhalf : commonSlackValue Γ / 2 < commonSlackValue Γ := by linarith
  rw [commonSlackValue] at hhalf
  rcases (lt_csSup_iff (bddAbove_commonSlackSet Γ) hne).mp hhalf with ⟨δ, hδmem, hhalfδ⟩
  refine ⟨δ, ?_, hδmem⟩
  have hhalf_pos : 0 < commonSlackValue Γ / 2 := by linarith
  exact hhalf_pos.trans hhalfδ

/-- Given [an affine constraint system](hyp:Γ), [its strict cell is nonempty exactly when
its bounded common-slack value is positive](goal). -/
theorem strictFeasible_iff_commonSlackValue_pos {n : ℕ} (Γ : AffineSystem n) :
    (strictCell Γ).Nonempty ↔ 0 < commonSlackValue Γ := by
  constructor
  · rintro ⟨x, hx⟩
    rcases positiveSlackWitness_of_strictPoint hx with ⟨δ, hδ, hfeas⟩
    exact commonSlackValue_pos_of_witness hδ hfeas
  · intro hval
    rcases positiveSlackWitness_of_commonSlackValue_pos hval with ⟨δ, hδ, x, hx⟩
    exact ⟨x, strictPoint_of_positiveSlack hδ hx⟩

/-- Given [a number of coordinates](hyp:n), [the empty system's common-slack value equals
one](goal). -/
theorem commonSlackValue_nil (n : ℕ) : commonSlackValue ([] : AffineSystem n) = 1 := by
  have hmem : (1 : ℝ) ∈ commonSlackSet ([] : AffineSystem n) := by
    refine ⟨fun _ => 0, ?_⟩
    simp [commonSlackFeasible]
  apply le_antisymm
  · unfold commonSlackValue
    exact csSup_le ⟨1, hmem⟩ fun δ hδ => hδ.choose_spec.2.1
  · unfold commonSlackValue
    exact le_csSup (bddAbove_commonSlackSet ([] : AffineSystem n)) hmem

end Causalean.Mathlib.Optimization.AffineSignCellClosure

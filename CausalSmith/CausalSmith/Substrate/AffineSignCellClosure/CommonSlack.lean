import CausalSmith.Substrate.AffineSignCellClosure.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Common-slack strict feasibility

This module gives the bounded Phase-I common-slack formulation. Strict constraints receive
one shared margin `δ`, weak constraints remain weak, and `δ` is restricted to `[0, 1]`.
-/

open Set

namespace CausalSmith.Substrate.AffineSignCellClosure

/-- A point and slack are common-slack feasible when the slack lies in `[0,1]`, weak
constraints remain at level zero, and strict constraints hold at level `-δ`. -/
def commonSlackFeasible {n : ℕ} (Γ : AffineSystem n) (x : Fin n → ℝ) (δ : ℝ) : Prop :=
  0 ≤ δ ∧ δ ≤ 1 ∧ ∀ c ∈ Γ,
    c.fn.eval x ≤ match c.kind with | .weak => 0 | .strict => -δ

/-- The feasible common-slack set contains the slacks admitting some feasible point. -/
def commonSlackSet {n : ℕ} (Γ : AffineSystem n) : Set ℝ :=
  {δ | ∃ x, commonSlackFeasible Γ x δ}

/-- The common-slack value is the supremum of all feasible slacks. -/
noncomputable def commonSlackValue {n : ℕ} (Γ : AffineSystem n) : ℝ :=
  sSup (commonSlackSet Γ)

/-- Feasible common slacks are bounded above by one. -/
/- Proof strategy: use `1` as a common upper bound and project `δ ≤ 1` from the
feasibility witness. -/
theorem bddAbove_commonSlackSet {n : ℕ} (Γ : AffineSystem n) :
    BddAbove (commonSlackSet Γ) := by
  refine ⟨1, ?_⟩
  intro δ hδ
  rcases hδ with ⟨x, hx⟩
  exact hx.2.1

/-- A strictly feasible point admits a common-slack certificate with a positive slack. -/
/- Proof strategy: induct on the finite list while keeping the same point. A weak head does
not change the candidate margin. At a strict head, shrink the positive tail margin with
`min` of `-f x`; cap the empty-list base margin at one. -/
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
            have hc' : c.fn.eval x < 0 := by
              simpa [Constraint.strictHolds, hk] using hc
            exact neg_pos.mpr hc'
          have hε : 0 < ε := by
            exact lt_min hδ hneg
          have hε_head : ε ≤ -c.fn.eval x := min_le_right _ _
          refine ⟨ε, hε, le_of_lt hε, (min_le_left _ _).trans hδ1, ?_⟩
          intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · simp only [hk]
            linarith
          · have hd' := htail d hd
            cases hdk : d.kind with
            | weak =>
                simpa [hdk] using hd'
            | strict =>
                have hε_le : ε ≤ δ := min_le_left _ _
                simp only [hdk] at hd' ⊢
                linarith

/-- A common-slack certificate with positive slack is a point of the strict cell. -/
/- Proof strategy: unfold the two notions constraint-by-constraint. Weak constraints are
unchanged; for a strict constraint combine `f x ≤ -δ` with `-δ < 0`. -/
theorem strictPoint_of_positiveSlack {n : ℕ} {Γ : AffineSystem n}
    {x : Fin n → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hx : commonSlackFeasible Γ x δ) :
    x ∈ strictCell Γ := by
  intro c hc
  have hcx := hx.2.2 c hc
  cases hk : c.kind with
  | weak =>
      simpa [Constraint.strictHolds, hk] using hcx
  | strict =>
      simp only [hk] at hcx
      simp only [Constraint.strictHolds, hk]
      linarith

/-- A positive feasible slack forces the common-slack supremum to be positive. -/
/- Proof strategy: package the certificate as membership in `commonSlackSet`, apply
`le_csSup` using `bddAbove_commonSlackSet`, and compare the positive slack to the supremum. -/
theorem commonSlackValue_pos_of_witness {n : ℕ} {Γ : AffineSystem n}
    {x : Fin n → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hx : commonSlackFeasible Γ x δ) :
    0 < commonSlackValue Γ := by
  have hmem : δ ∈ commonSlackSet Γ := ⟨x, hx⟩
  have hle : δ ≤ commonSlackValue Γ := by
    unfold commonSlackValue
    exact le_csSup (bddAbove_commonSlackSet Γ) hmem
  exact hδ.trans_le hle

/-- Positivity of the common-slack supremum yields an actual positive feasible slack. -/
/- Proof strategy: the feasible-slack set is bounded above. If it were empty, `sSup` would
be zero; after obtaining nonemptiness, apply a strict `csSup` approximation below the
positive supremum (for example at half the value). -/
theorem positiveSlackWitness_of_commonSlackValue_pos {n : ℕ} {Γ : AffineSystem n}
    (hval : 0 < commonSlackValue Γ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ∈ commonSlackSet Γ := by
  have hne : (commonSlackSet Γ).Nonempty := by
    by_contra h
    have hempty : commonSlackSet Γ = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [commonSlackValue, hempty, Real.sSup_empty] at hval
    exact (lt_irrefl 0 hval)
  have hhalf : commonSlackValue Γ / 2 < commonSlackValue Γ := by
    linarith
  rw [commonSlackValue] at hhalf
  rcases (lt_csSup_iff (bddAbove_commonSlackSet Γ) hne).mp hhalf with
    ⟨δ, hδmem, hhalfδ⟩
  refine ⟨δ, ?_, hδmem⟩
  have hhalf_pos : 0 < commonSlackValue Γ / 2 := by
    linarith
  exact hhalf_pos.trans hhalfδ

/-- A finite affine sign cell is strictly feasible exactly when its bounded common-slack
supremum is positive. -/
/- Proof strategy: forward composition uses `positiveSlackWitness_of_strictPoint` and
`commonSlackValue_pos_of_witness`. In reverse, unpack the positive slack returned by
`positiveSlackWitness_of_commonSlackValue_pos` and apply `strictPoint_of_positiveSlack`. -/
theorem strictFeasible_iff_commonSlackValue_pos {n : ℕ} (Γ : AffineSystem n) :
    (strictCell Γ).Nonempty ↔ 0 < commonSlackValue Γ := by
  constructor
  · rintro ⟨x, hx⟩
    rcases positiveSlackWitness_of_strictPoint hx with ⟨δ, hδ, hfeas⟩
    exact commonSlackValue_pos_of_witness hδ hfeas
  · intro hval
    rcases positiveSlackWitness_of_commonSlackValue_pos hval with ⟨δ, hδ, x, hx⟩
    exact ⟨x, strictPoint_of_positiveSlack hδ hx⟩

/-- The empty constraint system has common-slack value one, covering the no-constraint
edge case of the Phase-I formulation. -/
/- Proof strategy: slack `1` is feasible at any point, every feasible slack is at most one,
and antisymmetry follows from `le_csSup` and `csSup_le`. -/
theorem commonSlackValue_nil (n : ℕ) :
    commonSlackValue ([] : AffineSystem n) = 1 := by
  have hmem : (1 : ℝ) ∈ commonSlackSet ([] : AffineSystem n) := by
    refine ⟨fun _ => 0, ?_⟩
    simp [commonSlackFeasible]
  apply le_antisymm
  · unfold commonSlackValue
    exact csSup_le ⟨1, hmem⟩ fun δ hδ => hδ.choose_spec.2.1
  · unfold commonSlackValue
    exact le_csSup (bddAbove_commonSlackSet ([] : AffineSystem n)) hmem

end CausalSmith.Substrate.AffineSignCellClosure

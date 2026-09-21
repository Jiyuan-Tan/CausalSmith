/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Staggered-adoption indicator residuals

This file derives the two-way fixed-effect residual formulas for diagonal and
triangular adoption indicators in the cohort-period panels constructed by
`CohortPeriod.lean`.
-/

module
public import Causalean.Panel.FixedEffect.IndicatorClosedForms.CohortPeriod

/-! # Staggered Indicator Closed Forms

This part proves closed forms for diagonal and triangular staggered-adoption
indicators in generic cohort-period panels. -/

@[expose] public section

open scoped BigOperators

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false

namespace Causalean
namespace Panel
namespace Cells

variable {I T : Type*}
variable [Fintype I] [Fintype T] [DecidableEq I] [DecidableEq T]

section CohortPeriod

variable {C S : ℕ}
variable [Nonempty (Fin C)] [Nonempty (Fin S)]
variable (law : CohortLaw C) (hpi : ∀ g : Fin C, 0 < (law.pi g : ℝ))
/-! ### Staggered indicators: diagonal and triangular -/

/-- In a cohort-by-period panel with cohort-period weights, the weighted inner
product of any outcome array with a cohort's unit indicator equals that cohort's
weighted sum of outcomes across periods. -/
lemma cohortPeriod_ip_unit_eq (law : CohortLaw C)
    (hpi : ∀ g : Fin C, 0 < (law.pi g : ℝ))
    (Y : V (Fin C) (Fin S)) (g₁ : Fin C) :
    (cohortPeriodCells law hpi).ip Y
      (fun r : Fin C × Fin S => if r.1 = g₁ then (1 : ℝ) else 0) =
        ((law.pi g₁ : ℝ) / (Fintype.card (Fin S) : ℝ)) *
          ∑ t : Fin S, Y (g₁, t) := by
  unfold ip
  simp only [cohortPeriodCells, Finset.mem_univ, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero, ↓reduceIte]
  rw [Fintype.sum_prod_type]
  rw [show (∑ x : Fin C, ∑ t : Fin S,
      if x = g₁ then (law.pi x : ℝ) / (Fintype.card (Fin S) : ℝ) * Y (x, t) else 0) =
      ∑ t : Fin S, (law.pi g₁ : ℝ) / (Fintype.card (Fin S) : ℝ) * Y (g₁, t) by
    simpa [eq_comm] using (Fintype.sum_ite_eq (i := g₁)
      (f := fun x : Fin C =>
        ∑ t : Fin S, (law.pi x : ℝ) / (Fintype.card (Fin S) : ℝ) * Y (x, t))).symm]
  rw [Finset.mul_sum]

/-- In a cohort-by-period panel with cohort-period weights, the weighted inner
product of any outcome array with a period indicator equals the cohort-weighted
sum of outcomes in that period. -/
lemma cohortPeriod_ip_period_eq (law : CohortLaw C)
    (hpi : ∀ g : Fin C, 0 < (law.pi g : ℝ))
    (Y : V (Fin C) (Fin S)) (t₁ : Fin S) :
    (cohortPeriodCells law hpi).ip Y
      (fun r : Fin C × Fin S => if r.2 = t₁ then (1 : ℝ) else 0) =
        (1 / (Fintype.card (Fin S) : ℝ)) *
          ∑ g : Fin C, (law.pi g : ℝ) * Y (g, t₁) := by
  unfold ip
  simp only [cohortPeriodCells, Finset.mem_univ, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero, ↓reduceIte]
  rw [Fintype.sum_prod_type]
  rw [show (∑ g : Fin C, ∑ t : Fin S,
      if t = t₁ then (law.pi g : ℝ) / (Fintype.card (Fin S) : ℝ) * Y (g, t) else 0) =
      ∑ g : Fin C, (law.pi g : ℝ) / (Fintype.card (Fin S) : ℝ) * Y (g, t₁) by
    refine Finset.sum_congr rfl ?_
    intro g _
    simpa [eq_comm] using (Fintype.sum_ite_eq (i := t₁)
      (f := fun t : Fin S => (law.pi g : ℝ) / (Fintype.card (Fin S) : ℝ) * Y (g, t))).symm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro g _
  ring

private noncomputable def diagRowMean {C S : ℕ} (g : Fin C) : ℝ :=
  if g.val < S then 1 / (Fintype.card (Fin S) : ℝ) else 0

private noncomputable def diagPeriodMean {C S : ℕ}
    (law : CohortLaw C) (t : Fin S) : ℝ :=
  if h : t.val < C then (law.pi ⟨t.val, h⟩ : ℝ) else 0

private noncomputable def diagGrandMean {C S : ℕ}
    (law : CohortLaw C) : ℝ :=
  (1 / (Fintype.card (Fin S) : ℝ)) *
    ∑ g : Fin C, (if g.val < S then (law.pi g : ℝ) else 0)

private noncomputable def diagX {C S : ℕ} : V (Fin C) (Fin S) :=
  fun s => if s.1.val = s.2.val then (1 : ℝ) else 0

private noncomputable def diagY {C S : ℕ} (law : CohortLaw C) :
    V (Fin C) (Fin S) :=
  fun s =>
    diagX s - diagRowMean (S := S) s.1 - diagPeriodMean law s.2 +
      diagGrandMean (S := S) law

private lemma diagonal_row_hit_sum (g : Fin C) :
    (∑ t : Fin S, (if g.val = t.val then (1 : ℝ) else 0)) =
      (if g.val < S then (1 : ℝ) else 0) := by
  by_cases hg : g.val < S
  · rw [show (∑ t : Fin S, (if g.val = t.val then (1 : ℝ) else 0)) =
        ∑ t : Fin S, (if t = ⟨g.val, hg⟩ then (1 : ℝ) else 0) by
      refine Finset.sum_congr rfl ?_
      intro t _
      by_cases hgt : g.val = t.val
      · have ht_eq : t = ⟨g.val, hg⟩ := by
          ext
          exact hgt.symm
        rw [if_pos hgt, if_pos ht_eq]
      · have ht_ne : t ≠ ⟨g.val, hg⟩ := by
          intro ht_eq
          apply hgt
          rw [ht_eq]
        rw [if_neg hgt, if_neg ht_ne]]
    rw [show (∑ t : Fin S, (if t = ⟨g.val, hg⟩ then (1 : ℝ) else 0)) = (1 : ℝ) by
      simpa using (Fintype.sum_ite_eq (i := ⟨g.val, hg⟩)
        (f := fun _ : Fin S => (1 : ℝ))).symm]
    simp [hg]
  · have hzero : ∀ t : Fin S, (if g.val = t.val then (1 : ℝ) else 0) = 0 := by
      intro t
      have hne : g.val ≠ t.val := by
        intro heq
        apply hg
        rw [heq]
        exact t.isLt
      rw [if_neg hne]
    rw [Finset.sum_eq_zero]
    · simp [hg]
    · intro t _
      exact hzero t

private lemma diagonal_col_hit_sum (law : CohortLaw C) (t : Fin S) :
    (∑ g : Fin C, (law.pi g : ℝ) * (if g.val = t.val then (1 : ℝ) else 0)) =
      diagPeriodMean law t := by
  unfold diagPeriodMean
  by_cases ht : t.val < C
  · rw [show (∑ g : Fin C, (law.pi g : ℝ) * (if g.val = t.val then (1 : ℝ) else 0)) =
        ∑ g : Fin C, (law.pi g : ℝ) * (if g = ⟨t.val, ht⟩ then (1 : ℝ) else 0) by
      refine Finset.sum_congr rfl ?_
      intro g _
      by_cases hgt : g.val = t.val
      · have hg_eq : g = ⟨t.val, ht⟩ := by
          ext
          exact hgt
        rw [if_pos hgt, if_pos hg_eq]
      · have hg_ne : g ≠ ⟨t.val, ht⟩ := by
          intro hg_eq
          apply hgt
          rw [hg_eq]
        rw [if_neg hgt, if_neg hg_ne]]
    rw [show (∑ g : Fin C, (law.pi g : ℝ) *
          (if g = ⟨t.val, ht⟩ then (1 : ℝ) else 0)) =
        (law.pi ⟨t.val, ht⟩ : ℝ) by
      simpa using (Fintype.sum_ite_eq (i := ⟨t.val, ht⟩)
        (f := fun g : Fin C => (law.pi g : ℝ))).symm]
    simp [ht]
  · have hzero :
        ∀ g : Fin C, (law.pi g : ℝ) * (if g.val = t.val then (1 : ℝ) else 0) = 0 := by
      intro g
      have hne : g.val ≠ t.val := by
        intro heq
        apply ht
        rw [← heq]
        exact g.isLt
      rw [if_neg hne]
      ring
    rw [Finset.sum_eq_zero]
    · simp [ht]
    · intro g _
      exact hzero g

private lemma diagonal_periodMean_sum_eq_grand_sum (law : CohortLaw C) :
    (∑ t : Fin S, diagPeriodMean law t) =
      ∑ g : Fin C, (if g.val < S then (law.pi g : ℝ) else 0) := by
  unfold diagPeriodMean
  rw [Finset.sum_fin_eq_sum_range]
  rw [Finset.sum_fin_eq_sum_range]
  simp only
  let f : ℕ → ℝ := fun x => if hC : x < C then (law.pi ⟨x, hC⟩ : ℝ) else 0
  let g : ℕ → ℝ := fun x => if hS : x < S then f x else 0
  have hL : (∑ x ∈ Finset.range S,
        if h : x < S then (if hC : x < C then (law.pi ⟨x, hC⟩ : ℝ) else 0) else 0) =
      ∑ x ∈ Finset.range S, f x := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hS : x < S := Finset.mem_range.mp hx
    simp [f, hS]
  have hR : (∑ x ∈ Finset.range C,
        if h : x < C then (if x < S then (law.pi ⟨x, h⟩ : ℝ) else 0) else 0) =
      ∑ x ∈ Finset.range C, g x := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hC : x < C := Finset.mem_range.mp hx
    by_cases hS : x < S <;> simp [f, g, hC, hS]
  rw [hL, hR]
  exact Finset.sum_congr_of_eq_on_inter
    (s₁ := Finset.range S) (s₂ := Finset.range C) (f := f) (g := g)
    (by
      intro x _ hxCnot
      have hnot : ¬ x < C := by simpa [Finset.mem_range] using hxCnot
      simp [f, hnot])
    (by
      intro x _ hxSnot
      have hnot : ¬ x < S := by simpa [Finset.mem_range] using hxSnot
      simp [g, hnot])
    (by
      intro x hxS _
      have hS : x < S := Finset.mem_range.mp hxS
      simp [g, hS])

private lemma diagonal_weighted_rowMean_eq_grand (law : CohortLaw C) :
    (∑ g : Fin C, (law.pi g : ℝ) * diagRowMean (S := S) g) =
      diagGrandMean (S := S) law := by
  unfold diagRowMean diagGrandMean
  rw [show (∑ g : Fin C,
        (law.pi g : ℝ) * (if g.val < S then 1 / (Fintype.card (Fin S) : ℝ) else 0)) =
      (1 / (Fintype.card (Fin S) : ℝ)) *
        ∑ g : Fin C, (if g.val < S then (law.pi g : ℝ) else 0) by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro g _
    by_cases hg : g.val < S
    · simp [hg]
      ring
    · simp [hg]]

private lemma diagonal_sum_Y_over_periods_eq_zero (law : CohortLaw C)
    (g₁ : Fin C) :
    (∑ t : Fin S, diagY (S := S) law (g₁, t)) = 0 := by
  unfold diagY diagX diagRowMean diagGrandMean
  simp only [Prod.fst, Prod.snd]
  simp only [sum_algebra_simps, diagonal_row_hit_sum (S := S) (g := g₁),
    diagonal_periodMean_sum_eq_grand_sum (S := S) (law := law)]
  have hS0 : (Fintype.card (Fin S) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (Fin S) := Fintype.card_pos
    exact_mod_cast this.ne'
  have hSnz : (S : ℝ) ≠ 0 := by
    simpa [Fintype.card_fin] using hS0
  have hS_mul_inv : (S : ℝ) * (S : ℝ)⁻¹ = 1 := by
    field_simp [hSnz]
  by_cases hg : g₁.val < S <;>
    simp [sum_algebra_simps, hg, Fintype.card_fin, mul_comm, mul_left_comm,
      ← mul_assoc, hS_mul_inv, hSnz]

private lemma diagonal_weighted_sum_Y_over_cohorts_eq_zero (law : CohortLaw C)
    (t₁ : Fin S) :
    (∑ g : Fin C, (law.pi g : ℝ) * diagY (S := S) law (g, t₁)) = 0 := by
  unfold diagY diagX
  simp only [Prod.fst, Prod.snd]
  simp only [sum_algebra_simps,
    diagonal_col_hit_sum (law := law) (t := t₁),
    diagonal_weighted_rowMean_eq_grand (S := S) (law := law)]
  rw [← Finset.sum_mul, ← Finset.sum_mul, law.sumOne]
  ring

private lemma diagonal_centered_orth_unit (law : CohortLaw C)
    (hpi : ∀ g : Fin C, 0 < (law.pi g : ℝ)) (g₁ : Fin C) :
    (cohortPeriodCells law hpi).ip (diagY (S := S) law)
      (fun r : Fin C × Fin S => if r.1 = g₁ then (1 : ℝ) else 0) = 0 := by
  rw [cohortPeriod_ip_unit_eq (law := law) (hpi := hpi)]
  rw [diagonal_sum_Y_over_periods_eq_zero (S := S) (law := law) (g₁ := g₁)]
  ring

private lemma diagonal_centered_orth_period (law : CohortLaw C)
    (hpi : ∀ g : Fin C, 0 < (law.pi g : ℝ)) (t₁ : Fin S) :
    (cohortPeriodCells law hpi).ip (diagY (S := S) law)
      (fun r : Fin C × Fin S => if r.2 = t₁ then (1 : ℝ) else 0) = 0 := by
  rw [cohortPeriod_ip_period_eq (law := law) (hpi := hpi)]
  rw [diagonal_weighted_sum_Y_over_cohorts_eq_zero (S := S) (law := law) (t₁ := t₁)]
  ring

private noncomputable def triRowMean {C S : ℕ} (g : Fin C) : ℝ :=
  (∑ t : Fin S, (if g.val < t.val then (1 : ℝ) else 0)) /
    (Fintype.card (Fin S) : ℝ)

private noncomputable def triPeriodMean {C S : ℕ}
    (law : CohortLaw C) (t : Fin S) : ℝ :=
  ∑ g : Fin C, (if g.val < t.val then (1 : ℝ) else 0) * (law.pi g : ℝ)

private noncomputable def triGrandMean {C S : ℕ}
    (law : CohortLaw C) : ℝ :=
  (1 / (Fintype.card (Fin S) : ℝ)) *
    ∑ g : Fin C, ∑ t : Fin S,
      (if g.val < t.val then (law.pi g : ℝ) else 0)

private noncomputable def triX {C S : ℕ} : V (Fin C) (Fin S) :=
  fun s => if s.1.val < s.2.val then (1 : ℝ) else 0

private noncomputable def triY {C S : ℕ} (law : CohortLaw C) :
    V (Fin C) (Fin S) :=
  fun s =>
    triX s - triRowMean (S := S) s.1 - triPeriodMean law s.2 +
      triGrandMean (S := S) law

private lemma tri_sum_periodMean_eq_double (law : CohortLaw C) :
    (∑ t : Fin S, triPeriodMean law t) =
      ∑ g : Fin C, ∑ t : Fin S,
        (if g.val < t.val then (law.pi g : ℝ) else 0) := by
  unfold triPeriodMean
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro g _
  refine Finset.sum_congr rfl ?_
  intro t _
  by_cases h : g.val < t.val <;> simp [h]

private lemma tri_weighted_rowMean_eq_grand (law : CohortLaw C) :
    (∑ g : Fin C, (law.pi g : ℝ) * triRowMean (S := S) g) =
      triGrandMean (S := S) law := by
  unfold triRowMean triGrandMean
  rw [show (∑ g : Fin C,
        (law.pi g : ℝ) * ((∑ t : Fin S, if g.val < t.val then (1 : ℝ) else 0) /
          (Fintype.card (Fin S) : ℝ))) =
      (1 / (Fintype.card (Fin S) : ℝ)) *
        ∑ g : Fin C, (law.pi g : ℝ) *
          (∑ t : Fin S, if g.val < t.val then (1 : ℝ) else 0) by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro g _
    ring]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro g _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro t _
  by_cases h : g.val < t.val <;> simp [h]

private lemma tri_sum_Y_over_periods_eq_zero (law : CohortLaw C)
    (g₁ : Fin C) :
    (∑ t : Fin S, triY (S := S) law (g₁, t)) = 0 := by
  unfold triY triX triRowMean triGrandMean
  simp only [Prod.fst, Prod.snd]
  simp only [sum_algebra_simps, tri_sum_periodMean_eq_double (S := S) (law := law)]
  have hS0 : (Fintype.card (Fin S) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (Fin S) := Fintype.card_pos
    exact_mod_cast this.ne'
  field_simp [hS0]
  ring_nf

private lemma tri_weighted_sum_Y_over_cohorts_eq_zero (law : CohortLaw C)
    (t₁ : Fin S) :
    (∑ g : Fin C, (law.pi g : ℝ) * triY (S := S) law (g, t₁)) = 0 := by
  unfold triY triX triPeriodMean
  simp only [Prod.fst, Prod.snd]
  simp only [sum_algebra_simps, tri_weighted_rowMean_eq_grand (S := S) (law := law)]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, law.sumOne, one_mul]
  simp [← Finset.sum_mul, law.sumOne, mul_comm]

private lemma tri_centered_orth_unit (law : CohortLaw C)
    (hpi : ∀ g : Fin C, 0 < (law.pi g : ℝ)) (g₁ : Fin C) :
    (cohortPeriodCells law hpi).ip (triY (S := S) law)
      (fun r : Fin C × Fin S => if r.1 = g₁ then (1 : ℝ) else 0) = 0 := by
  rw [cohortPeriod_ip_unit_eq (law := law) (hpi := hpi)]
  rw [tri_sum_Y_over_periods_eq_zero (S := S) (law := law) (g₁ := g₁)]
  ring

private lemma tri_centered_orth_period (law : CohortLaw C)
    (hpi : ∀ g : Fin C, 0 < (law.pi g : ℝ)) (t₁ : Fin S) :
    (cohortPeriodCells law hpi).ip (triY (S := S) law)
      (fun r : Fin C × Fin S => if r.2 = t₁ then (1 : ℝ) else 0) = 0 := by
  rw [cohortPeriod_ip_period_eq (law := law) (hpi := hpi)]
  rw [tri_weighted_sum_Y_over_cohorts_eq_zero (S := S) (law := law) (t₁ := t₁)]
  ring

/-- For [an evaluation cell `r`](hyp:r), [the cohort-period-weighted two-way-fixed-effect
residual of the diagonal (switch-on) indicator `1{g.val = t.val}`, evaluated at `r`, equals the
indicator minus the cohort-conditional mean, minus the period-conditional mean net of the grand
mean](goal).

In closed form

    tildeX R = ind(g.val = t.val)
              − E[R | g] − (E[R | t] − E[R])

with conditional means `E[R | g] = (1/S) · ind(g.val < S)`,
`E[R | t] = ind(t.val < C) · π(t.val)`, and grand mean
`E[R] = (1/S) · ∑_{g : g.val < S} π(g)`. -/
theorem tildeX_diagonal_indicator_cohortPeriod
    (r : Fin C × Fin S) :
    (cohortPeriodCells law hpi).tildeX
        Cells.H_twfe
        (fun s : Fin C × Fin S => if s.1.val = s.2.val then (1 : ℝ) else 0) r =
      (if r.1.val = r.2.val then (1 : ℝ) else 0)
        - (if r.1.val < S then 1 / (Fintype.card (Fin S) : ℝ) else 0)
        - (if h : r.2.val < C then (law.pi ⟨r.2.val, h⟩ : ℝ) else 0)
        + (1 / (Fintype.card (Fin S) : ℝ)) *
            ∑ g : Fin C, (if g.val < S then (law.pi g : ℝ) else 0) := by
  classical
  let c : Cells (Fin C) (Fin S) := cohortPeriodCells law hpi
  let X : V (Fin C) (Fin S) := diagX
  let Y : V (Fin C) (Fin S) := diagY law
  let G : V (Fin C) (Fin S) := X - Y
  have hG_mem : G ∈ Cells.H_twfe := by
    refine ⟨fun g => diagRowMean (S := S) g - diagGrandMean (S := S) law,
      fun t => diagPeriodMean law t, ?_⟩
    intro p
    simp [G, X, Y, diagY, diagX, diagRowMean, diagPeriodMean, diagGrandMean]
    ring
  have hXsubG : X - G = Y := by
    ext s
    simp [G]
  have horth : ∀ h ∈ Cells.H_twfe, c.ip (X - G) h = 0 := by
    rw [H_twfe_orthogonal_iff]
    constructor
    · intro g₁
      rw [hXsubG]
      exact diagonal_centered_orth_unit (S := S) (law := law) (hpi := hpi) (g₁ := g₁)
    · intro t₁
      rw [hXsubG]
      exact diagonal_centered_orth_period (S := S) (law := law) (hpi := hpi) (t₁ := t₁)
  have hproj : c.proj Cells.H_twfe X r = G r :=
    c.proj_apply_eq_of_mem_orthogonal Cells.H_twfe X hG_mem horth r
      (by simp [c, cohortPeriodCells])
  calc
    c.tildeX Cells.H_twfe X r = (X - c.proj Cells.H_twfe X) r := by
      simp [Cells.tildeX_eq]
    _ = Y r := by
      rw [Pi.sub_apply, hproj]
      exact congrFun hXsubG r
    _ = (if r.1.val = r.2.val then (1 : ℝ) else 0)
        - (if r.1.val < S then 1 / (Fintype.card (Fin S) : ℝ) else 0)
        - (if h : r.2.val < C then (law.pi ⟨r.2.val, h⟩ : ℝ) else 0)
        + (1 / (Fintype.card (Fin S) : ℝ)) *
            ∑ g : Fin C, (if g.val < S then (law.pi g : ℝ) else 0) := rfl

/-- For [an evaluation cell `r`](hyp:r), [the cohort-period-weighted two-way-fixed-effect
residual of the triangular (continued-treatment) indicator `1{g.val < t.val}`, evaluated at
`r`, equals the indicator minus the cohort-conditional mean, minus the period-conditional mean
net of the grand mean](goal).

In closed form

    tildeX J = ind(g.val < t.val)
              − E[J | g] − (E[J | t] − E[J])

with conditional means `E[J | g] = (1/S) · ∑_t ind(g.val < t.val)`,
`E[J | t] = ∑_{g'} π(g') ind(g'.val < t.val)`, and grand mean
`E[J] = (1/S) · ∑_{g, t} π(g) · ind(g.val < t.val)`. -/
theorem tildeX_triangular_indicator_cohortPeriod
    (r : Fin C × Fin S) :
    (cohortPeriodCells law hpi).tildeX
        Cells.H_twfe
        (fun s : Fin C × Fin S => if s.1.val < s.2.val then (1 : ℝ) else 0) r =
      (if r.1.val < r.2.val then (1 : ℝ) else 0)
        - (∑ s : Fin S, (if r.1.val < s.val then (1 : ℝ) else 0)) /
            (Fintype.card (Fin S) : ℝ)
        - (∑ g : Fin C,
            (if g.val < r.2.val then (1 : ℝ) else 0) * (law.pi g : ℝ))
        + (1 / (Fintype.card (Fin S) : ℝ)) *
            ∑ g : Fin C, ∑ s : Fin S,
              (if g.val < s.val then (law.pi g : ℝ) else 0) := by
  classical
  let c : Cells (Fin C) (Fin S) := cohortPeriodCells law hpi
  let X : V (Fin C) (Fin S) := triX
  let Y : V (Fin C) (Fin S) := triY law
  let G : V (Fin C) (Fin S) := X - Y
  have hG_mem : G ∈ Cells.H_twfe := by
    refine ⟨fun g => triRowMean (S := S) g - triGrandMean (S := S) law,
      fun t => triPeriodMean law t, ?_⟩
    intro p
    simp [G, X, Y, triY, triX, triRowMean, triPeriodMean, triGrandMean]
    ring
  have hXsubG : X - G = Y := by
    ext s
    simp [G]
  have horth : ∀ h ∈ Cells.H_twfe, c.ip (X - G) h = 0 := by
    rw [H_twfe_orthogonal_iff]
    constructor
    · intro g₁
      rw [hXsubG]
      exact tri_centered_orth_unit (S := S) (law := law) (hpi := hpi) (g₁ := g₁)
    · intro t₁
      rw [hXsubG]
      exact tri_centered_orth_period (S := S) (law := law) (hpi := hpi) (t₁ := t₁)
  have hproj : c.proj Cells.H_twfe X r = G r :=
    c.proj_apply_eq_of_mem_orthogonal Cells.H_twfe X hG_mem horth r
      (by simp [c, cohortPeriodCells])
  calc
    c.tildeX Cells.H_twfe X r = (X - c.proj Cells.H_twfe X) r := by
      simp [Cells.tildeX_eq]
    _ = Y r := by
      rw [Pi.sub_apply, hproj]
      exact congrFun hXsubG r
    _ = (if r.1.val < r.2.val then (1 : ℝ) else 0)
        - (∑ s : Fin S, (if r.1.val < s.val then (1 : ℝ) else 0)) /
            (Fintype.card (Fin S) : ℝ)
        - (∑ g : Fin C,
            (if g.val < r.2.val then (1 : ℝ) else 0) * (law.pi g : ℝ))
        + (1 / (Fintype.card (Fin S) : ℝ)) *
            ∑ g : Fin C, ∑ s : Fin S,
              (if g.val < s.val then (law.pi g : ℝ) else 0) := rfl

end CohortPeriod

end Cells
end Panel
end Causalean

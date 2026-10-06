/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Cohort-period indicator residuals

This file defines finite cohort laws and their induced cohort-period weighted
panels, then proves the two-way fixed-effect residual formula for a single
cohort-period cell indicator.
-/

module
public import Causalean.Panel.FixedEffect.IndicatorClosedForms.Basic

/-! # Cohort-Period Indicator Closed Forms

This part defines generic cohort-period cells and proves the closed form for a single
cohort-period cell indicator. -/

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

/-! ### Cohort-period cells (generic, weight `π(g) / S`)

This construction is kept generic and self-contained: every `(g, t)` cell is
observed, and the weight factors into the cohort mass `π(g)` times the uniform
period weight `1 / S`. -/

/-- Cohort law on a finite cohort index `Fin C`: probabilities `π(g) ≥ 0`
summing to one. -/
structure CohortLaw (C : ℕ) where
  /-- Cohort probabilities (nonnegative reals). -/
  pi : Fin C → NNReal
  /-- The probabilities sum to one. -/
  sumOne : (∑ g, (pi g : ℝ)) = 1

/-- Generic cohort-period `Cells` instance for a nonempty set of cohorts and a nonempty set of
periods, a cohort law (a probability mass function over cohorts, summing to one) and strictly positive
cohort masses. Every cell `(g, t) ∈ Fin C × Fin S` is observed and carries weight `π(g) / S`. -/
noncomputable def cohortPeriodCells {C S : ℕ}
    [Nonempty (Fin C)] [Nonempty (Fin S)] (law : CohortLaw C)
    (hpi : ∀ g : Fin C, 0 < (law.pi g : ℝ)) :
    Cells (Fin C) (Fin S) where
  observed := Finset.univ
  observed_nonempty := Finset.univ_nonempty
  weight r := (law.pi r.1 : ℝ) / (Fintype.card (Fin S) : ℝ)
  weight_pos := by
    intro r _
    have hS : (0 : ℝ) < Fintype.card (Fin S) := by exact_mod_cast Fintype.card_pos
    exact div_pos (hpi r.1) hS
  weight_zero_off := by
    intro r hr
    exact (hr (Finset.mem_univ r)).elim
  weight_sum_one := by
    have hS : (Fintype.card (Fin S) : ℝ) ≠ 0 := by
      have : 0 < Fintype.card (Fin S) := Fintype.card_pos
      exact_mod_cast this.ne'
    rw [Fintype.sum_prod_type]
    calc
      ∑ x : Fin C, ∑ _y : Fin S, (law.pi x : ℝ) / (Fintype.card (Fin S) : ℝ)
          = ∑ x : Fin C, (law.pi x : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro x _
            simp only [sum_algebra_simps]
            field_simp [hS]
      _ = 1 := law.sumOne

/-! ### Cohort-period indicator closed forms -/

section CohortPeriod

variable {C S : ℕ}
variable [Nonempty (Fin C)] [Nonempty (Fin S)]
variable (law : CohortLaw C) (hpi : ∀ g : Fin C, 0 < (law.pi g : ℝ))

/-- A singleton indicator centered by the selected category's weight has a
zero weighted average whenever the weights across categories sum to one. -/
lemma cohort_sum_pi_centered_eq_zero {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (hw : ∑ g, w g = 1) (g₀ : α) :
    (∑ g : α,
      w g * ((if g = g₀ then (1 : ℝ) else 0) - w g₀)) =
        0 := by
  simp only [sum_algebra_simps, mul_ite, mul_zero, mul_one]
  rw [← Finset.sum_mul, hw]
  simp

private lemma cohort_cell_centered_orth_unit (law : CohortLaw C)
    (hpi : ∀ g : Fin C, 0 < (law.pi g : ℝ)) (g₀ g₁ : Fin C) (t₀ : Fin S) :
    (cohortPeriodCells law hpi).ip
      (fun s : Fin C × Fin S =>
        ((if s.1 = g₀ then (1 : ℝ) else 0) - (law.pi g₀ : ℝ)) *
          ((if s.2 = t₀ then (1 : ℝ) else 0) -
            1 / (Fintype.card (Fin S) : ℝ)))
      (fun r => if r.1 = g₁ then (1 : ℝ) else 0) = 0 := by
  unfold ip
  simp only [cohortPeriodCells, Finset.mem_univ, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero, ↓reduceIte]
  rw [Fintype.sum_prod_type]
  simp only
  rw [show (∑ x : Fin C, ∑ x_1 : Fin S,
        if x = g₁ then
          (law.pi x : ℝ) / (Fintype.card (Fin S) : ℝ) *
            (((if x = g₀ then 1 else 0) - (law.pi g₀ : ℝ)) *
              ((if x_1 = t₀ then 1 else 0) - 1 / (Fintype.card (Fin S) : ℝ)))
        else 0) =
      ∑ x_1 : Fin S,
          (law.pi g₁ : ℝ) / (Fintype.card (Fin S) : ℝ) *
            (((if g₁ = g₀ then 1 else 0) - (law.pi g₀ : ℝ)) *
              ((if x_1 = t₀ then 1 else 0) - 1 / (Fintype.card (Fin S) : ℝ))) by
    simpa [eq_comm] using (Fintype.sum_ite_eq (i := g₁)
      (f := fun x : Fin C => ∑ x_1 : Fin S,
          (law.pi x : ℝ) / (Fintype.card (Fin S) : ℝ) *
            (((if x = g₀ then 1 else 0) - (law.pi g₀ : ℝ)) *
              ((if x_1 = t₀ then 1 else 0) - 1 / (Fintype.card (Fin S) : ℝ)))))]
  rw [show (∑ x_1 : Fin S,
          (law.pi g₁ : ℝ) / (Fintype.card (Fin S) : ℝ) *
            (((if g₁ = g₀ then 1 else 0) - (law.pi g₀ : ℝ)) *
              ((if x_1 = t₀ then 1 else 0) - 1 / (Fintype.card (Fin S) : ℝ)))) =
      ((law.pi g₁ : ℝ) / (Fintype.card (Fin S) : ℝ) *
        ((if g₁ = g₀ then 1 else 0) - (law.pi g₀ : ℝ))) *
        (∑ x_1 : Fin S,
          ((if x_1 = t₀ then 1 else 0) - 1 / (Fintype.card (Fin S) : ℝ))) by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro x hx
    ring]
  rw [sum_centered_eq_indicator_real (a₀ := t₀), mul_zero]

private lemma cohort_cell_centered_orth_period (law : CohortLaw C)
    (hpi : ∀ g : Fin C, 0 < (law.pi g : ℝ)) (g₀ : Fin C) (t₀ t₁ : Fin S) :
    (cohortPeriodCells law hpi).ip
      (fun s : Fin C × Fin S =>
        ((if s.1 = g₀ then (1 : ℝ) else 0) - (law.pi g₀ : ℝ)) *
          ((if s.2 = t₀ then (1 : ℝ) else 0) -
            1 / (Fintype.card (Fin S) : ℝ)))
      (fun r => if r.2 = t₁ then (1 : ℝ) else 0) = 0 := by
  unfold ip
  simp only [cohortPeriodCells, Finset.mem_univ, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero, ↓reduceIte]
  rw [Fintype.sum_prod_type]
  simp only
  rw [show (∑ x : Fin C, ∑ x_1 : Fin S,
        if x_1 = t₁ then
          (law.pi x : ℝ) / (Fintype.card (Fin S) : ℝ) *
            (((if x = g₀ then 1 else 0) - (law.pi g₀ : ℝ)) *
              ((if x_1 = t₀ then 1 else 0) - 1 / (Fintype.card (Fin S) : ℝ)))
        else 0) =
      ∑ x : Fin C,
          (law.pi x : ℝ) / (Fintype.card (Fin S) : ℝ) *
            (((if x = g₀ then 1 else 0) - (law.pi g₀ : ℝ)) *
              ((if t₁ = t₀ then 1 else 0) - 1 / (Fintype.card (Fin S) : ℝ))) by
    refine Finset.sum_congr rfl ?_
    intro x hx
    simpa [eq_comm] using (Fintype.sum_ite_eq (i := t₁)
      (f := fun t : Fin S =>
          (law.pi x : ℝ) / (Fintype.card (Fin S) : ℝ) *
            (((if x = g₀ then 1 else 0) - (law.pi g₀ : ℝ)) *
              ((if t = t₀ then 1 else 0) - 1 / (Fintype.card (Fin S) : ℝ)))))]
  rw [show (∑ x : Fin C,
          (law.pi x : ℝ) / (Fintype.card (Fin S) : ℝ) *
            (((if x = g₀ then 1 else 0) - (law.pi g₀ : ℝ)) *
              ((if t₁ = t₀ then 1 else 0) - 1 / (Fintype.card (Fin S) : ℝ)))) =
      (((if t₁ = t₀ then 1 else 0) - 1 / (Fintype.card (Fin S) : ℝ)) /
        (Fintype.card (Fin S) : ℝ)) *
        (∑ x : Fin C,
          (law.pi x : ℝ) * ((if x = g₀ then 1 else 0) - (law.pi g₀ : ℝ))) by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro x hx
    ring]
  rw [cohort_sum_pi_centered_eq_zero (fun g => (law.pi g : ℝ)) law.sumOne g₀, mul_zero]

/-- For [a target cohort `g₀`](hyp:g₀), [a target period `t₀`](hyp:t₀), and [an evaluation
cell `r`](hyp:r), [the cohort-period-weighted two-way-fixed-effect residual of the cell
indicator `1{g = g₀, t = t₀}`, evaluated at `r`, equals the product of centered cohort and
period indicators minus the corresponding cross terms fixed by the gauge normalization
`∑_t β(t) = π(g₀)`](goal). -/
theorem tildeX_cell_indicator_cohortPeriod (g₀ : Fin C) (t₀ : Fin S)
    (r : Fin C × Fin S) :
    (cohortPeriodCells law hpi).tildeX
        Cells.H_twfe
        (fun s : Fin C × Fin S =>
          if s.1 = g₀ ∧ s.2 = t₀ then (1 : ℝ) else 0) r =
      (if r.1 = g₀ then (1 : ℝ) else 0) *
          (if r.2 = t₀ then (1 : ℝ) else 0)
        - (law.pi g₀ : ℝ) * (if r.2 = t₀ then (1 : ℝ) else 0)
        - (1 / (Fintype.card (Fin S) : ℝ)) *
            (if r.1 = g₀ then (1 : ℝ) else 0)
        + (law.pi g₀ : ℝ) / (Fintype.card (Fin S) : ℝ) := by
  classical
  let c : Cells (Fin C) (Fin S) := cohortPeriodCells law hpi
  let X : V (Fin C) (Fin S) := fun s : Fin C × Fin S =>
    if s.1 = g₀ ∧ s.2 = t₀ then (1 : ℝ) else 0
  let Y : V (Fin C) (Fin S) := fun s : Fin C × Fin S =>
    ((if s.1 = g₀ then (1 : ℝ) else 0) - (law.pi g₀ : ℝ)) *
      ((if s.2 = t₀ then (1 : ℝ) else 0) -
        1 / (Fintype.card (Fin S) : ℝ))
  let G : V (Fin C) (Fin S) := X - Y
  have hG_mem : G ∈ Cells.H_twfe := by
    refine ⟨fun g => (1 / (Fintype.card (Fin S) : ℝ)) *
        (if g = g₀ then (1 : ℝ) else 0),
      fun t => (law.pi g₀ : ℝ) * (if t = t₀ then (1 : ℝ) else 0) -
        (law.pi g₀ : ℝ) / (Fintype.card (Fin S) : ℝ), ?_⟩
    intro p
    by_cases hg : p.1 = g₀ <;> by_cases ht : p.2 = t₀ <;>
      simp [G, X, Y, hg, ht] <;> ring
  have hXsubG : X - G = Y := by
    ext s
    simp [G]
  have horth : ∀ h ∈ Cells.H_twfe, c.ip (X - G) h = 0 := by
    rw [H_twfe_orthogonal_iff]
    constructor
    · intro g₁
      rw [hXsubG]
      simpa [c, Y] using
        cohort_cell_centered_orth_unit (law := law) (hpi := hpi) (g₀ := g₀)
          (g₁ := g₁) (t₀ := t₀)
    · intro t₁
      rw [hXsubG]
      simpa [c, Y] using
        cohort_cell_centered_orth_period (law := law) (hpi := hpi) (g₀ := g₀)
          (t₀ := t₀) (t₁ := t₁)
  have hproj : c.proj Cells.H_twfe X r = G r :=
    c.proj_apply_eq_of_mem_orthogonal Cells.H_twfe X hG_mem horth r
      (by simp [c, cohortPeriodCells])
  calc
    c.tildeX Cells.H_twfe X r = (X - c.proj Cells.H_twfe X) r := by simp [Cells.tildeX_eq]
    _ = Y r := by
      rw [Pi.sub_apply, hproj]
      exact congrFun hXsubG r
    _ = (if r.1 = g₀ then (1 : ℝ) else 0) *
          (if r.2 = t₀ then (1 : ℝ) else 0)
        - (law.pi g₀ : ℝ) * (if r.2 = t₀ then (1 : ℝ) else 0)
        - (1 / (Fintype.card (Fin S) : ℝ)) *
            (if r.1 = g₀ then (1 : ℝ) else 0)
        + (law.pi g₀ : ℝ) / (Fintype.card (Fin S) : ℝ) := by
          by_cases hg : r.1 = g₀ <;> by_cases ht : r.2 = t₀ <;>
            simp [Y, hg, ht] <;> ring


end CohortPeriod

end Cells
end Panel
end Causalean

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Basic TWFE indicator residuals

This file proves the row-and-column orthogonality criterion and the residual
closed forms for constants, unit indicators, period indicators, and balanced
rectangular indicators. Cohort-period and staggered-adoption forms are supplied
by the two downstream files in this directory.
-/

module
public import Causalean.Tactic.SumAlgebraSimps
public import Causalean.Panel.Cells
public import Causalean.Panel.InnerProduct
public import Causalean.Panel.Subspace
public import Causalean.Panel.FixedEffect
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.NNReal.Basic

/-! # Basic Indicator Residual Closed Forms

This file proves the row-and-column orthogonality criterion and closed-form
two-way fixed-effect residuals for constant, unit-only, period-only, and
balanced rectangular indicators. -/

public section

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

private lemma sum_indicator_mem_real {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) :
    (∑ x : α, (if x ∈ S then (1 : ℝ) else 0)) = (S.card : ℝ) := by
  rw [show (∑ x : α, (if x ∈ S then (1 : ℝ) else 0)) =
      ∑ x ∈ (Finset.univ : Finset α) ∩ S, (1 : ℝ) by
    simpa using
      (Finset.sum_ite_mem (s := (Finset.univ : Finset α)) (t := S)
        (f := fun _ : α => (1 : ℝ)))]
  simp

/-- Centering the indicator of a finite subset by its uniform average makes
its sum across the index set equal to zero. -/
lemma sum_centered_indicator_mem_real {α : Type*}
    [Fintype α] [DecidableEq α] (S : Finset α) :
    (∑ x : α,
      ((if x ∈ S then (1 : ℝ) else 0) - (S.card : ℝ) / (Fintype.card α : ℝ))) =
        0 := by
  rcases isEmpty_or_nonempty α with hα | hα
  · letI := hα
    simp
  · letI := hα
    simp only [sum_algebra_simps, sum_indicator_mem_real]
    have hcard : (Fintype.card α : ℝ) ≠ 0 := by
      have : 0 < Fintype.card α := Fintype.card_pos
      exact_mod_cast this.ne'
    field_simp [hcard]
    ring

/-- For [a value in a nonempty finite type](hyp:α,a₀), [the sum over all values of its singleton
indicator centered by the reciprocal cardinality is zero](goal). -/
lemma sum_centered_eq_indicator_real {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] (a₀ : α) :
    (∑ x : α,
      ((if x = a₀ then (1 : ℝ) else 0) - 1 / (Fintype.card α : ℝ))) = 0 := by
  simp only [sum_algebra_simps, Finset.mem_univ, if_true]
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by
    have : 0 < Fintype.card α := Fintype.card_pos
    exact_mod_cast this.ne'
  field_simp [hcard]
  ring

/-! ### `H_twfe`-orthogonality test against unit/period basis

To certify that an array `g : V I T` is `c.ip`-orthogonal to every member of
`H_twfe`, it suffices to test orthogonality against the spanning families
`e_{i₀}(i, t) := ind(i = i₀)` and `f_{t₀}(i, t) := ind(t = t₀)`.  This
helper is used throughout the indicator closed-form proofs and exported for
downstream residual arguments that need the same row/column reduction. -/

/-- For [a panel weighting scheme](hyp:c) and [any panel array `g`](hyp:g), [`g` is orthogonal,
under the weighted inner product, to every member of the two-way fixed-effect subspace `H_twfe`
exactly when it is orthogonal to every unit indicator and every period indicator](goal).

This reduces `H_twfe` residual proofs to row and column normal equations. -/
lemma H_twfe_orthogonal_iff (c : Cells I T) (g : V I T) :
    (∀ h ∈ Cells.H_twfe, c.ip g h = 0) ↔
      ((∀ i₀ : I,
          c.ip g (fun r => if r.1 = i₀ then (1 : ℝ) else 0) = 0) ∧
       (∀ t₀ : T,
          c.ip g (fun r => if r.2 = t₀ then (1 : ℝ) else 0) = 0)) := by
  classical
  constructor
  · intro horth
    constructor
    · intro i₀
      exact horth (fun r => if r.1 = i₀ then (1 : ℝ) else 0)
        ⟨fun i => if i = i₀ then (1 : ℝ) else 0, fun _ => 0,
          by intro p; simp⟩
    · intro t₀
      exact horth (fun r => if r.2 = t₀ then (1 : ℝ) else 0)
        ⟨fun _ => 0, fun t => if t = t₀ then (1 : ℝ) else 0,
          by intro p; simp⟩
  · rintro ⟨hunit, hperiod⟩ h ⟨a, b, hh⟩
    have hA :
        c.ip g (fun r : I × T => a r.1) = 0 := by
      have hexp :
          c.ip g (fun r : I × T => a r.1) =
            ∑ i₀ : I, a i₀ *
              c.ip g (fun r : I × T => if r.1 = i₀ then (1 : ℝ) else 0) := by
        unfold ip
        rw [show
            (∑ i₀ : I, a i₀ *
                ∑ x ∈ c.observed,
                  c.weight x * g x * (if x.1 = i₀ then (1 : ℝ) else 0)) =
              ∑ x ∈ c.observed, c.weight x * g x * a x.1 by
          rw [show
              (∑ i₀ : I, a i₀ *
                  ∑ x ∈ c.observed,
                    c.weight x * g x * (if x.1 = i₀ then (1 : ℝ) else 0)) =
                ∑ i₀ : I, ∑ x ∈ c.observed,
                  a i₀ * (c.weight x * g x * (if x.1 = i₀ then (1 : ℝ) else 0)) by
            simp only [sum_algebra_simps]]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [show
              (∑ i₀ : I,
                a i₀ * (c.weight x * g x * (if x.1 = i₀ then (1 : ℝ) else 0))) =
                c.weight x * g x * a x.1 by
            rw [show
                (∑ i₀ : I,
                  a i₀ * (c.weight x * g x * (if x.1 = i₀ then (1 : ℝ) else 0))) =
                  (c.weight x * g x) *
                    ∑ i₀ : I, a i₀ * (if x.1 = i₀ then (1 : ℝ) else 0) by
              simp only [sum_algebra_simps]
              exact Finset.sum_congr rfl fun _ _ => by ring]
            rw [show (∑ i₀ : I, a i₀ * (if x.1 = i₀ then (1 : ℝ) else 0)) =
                a x.1 by
              rw [Finset.sum_eq_single x.1]
              · simp
              · intro y _ hy
                simp [hy.symm]
              · intro hnot
                exact (hnot (Finset.mem_univ x.1)).elim]
            ]]
      rw [hexp]
      exact Finset.sum_eq_zero (fun i₀ _ => by rw [hunit i₀, mul_zero])
    have hB :
        c.ip g (fun r : I × T => b r.2) = 0 := by
      have hexp :
          c.ip g (fun r : I × T => b r.2) =
            ∑ t₀ : T, b t₀ *
              c.ip g (fun r : I × T => if r.2 = t₀ then (1 : ℝ) else 0) := by
        unfold ip
        rw [show
            (∑ t₀ : T, b t₀ *
                ∑ x ∈ c.observed,
                  c.weight x * g x * (if x.2 = t₀ then (1 : ℝ) else 0)) =
              ∑ x ∈ c.observed, c.weight x * g x * b x.2 by
          rw [show
              (∑ t₀ : T, b t₀ *
                  ∑ x ∈ c.observed,
                    c.weight x * g x * (if x.2 = t₀ then (1 : ℝ) else 0)) =
                ∑ t₀ : T, ∑ x ∈ c.observed,
                  b t₀ * (c.weight x * g x * (if x.2 = t₀ then (1 : ℝ) else 0)) by
            simp only [sum_algebra_simps]]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [show
              (∑ t₀ : T,
                b t₀ * (c.weight x * g x * (if x.2 = t₀ then (1 : ℝ) else 0))) =
                c.weight x * g x * b x.2 by
            rw [show
                (∑ t₀ : T,
                  b t₀ * (c.weight x * g x * (if x.2 = t₀ then (1 : ℝ) else 0))) =
                  (c.weight x * g x) *
                    ∑ t₀ : T, b t₀ * (if x.2 = t₀ then (1 : ℝ) else 0) by
              simp only [sum_algebra_simps]
              exact Finset.sum_congr rfl fun _ _ => by ring]
            rw [show (∑ t₀ : T, b t₀ * (if x.2 = t₀ then (1 : ℝ) else 0)) =
                b x.2 by
              rw [Finset.sum_eq_single x.2]
              · simp
              · intro y _ hy
                simp [hy.symm]
              · intro hnot
                exact (hnot (Finset.mem_univ x.2)).elim]
            ]]
      rw [hexp]
      exact Finset.sum_eq_zero (fun t₀ _ => by rw [hperiod t₀, mul_zero])
    calc
      c.ip g h = c.ip g ((fun r : I × T => a r.1) + fun r : I × T => b r.2) := by
        congr 1
        ext p
        exact hh p
      _ = c.ip g (fun r : I × T => a r.1) +
          c.ip g (fun r : I × T => b r.2) := by
        rw [c.ip_add_right]
      _ = 0 := by rw [hA, hB]; ring

/-! ### Constants are absorbed by `H_twfe` -/

/-- The TWFE residual of a constant array vanishes on every observed cell. -/
theorem tildeX_const (c : Cells I T) (k : ℝ) (r : I × T) (hr : r ∈ c.observed) :
    c.tildeX Cells.H_twfe (fun _ : I × T => k) r = 0 := by
  -- PROOF: constants belong to `H_twfe` (`const_mem_H_twfe`), so by
  -- `residualize_self_of_mem` the residual vanishes on observed cells.
  exact c.residualize_self_of_mem Cells.H_twfe (Cells.const_mem_H_twfe k) r hr

/-! ### Unit-only and period-only indicators are absorbed by `H_twfe` -/

/-- Unit indicator is absorbed by `H_twfe`: `ind(i = i₀)` lies in `H_twfe`
(via `a(i) := ind(i = i₀)`, `b(t) := 0`), so its residual vanishes on every
observed cell.  Independent of the weights. -/
theorem tildeX_unit_indicator (c : Cells I T) (i₀ : I)
    (r : I × T) (hr : r ∈ c.observed) :
    c.tildeX Cells.H_twfe
        (fun s : I × T => if s.1 = i₀ then (1 : ℝ) else 0) r = 0 := by
  apply c.residualize_self_of_mem Cells.H_twfe ?_ r hr
  exact ⟨fun i => (if i = i₀ then 1 else 0 : ℝ), fun _ => 0,
    by intro p; simp⟩

/-- Period indicator is absorbed by `H_twfe`: `ind(t = t₀)` lies in `H_twfe`
(via `a := 0`, `b(t) := ind(t = t₀)`), so its residual vanishes on every
observed cell.  Independent of the weights. -/
theorem tildeX_period_indicator (c : Cells I T) (t₀ : T)
    (r : I × T) (hr : r ∈ c.observed) :
    c.tildeX Cells.H_twfe
        (fun s : I × T => if s.2 = t₀ then (1 : ℝ) else 0) r = 0 := by
  apply c.residualize_self_of_mem Cells.H_twfe ?_ r hr
  exact ⟨fun _ => 0, fun t => (if t = t₀ then 1 else 0 : ℝ),
    by intro p; simp⟩

/-! ### Product indicator under balanced weights -/

section Balanced

variable [Nonempty I] [Nonempty T]

private lemma balanced_centered_product_orth_unit (S_I : Finset I) (S_T : Finset T)
    (i₀ : I) :
    (balanced (I := I) (T := T)).ip
      (fun s : I × T =>
        ((if s.1 ∈ S_I then (1 : ℝ) else 0) -
            (S_I.card : ℝ) / (Fintype.card I : ℝ)) *
          ((if s.2 ∈ S_T then (1 : ℝ) else 0) -
            (S_T.card : ℝ) / (Fintype.card T : ℝ)))
      (fun r => if r.1 = i₀ then (1 : ℝ) else 0) = 0 := by
  unfold ip
  rw [balanced_observed]
  simp only [balanced_weight, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
    mul_zero, ↓reduceIte]
  rw [Fintype.sum_prod_type]
  simp only
  rw [show (∑ x : I, ∑ x_1 : T,
        if x = i₀ then
          1 / ((Fintype.card I : ℝ) * (Fintype.card T : ℝ)) *
            (((if x ∈ S_I then 1 else 0) - (S_I.card : ℝ) / (Fintype.card I : ℝ)) *
              ((if x_1 ∈ S_T then 1 else 0) - (S_T.card : ℝ) / (Fintype.card T : ℝ)))
        else 0) =
      ∑ x_1 : T,
          1 / ((Fintype.card I : ℝ) * (Fintype.card T : ℝ)) *
            (((if i₀ ∈ S_I then 1 else 0) - (S_I.card : ℝ) / (Fintype.card I : ℝ)) *
              ((if x_1 ∈ S_T then 1 else 0) - (S_T.card : ℝ) / (Fintype.card T : ℝ))) by
    simpa [eq_comm] using (Fintype.sum_ite_eq (i := i₀)
      (f := fun x : I => ∑ x_1 : T,
            1 / ((Fintype.card I : ℝ) * (Fintype.card T : ℝ)) *
              (((if x ∈ S_I then 1 else 0) - (S_I.card : ℝ) / (Fintype.card I : ℝ)) *
                ((if x_1 ∈ S_T then 1 else 0) - (S_T.card : ℝ) / (Fintype.card T : ℝ)))))]
  rw [show (∑ x_1 : T,
          1 / ((Fintype.card I : ℝ) * (Fintype.card T : ℝ)) *
            (((if i₀ ∈ S_I then 1 else 0) - (S_I.card : ℝ) / (Fintype.card I : ℝ)) *
              ((if x_1 ∈ S_T then 1 else 0) - (S_T.card : ℝ) / (Fintype.card T : ℝ)))) =
      (1 / ((Fintype.card I : ℝ) * (Fintype.card T : ℝ)) *
        ((if i₀ ∈ S_I then 1 else 0) - (S_I.card : ℝ) / (Fintype.card I : ℝ))) *
        (∑ x_1 : T,
          ((if x_1 ∈ S_T then 1 else 0) - (S_T.card : ℝ) / (Fintype.card T : ℝ))) by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro x hx
    ring]
  rw [sum_centered_indicator_mem_real (S := S_T), mul_zero]

private lemma balanced_centered_product_orth_period (S_I : Finset I) (S_T : Finset T)
    (t₀ : T) :
    (balanced (I := I) (T := T)).ip
      (fun s : I × T =>
        ((if s.1 ∈ S_I then (1 : ℝ) else 0) -
            (S_I.card : ℝ) / (Fintype.card I : ℝ)) *
          ((if s.2 ∈ S_T then (1 : ℝ) else 0) -
            (S_T.card : ℝ) / (Fintype.card T : ℝ)))
      (fun r => if r.2 = t₀ then (1 : ℝ) else 0) = 0 := by
  unfold ip
  rw [balanced_observed]
  simp only [balanced_weight, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
    mul_zero, ↓reduceIte]
  rw [Fintype.sum_prod_type]
  simp only
  rw [show (∑ x : I, ∑ x_1 : T,
        if x_1 = t₀ then
          1 / ((Fintype.card I : ℝ) * (Fintype.card T : ℝ)) *
            (((if x ∈ S_I then 1 else 0) - (S_I.card : ℝ) / (Fintype.card I : ℝ)) *
              ((if x_1 ∈ S_T then 1 else 0) - (S_T.card : ℝ) / (Fintype.card T : ℝ)))
        else 0) =
      ∑ x : I,
          1 / ((Fintype.card I : ℝ) * (Fintype.card T : ℝ)) *
            (((if x ∈ S_I then 1 else 0) - (S_I.card : ℝ) / (Fintype.card I : ℝ)) *
              ((if t₀ ∈ S_T then 1 else 0) - (S_T.card : ℝ) / (Fintype.card T : ℝ))) by
    refine Finset.sum_congr rfl ?_
    intro x hx
    simpa [eq_comm] using (Fintype.sum_ite_eq (i := t₀)
      (f := fun t : T =>
            1 / ((Fintype.card I : ℝ) * (Fintype.card T : ℝ)) *
              (((if x ∈ S_I then 1 else 0) - (S_I.card : ℝ) / (Fintype.card I : ℝ)) *
                ((if t ∈ S_T then 1 else 0) - (S_T.card : ℝ) / (Fintype.card T : ℝ)))))]
  rw [show (∑ x : I,
          1 / ((Fintype.card I : ℝ) * (Fintype.card T : ℝ)) *
            (((if x ∈ S_I then 1 else 0) - (S_I.card : ℝ) / (Fintype.card I : ℝ)) *
              ((if t₀ ∈ S_T then 1 else 0) - (S_T.card : ℝ) / (Fintype.card T : ℝ)))) =
      (1 / ((Fintype.card I : ℝ) * (Fintype.card T : ℝ)) *
        ((if t₀ ∈ S_T then 1 else 0) - (S_T.card : ℝ) / (Fintype.card T : ℝ))) *
        (∑ x : I,
          ((if x ∈ S_I then 1 else 0) - (S_I.card : ℝ) / (Fintype.card I : ℝ))) by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro x hx
    ring]
  rw [sum_centered_indicator_mem_real (S := S_I), mul_zero]

/-- For [a subset of units `S_I`](hyp:S_I), [a subset of periods `S_T`](hyp:S_T), and [an
evaluation cell `r`](hyp:r), [under balanced (equal) weights, the two-way-fixed-effect residual
of the product indicator `1{i ∈ S_I}·1{t ∈ S_T}`, evaluated at `r`, factorizes into the product
of the centered unit indicator and the centered period indicator](goal). -/
theorem tildeX_product_indicator_balanced (S_I : Finset I) (S_T : Finset T)
    (r : I × T) :
    (balanced (I := I) (T := T)).tildeX
        Cells.H_twfe
        (fun s : I × T =>
          (if s.1 ∈ S_I then (1 : ℝ) else 0) *
            (if s.2 ∈ S_T then (1 : ℝ) else 0)) r =
      ((if r.1 ∈ S_I then (1 : ℝ) else 0) -
          (S_I.card : ℝ) / (Fintype.card I : ℝ)) *
        ((if r.2 ∈ S_T then (1 : ℝ) else 0) -
          (S_T.card : ℝ) / (Fintype.card T : ℝ)) := by
  classical
  let c : Cells I T := balanced (I := I) (T := T)
  let X : V I T := fun s : I × T =>
    (if s.1 ∈ S_I then (1 : ℝ) else 0) *
      (if s.2 ∈ S_T then (1 : ℝ) else 0)
  let Y : V I T := fun s : I × T =>
    ((if s.1 ∈ S_I then (1 : ℝ) else 0) -
        (S_I.card : ℝ) / (Fintype.card I : ℝ)) *
      ((if s.2 ∈ S_T then (1 : ℝ) else 0) -
        (S_T.card : ℝ) / (Fintype.card T : ℝ))
  let G : V I T := X - Y
  have hG_mem : G ∈ Cells.H_twfe := by
    refine ⟨fun i =>
        ((S_T.card : ℝ) / (Fintype.card T : ℝ)) *
          (if i ∈ S_I then (1 : ℝ) else 0),
      fun t =>
        ((S_I.card : ℝ) / (Fintype.card I : ℝ)) *
          (if t ∈ S_T then (1 : ℝ) else 0) -
        ((S_I.card : ℝ) / (Fintype.card I : ℝ)) *
          ((S_T.card : ℝ) / (Fintype.card T : ℝ)), ?_⟩
    intro p
    by_cases hi : p.1 ∈ S_I <;> by_cases ht : p.2 ∈ S_T <;> simp [G, X, Y, hi, ht] <;>
      ring
  have hXsubG : X - G = Y := by
    ext s
    simp [G]
  have horth : ∀ h ∈ Cells.H_twfe, c.ip (X - G) h = 0 := by
    rw [H_twfe_orthogonal_iff]
    constructor
    · intro i₀
      rw [hXsubG]
      simpa [c, Y] using balanced_centered_product_orth_unit (S_I := S_I) (S_T := S_T) i₀
    · intro t₀
      rw [hXsubG]
      simpa [c, Y] using balanced_centered_product_orth_period (S_I := S_I) (S_T := S_T) t₀
  have hproj : c.proj Cells.H_twfe X r = G r :=
    c.proj_apply_eq_of_mem_orthogonal Cells.H_twfe X hG_mem horth r (by simp [c])
  calc
    c.tildeX Cells.H_twfe X r = (X - c.proj Cells.H_twfe X) r := by simp [Cells.tildeX_eq]
    _ = Y r := by
      rw [Pi.sub_apply, hproj]
      exact congrFun hXsubG r
    _ = ((if r.1 ∈ S_I then (1 : ℝ) else 0) -
          (S_I.card : ℝ) / (Fintype.card I : ℝ)) *
        ((if r.2 ∈ S_T then (1 : ℝ) else 0) -
          (S_T.card : ℝ) / (Fintype.card T : ℝ)) := rfl

end Balanced

end Cells
end Panel
end Causalean

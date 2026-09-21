/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.ML.PartitionPredictor.FinitePartitionPredictor

/-! # Finite-partition predictor ensembles

This file models a fixed-size finite ensemble of `FinitePartitionPredictor`s over
an input type `X`. The public API consists of `PartitionEnsemble`, which stores
one predictor for each index in `Fin T`, and `PartitionEnsemble.eval`, their
uniform average.

The main structural theorem, `PartitionEnsemble.eval_mem_Icc`, states that a
nonempty ensemble preserves pointwise interval bounds: if every member's value
lies in `[a, b]` at every input, then the averaged value also lies in `[a, b]`.
-/

@[expose] public section

namespace Causalean.ML

open BigOperators

/-- A finite-partition predictor ensemble: [one predictor `tree` for each index in
`Fin T`](hyp:tree). -/
structure PartitionEnsemble (X : Type*) (T : ℕ) where
  /-- The ensemble members. -/
  tree : Fin T → FinitePartitionPredictor X

/-- [A finite-partition ensemble prediction](goal) is [the memberwise average](step:1). It
evaluates [an ensemble](hyp:F) with [the specified member count](hyp:T) at
[an input point](hyp:x) in [its domain](hyp:X).

The displayed definition uses reciprocal scaling by the number of ensemble members, including its conventional value when that number is zero. -/
noncomputable def PartitionEnsemble.eval {X : Type*} {T : ℕ} (F : PartitionEnsemble X T) (x : X) : ℝ :=
  (T : ℝ)⁻¹ * ∑ t : Fin T, (F.tree t).eval x

/-- [A nonempty ensemble average preserves common member bounds](goal). For
[the ensemble and evaluation point](hyp:F,x), this follows from
[having at least one member](hyp:hT) and [uniform memberwise bounds at every input](hyp:hb). -/
theorem PartitionEnsemble.eval_mem_Icc {X : Type*} {T : ℕ} (F : PartitionEnsemble X T) (hT : 0 < T)
    {a b : ℝ} (hb : ∀ (t : Fin T) (x : X), (F.tree t).eval x ∈ Set.Icc a b) (x : X) :
    F.eval x ∈ Set.Icc a b := by
  rw [Set.mem_Icc]
  have hTpos : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hTne : (T : ℝ) ≠ 0 := ne_of_gt hTpos
  have hsum_lower : (T : ℝ) * a ≤ ∑ t : Fin T, (F.tree t).eval x := by
    calc
      (T : ℝ) * a = ∑ _t : Fin T, a := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ t : Fin T, (F.tree t).eval x := by
        exact Finset.sum_le_sum (fun t _ => (Set.mem_Icc.mp (hb t x)).1)
  have hsum_upper : ∑ t : Fin T, (F.tree t).eval x ≤ (T : ℝ) * b := by
    calc
      ∑ t : Fin T, (F.tree t).eval x ≤ ∑ _t : Fin T, b := by
        exact Finset.sum_le_sum (fun t _ => (Set.mem_Icc.mp (hb t x)).2)
      _ = (T : ℝ) * b := by
        simp [Finset.sum_const, nsmul_eq_mul]
  constructor
  · have hscale :=
      mul_le_mul_of_nonneg_left hsum_lower (inv_nonneg.mpr (le_of_lt hTpos))
    calc
      a = (T : ℝ)⁻¹ * ((T : ℝ) * a) := by
        field_simp [hTne]
      _ ≤ F.eval x := by
        simpa [PartitionEnsemble.eval] using hscale
  · have hscale :=
      mul_le_mul_of_nonneg_left hsum_upper (inv_nonneg.mpr (le_of_lt hTpos))
    calc
      F.eval x ≤ (T : ℝ)⁻¹ * ((T : ℝ) * b) := by
        simpa [PartitionEnsemble.eval] using hscale
      _ = b := by
        field_simp [hTne]

end Causalean.ML

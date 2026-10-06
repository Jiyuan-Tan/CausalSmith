/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

/-!
# Lipschitz bounds for piecewise profiles

This module turns uniform Lipschitz bounds on consecutive real-valued pieces, together with matching
endpoint values, into a bound across the full ordered chain.
-/

public section

namespace Causalean.Mathlib.Analysis

/-- Given [a finite number of pieces](hyp:k), [a real-valued profile on each piece](hyp:F), and
[a common Lipschitz constant](hyp:C), suppose [every active profile is Lipschitz on the unit
interval](hyp:hlocal) and [consecutive profiles agree at their shared endpoints](hyp:hend). For
[ordered piece indices](hyp:i,j) satisfying [the index order](hyp:hij) and [the upper range
condition](hyp:hjk), and [unit-interval coordinates](hyp:u,v) satisfying [the first coordinate
condition](hyp:hu), [the second coordinate condition](hyp:hv), and [the corresponding global
order](hyp:horder),
[the endpoint-telescoped profile difference is bounded by the common constant times the global
coordinate distance](goal). -/
theorem piecewiseLipschitz_chain_bound (k : ℕ) (F : ℕ → ℝ → ℝ) (C : ℝ)
    (hlocal : ∀ j < k, ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      |F j u - F j v| ≤ C * |u - v|)
    (hend : ∀ j, j + 1 < k → F j 1 = F (j + 1) 0)
    (i j : ℕ) (hij : i ≤ j) (hjk : j < k)
    (u v : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1)
    (horder : (i : ℝ) + u ≤ (j : ℝ) + v) :
    |F i u - F j v| ≤ C * ((j : ℝ) - (i : ℝ) + v - u) := by
  induction j, hij using Nat.le_induction generalizing v with
  | base =>
    have huv : u ≤ v := by linarith
    simpa [abs_of_nonpos (sub_nonpos.mpr huv)] using hlocal i hjk u hu v hv
  | succ j hij ih =>
    have hjk' : j < k := lt_trans (Nat.lt_succ_self j) hjk
    have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
    have hb := ih hjk' 1 (by norm_num) (by linarith [hu.2])
    have he := hend j hjk
    have hl := hlocal (j + 1) hjk 0 (by norm_num) v hv
    rw [zero_sub, abs_neg, abs_of_nonneg hv.1] at hl
    calc
      |F i u - F (j + 1) v| ≤ |F i u - F j 1| + |F j 1 - F (j + 1) v| :=
        abs_sub_le _ _ _
      _ ≤ C * ((j : ℝ) - (i : ℝ) + 1 - u) + C * v := by
        exact add_le_add hb (by simpa only [he] using hl)
      _ = C * (((j + 1 : ℕ) : ℝ) - (i : ℝ) + v - u) := by
        push_cast
        ring

end Causalean.Mathlib.Analysis

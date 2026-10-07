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

/-- Given [a finite number k of pieces](hyp:k), [a real-valued profile F_j on each piece](hyp:F),
and [a common Lipschitz constant C](hyp:C), suppose [each of the first k profiles is C-Lipschitz
on the unit interval](hyp:hlocal) and [consecutive profiles among them agree at their shared
endpoint, F_j(1) = F_(j+1)(0)](hyp:hend). For [piece indices i and j](hyp:i,j) with
[i ≤ j](hyp:hij) and [j < k](hyp:hjk), and [local coordinates u and v](hyp:u,v) with
[u in the unit interval](hyp:hu), [v in the unit interval](hyp:hv), and [global positions ordered
as i + u ≤ j + v](hyp:horder),
[the profile difference |F_i(u) − F_j(v)| is at most C times the global distance
(j + v) − (i + u)](goal). -/
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

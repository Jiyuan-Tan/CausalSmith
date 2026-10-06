/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Convergence of truncated real powers

This file records a reusable equivalence between convergence to zero and convergence after taking
a positive real power and truncating at one.
-/

public section

open Filter
open scoped Topology
namespace Causalean.Mathlib.Analysis.SpecialFunctions

/-- For [a nonnegative real-valued function](hyp:f,hf) and [a positive exponent](hyp:s,hs),
[convergence to zero is equivalent to convergence to zero after taking the real power and truncating
at one](goal). -/
theorem tendsto_min_one_rpow_zero_iff {α : Type*} {l : Filter α}
    (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (s : ℝ) (hs : 0 < s) :
    Tendsto (fun a => min 1 (f a ^ s)) l (𝓝 0) ↔ Tendsto f l (𝓝 0) := by
  constructor
  · intro h
    have hlt : ∀ᶠ a in l, min 1 (f a ^ s) < 1 :=
      h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    have heq : (fun a => min 1 (f a ^ s)) =ᶠ[l] (fun a => f a ^ s) := by
      filter_upwards [hlt] with a ha
      exact min_eq_right (le_of_lt ((min_lt_iff.mp ha).resolve_left (lt_irrefl 1)))
    have hp : Tendsto (fun a => f a ^ s) l (𝓝 0) := h.congr' heq
    have hi := hp.rpow_const (Or.inr (le_of_lt (inv_pos.mpr hs)))
    simpa only [Real.zero_rpow (ne_of_gt (inv_pos.mpr hs)),
      Real.rpow_rpow_inv (hf _) (ne_of_gt hs)] using hi
  · intro h
    have hp := h.rpow_const (Or.inr hs.le)
    have hm := (tendsto_const_nhds (x := (1 : ℝ)) (f := l)).min hp
    simpa only [Real.zero_rpow hs.ne', min_eq_right (by norm_num : (0 : ℝ) ≤ 1)] using hm

end Causalean.Mathlib.Analysis.SpecialFunctions

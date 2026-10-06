/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measurable finite-cover selectors

This module provides the measurable first-hit selector used to turn a finite
cover of side-law space into a decision rule.
-/

public section

open Set

namespace Causalean.Stat.Minimax.FiniteSideInformation

/-- Given a [number of centers](hyp:k) with [positive count](hyp:hk), [centers](hyp:center),
[radii](hyp:radius) that are [positive](hyp:hr), there is a [measurable selector](goal) choosing
a center within its radius at every point covered by the corresponding open balls. -/
theorem exists_measurable_finiteCoverSelector
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (k : ℕ) (hk : 0 < k) (center : Fin k → E) (radius : Fin k → ℝ)
    (hr : ∀ i, 0 < radius i) :
    ∃ select : E → Fin k, Measurable select ∧
      ∀ y, (∃ i, dist y (center i) < radius i) →
        dist y (center (select y)) < radius (select y) := by
  classical
  induction k with
  | zero => omega
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        refine ⟨fun _ => 0, measurable_const, ?_⟩
        intro y hy
        obtain ⟨i, hi⟩ := hy
        simpa [Fin.eq_zero i] using hi
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        obtain ⟨select, hselect_meas, hselect⟩ :=
          ih hnpos (fun i => center i.succ) (fun i => radius i.succ)
            (fun i => hr i.succ)
        let firstBall : Set E := Metric.ball (center 0) (radius 0)
        let result : E → Fin (n + 1) :=
          fun y => if y ∈ firstBall then 0 else (select y).succ
        refine ⟨result, ?_, ?_⟩
        · exact (measurable_const.ite Metric.isOpen_ball.measurableSet
            ((measurable_of_finite fun i : Fin n => i.succ).comp hselect_meas))
        · intro y hy
          by_cases hfirst : y ∈ firstBall
          · have hfirst' : dist y (center 0) < radius 0 := by
              simpa [firstBall, Metric.mem_ball] using hfirst
            simp [result, firstBall, hfirst']
          · have hfirst' : ¬ dist y (center 0) < radius 0 := by
              simpa [firstBall, Metric.mem_ball] using hfirst
            have htail : ∃ i : Fin n,
                dist y (center i.succ) < radius i.succ := by
              obtain ⟨i, hi⟩ := hy
              have hi0 : i ≠ 0 := by
                intro hieq
                subst i
                exact hfirst' hi
              refine ⟨i.pred hi0, ?_⟩
              simpa [Fin.succ_pred i hi0] using hi
            have hs := hselect y htail
            simpa [result, firstBall, hfirst'] using hs

end Causalean.Stat.Minimax.FiniteSideInformation

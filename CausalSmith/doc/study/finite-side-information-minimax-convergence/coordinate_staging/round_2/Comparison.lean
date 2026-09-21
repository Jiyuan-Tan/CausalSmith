/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Minimax.FiniteSideInformation.Fiber
import Mathlib.Analysis.Convex.Jensen

/-!
# Comparison with the exact side-law experiment

This module constructs the exact-law conditional average of an empirical
procedure and applies convexity of squared loss to obtain the lower minimax
comparison.  It also identifies exact-law minimax risk with the supremum of
fiberwise minimax values.
-/

open scoped BigOperators
open Set

namespace Causalean.Stat.Minimax.FiniteSideInformation

variable {Theta X C : Type*} [Fintype X] [Fintype C]

/-- Given [action bounds](hyp:l,u), a [side-sample size](hyp:m), and an [empirical-side procedure](hyp:d),
the [conditional-average exact-side procedure](goal) averages its action over iid samples drawn from the supplied law. -/
noncomputable def conditionalAverageProcedure (l u : ℝ) (m : ℕ)
    (d : EmpiricalSideProcedure X C m l u) : ExactSideProcedure X C l u := by
  intro x w
  refine ⟨∑ z : Fin m → C, productProbability C w z * (d x z : ℝ), ?_, ?_⟩
  · calc
      l = ∑ z : Fin m → C, productProbability C w z * l := by
        rw [← Finset.sum_mul, sum_productProbability, one_mul]
      _ ≤ ∑ z : Fin m → C, productProbability C w z * (d x z : ℝ) := by
        exact Finset.sum_le_sum fun z _ ↦
          mul_le_mul_of_nonneg_left (d x z).2.1 (productProbability_nonneg C w z)
  · calc
      ∑ z : Fin m → C, productProbability C w z * (d x z : ℝ) ≤
          ∑ z : Fin m → C, productProbability C w z * u := by
        exact Finset.sum_le_sum fun z _ ↦
          mul_le_mul_of_nonneg_left (d x z).2.2 (productProbability_nonneg C w z)
      _ = u := by
        rw [← Finset.sum_mul, sum_productProbability, one_mul]

/-- Given [label probabilities](hyp:p), [side coordinates](hyp:q), a [target](hyp:tau),
[simplex-valid probabilities](hyp:hp,hq), [ordered action bounds](hyp:hlu), a [side-sample size](hyp:m),
an [empirical-side procedure](hyp:d), and a [parameter](hyp:theta), [conditional averaging cannot increase squared risk](goal). -/
theorem exactSideRisk_conditionalAverage_le (p : Theta → X → ℝ)
    (q : Theta → C → ℝ) (tau : Theta → ℝ)
    (hp : ∀ theta, p theta ∈ stdSimplex ℝ X)
    (hq : ∀ theta, q theta ∈ stdSimplex ℝ C) (hlu : l ≤ u) (m : ℕ)
    (d : EmpiricalSideProcedure X C m l u) (theta : Theta) :
    exactSideRisk p q hq tau (conditionalAverageProcedure l u m d) theta ≤
      empiricalSideRisk p q hq tau m d theta := by
  have hconvex : ConvexOn ℝ Set.univ (fun a : ℝ ↦ (a - tau theta) ^ 2) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    dsimp
    apply sub_nonneg.mp
    calc
      a * (x - tau theta) ^ 2 + b * (y - tau theta) ^ 2 -
          (a * x + b * y - tau theta) ^ 2 = a * b * (x - y) ^ 2 := by
        have hb' : b = 1 - a := by linarith
        rw [hb']
        ring
      _ ≥ 0 := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x - y))
  unfold exactSideRisk empiricalSideRisk
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ ((hp theta).1 x)
  simpa [conditionalAverageProcedure, smul_eq_mul] using
    (hconvex.map_sum_le
      (t := Finset.univ)
      (w := fun z : Fin m → C ↦ productProbability C (sidePmf q hq theta) z)
      (p := fun z : Fin m → C ↦ (d x z : ℝ))
      (fun z _ ↦ productProbability_nonneg C (sidePmf q hq theta) z)
      (by simpa using sum_productProbability C (sidePmf q hq theta))
      (fun _ _ ↦ Set.mem_univ _))

/-- Given [label probabilities](hyp:p), [side coordinates](hyp:q), a [target](hyp:tau),
[simplex-valid probabilities](hyp:hp,hq), [ordered action bounds](hyp:hlu), a [target in those bounds](hyp:htau),
and a [side-sample size](hyp:m), the [exact-side minimax value is no larger than the empirical-side minimax value](goal). -/
theorem exactSideMinimaxValue_le_empiricalSideMinimaxValue [Nonempty Theta]
    (p : Theta → X → ℝ) (q : Theta → C → ℝ) (tau : Theta → ℝ)
    (hp : ∀ theta, p theta ∈ stdSimplex ℝ X)
    (hq : ∀ theta, q theta ∈ stdSimplex ℝ C)
    (hlu : l ≤ u) (htau : ∀ theta, tau theta ∈ Set.Icc l u) (m : ℕ) :
    exactSideMinimaxValue p q hq tau l u ≤
      empiricalSideMinimaxValue p q hq tau l u m := by
  letI : Nonempty (EmpiricalSideProcedure X C m l u) :=
    ⟨fun _ _ ↦ ⟨l, le_rfl, hlu⟩⟩
  have hexact_nonneg (d : ExactSideProcedure X C l u) (theta : Theta) :
      0 ≤ exactSideRisk p q hq tau d theta := by
    unfold exactSideRisk
    exact Finset.sum_nonneg fun x _ ↦
      mul_nonneg ((hp theta).1 x) (sq_nonneg _)
  unfold exactSideMinimaxValue empiricalSideMinimaxValue
  refine Causalean.Stat.minimaxValue_le_minimaxValue
    (Causalean.Stat.bddBelow_range_worstCaseRisk hexact_nonneg) ?_
  intro d
  refine ⟨conditionalAverageProcedure l u m d, ?_⟩
  apply Causalean.Stat.worstCaseRisk_le
  intro theta
  refine (exactSideRisk_conditionalAverage_le p q tau hp hq hlu m d theta).trans ?_
  apply Causalean.Stat.le_worstCaseRisk
  refine ⟨(u - l) ^ 2, ?_⟩
  rintro _ ⟨theta', rfl⟩
  exact empiricalSideRisk_le p q hp hq tau hlu htau m d theta'

/-- Given [label probabilities](hyp:p), [side coordinates](hyp:q), a [target](hyp:tau),
[simplex-valid probabilities](hyp:hp,hq), [continuous coordinates and target](hyp:hpcont,hqcont,htau),
[ordered action bounds](hyp:hlu), and a [target in those bounds](hyp:htau_mem) on a compact parameter space,
the [exact-side minimax value equals the supremum of fiberwise minimax values](goal). -/
theorem exactSideMinimaxValue_eq_iSup_fiber
    [TopologicalSpace Theta] [CompactSpace Theta] [Nonempty Theta]
    (p : Theta → X → ℝ) (q : Theta → C → ℝ) (tau : Theta → ℝ)
    (hp : ∀ theta, p theta ∈ stdSimplex ℝ X)
    (hq : ∀ theta, q theta ∈ stdSimplex ℝ C)
    (hpcont : ∀ x, Continuous (fun theta ↦ p theta x))
    (hqcont : ∀ c, Continuous (fun theta ↦ q theta c)) (htau : Continuous tau)
    (hlu : l ≤ u) (htau_mem : ∀ theta, tau theta ∈ Set.Icc l u) :
    exactSideMinimaxValue p q hq tau l u =
      ⨆ theta0 : Theta, fiberMinimaxValue p tau q hq l u theta0 := by
  classical
  letI : Nonempty (BoundedDecision X l u) :=
    ⟨fun _ ↦ ⟨l, le_rfl, hlu⟩⟩
  letI : Nonempty (ExactSideProcedure X C l u) :=
    ⟨fun _ _ ↦ ⟨l, le_rfl, hlu⟩⟩
  have hrisk (d : BoundedDecision X l u) (theta : Theta) :
      0 ≤ finiteSquaredRisk p tau d theta ∧
        finiteSquaredRisk p tau d theta ≤ (u - l) ^ 2 :=
    finiteSquaredRisk_bounds p tau (fun theta x ↦ (hp theta).1 x)
      (fun theta ↦ (hp theta).2) hlu htau_mem d theta
  have hexact_nonneg (d : ExactSideProcedure X C l u) (theta : Theta) :
      0 ≤ exactSideRisk p q hq tau d theta := by
    simpa [exactSideRisk, finiteSquaredRisk] using
      (hrisk (fun x ↦ d x (sidePmf q hq theta)) theta).1
  have hexact_le (d : ExactSideProcedure X C l u) (theta : Theta) :
      exactSideRisk p q hq tau d theta ≤ (u - l) ^ 2 := by
    simpa [exactSideRisk, finiteSquaredRisk] using
      (hrisk (fun x ↦ d x (sidePmf q hq theta)) theta).2
  have hfiber_le_exact (theta0 : Theta) :
      fiberMinimaxValue p tau q hq l u theta0 ≤
        exactSideMinimaxValue p q hq tau l u := by
    let fiberRisk := fun (d : BoundedDecision X l u)
      (theta : {theta : Theta // sidePmf q hq theta = sidePmf q hq theta0}) ↦
        finiteSquaredRisk p tau d theta.1
    let exactRisk : ExactSideProcedure X C l u → Theta → ℝ :=
      exactSideRisk p q hq tau
    have hfiber_nonneg : ∀ d theta, 0 ≤ fiberRisk d theta :=
      fun d theta ↦ (hrisk d theta.1).1
    unfold fiberMinimaxValue exactSideMinimaxValue
    refine Causalean.Stat.minimaxValue_le_minimaxValue
      (Causalean.Stat.bddBelow_range_worstCaseRisk hfiber_nonneg) ?_
    intro d
    refine ⟨fun x ↦ d x (sidePmf q hq theta0), ?_⟩
    letI : Nonempty {theta : Theta //
        sidePmf q hq theta = sidePmf q hq theta0} := ⟨⟨theta0, rfl⟩⟩
    apply Causalean.Stat.worstCaseRisk_le
    intro theta
    have hbddExact : BddAbove (Set.range (exactRisk d)) := by
      refine ⟨(u - l) ^ 2, ?_⟩
      rintro _ ⟨theta', rfl⟩
      exact hexact_le d theta'
    simpa [fiberRisk, exactRisk, exactSideRisk, finiteSquaredRisk, theta.property] using
      (Causalean.Stat.le_worstCaseRisk hbddExact theta.1)
  have hexactValue_le : exactSideMinimaxValue p q hq tau l u ≤ (u - l) ^ 2 := by
    let d0 : ExactSideProcedure X C l u := fun _ _ ↦ ⟨l, le_rfl, hlu⟩
    unfold exactSideMinimaxValue
    calc
      Causalean.Stat.minimaxValue (exactSideRisk p q hq tau) ≤
          Causalean.Stat.worstCaseRisk (exactSideRisk p q hq tau) d0 :=
        Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg hexact_nonneg d0
      _ ≤ (u - l) ^ 2 := Causalean.Stat.worstCaseRisk_le (hexact_le d0)
  have hfiber_bdd : BddAbove
      (Set.range (fun theta0 : Theta ↦ fiberMinimaxValue p tau q hq l u theta0)) := by
    refine ⟨(u - l) ^ 2, ?_⟩
    rintro _ ⟨theta0, rfl⟩
    exact (hfiber_le_exact theta0).trans hexactValue_le
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro a ha
    have hfiber_lt (theta0 : Theta) :
        fiberMinimaxValue p tau q hq l u theta0 < a :=
      (le_ciSup hfiber_bdd theta0).trans_lt ha
    have hdecision (theta0 : Theta) : ∃ d : BoundedDecision X l u,
        Causalean.Stat.worstCaseRisk
          (fun (d : BoundedDecision X l u)
            (theta : {theta : Theta // sidePmf q hq theta = sidePmf q hq theta0}) ↦
              finiteSquaredRisk p tau d theta.1) d < a := by
      let fiberRisk := fun (d : BoundedDecision X l u)
        (theta : {theta : Theta // sidePmf q hq theta = sidePmf q hq theta0}) ↦
          finiteSquaredRisk p tau d theta.1
      have hbddBelow : BddBelow
          (Set.range (Causalean.Stat.worstCaseRisk fiberRisk)) :=
        Causalean.Stat.bddBelow_range_worstCaseRisk
          (fun d theta ↦ (hrisk d theta.1).1)
      exact (ciInf_lt_iff hbddBelow).1 (by
        simpa [fiberMinimaxValue, Causalean.Stat.minimaxValue, fiberRisk] using
          hfiber_lt theta0)
    let chosen : Theta → BoundedDecision X l u :=
      fun theta0 ↦ Classical.choose (hdecision theta0)
    have hchosen (theta0 : Theta) :
        Causalean.Stat.worstCaseRisk
          (fun (d : BoundedDecision X l u)
            (theta : {theta : Theta // sidePmf q hq theta = sidePmf q hq theta0}) ↦
              finiteSquaredRisk p tau d theta.1) (chosen theta0) < a :=
      Classical.choose_spec (hdecision theta0)
    let rep : FinitePmf C → Theta := fun w ↦
      if h : ∃ theta, sidePmf q hq theta = w then Classical.choose h
      else Classical.choice inferInstance
    have hrep (w : FinitePmf C) (h : ∃ theta, sidePmf q hq theta = w) :
        sidePmf q hq (rep w) = w := by
      simp only [rep, dif_pos h]
      exact Classical.choose_spec h
    let assembled : ExactSideProcedure X C l u :=
      fun x w ↦ chosen (rep w) x
    have hassembled_lt (theta : Theta) :
        exactSideRisk p q hq tau assembled theta < a := by
      have hs : sidePmf q hq (rep (sidePmf q hq theta)) = sidePmf q hq theta :=
        hrep _ ⟨theta, rfl⟩
      let thetaFiber : {theta' : Theta //
          sidePmf q hq theta' = sidePmf q hq (rep (sidePmf q hq theta))} :=
        ⟨theta, hs.symm⟩
      have hbddFiber : BddAbove (Set.range
          ((fun (d : BoundedDecision X l u)
            (theta' : {theta' : Theta //
                sidePmf q hq theta' = sidePmf q hq (rep (sidePmf q hq theta))}) ↦
              finiteSquaredRisk p tau d theta'.1) (chosen (rep (sidePmf q hq theta))))) := by
        refine ⟨(u - l) ^ 2, ?_⟩
        rintro _ ⟨theta', rfl⟩
        exact (hrisk _ theta'.1).2
      have hpoint := Causalean.Stat.le_worstCaseRisk
        (risk := fun (d : BoundedDecision X l u)
          (theta' : {theta' : Theta //
              sidePmf q hq theta' = sidePmf q hq (rep (sidePmf q hq theta))}) ↦
            finiteSquaredRisk p tau d theta'.1)
        (e := chosen (rep (sidePmf q hq theta))) hbddFiber thetaFiber
      calc
        exactSideRisk p q hq tau assembled theta =
            finiteSquaredRisk p tau (chosen (rep (sidePmf q hq theta))) theta := by
          rfl
        _ ≤ Causalean.Stat.worstCaseRisk
            (fun (d : BoundedDecision X l u)
              (theta' : {theta' : Theta //
                  sidePmf q hq theta' = sidePmf q hq (rep (sidePmf q hq theta))}) ↦
                finiteSquaredRisk p tau d theta'.1)
            (chosen (rep (sidePmf q hq theta))) := by
          simpa [thetaFiber] using hpoint
        _ < a := hchosen (rep (sidePmf q hq theta))
    unfold exactSideMinimaxValue
    calc
      Causalean.Stat.minimaxValue (exactSideRisk p q hq tau) ≤
          Causalean.Stat.worstCaseRisk (exactSideRisk p q hq tau) assembled :=
        Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg hexact_nonneg assembled
      _ ≤ a := Causalean.Stat.worstCaseRisk_le fun theta ↦ (hassembled_lt theta).le
  · exact ciSup_le hfiber_le_exact

end Causalean.Stat.Minimax.FiniteSideInformation

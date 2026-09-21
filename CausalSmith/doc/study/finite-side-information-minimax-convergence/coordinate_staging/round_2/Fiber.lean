/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Minimax.FiniteSideInformation.Experiments
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Compact shrinking-fiber minimax values

This module isolates the compactness argument saying that minimax values over
shrinking neighborhoods of an observed side law converge to the minimax value
over its exact fiber.
-/

open Filter Topology Set

namespace Causalean.Stat.Minimax.FiniteSideInformation

open Causalean.Stat

variable {Theta X C : Type*} [TopologicalSpace Theta] [CompactSpace Theta]
  [Nonempty Theta] [Fintype X] [Fintype C]

/-- Given [label probabilities](hyp:p), a [target](hyp:tau), [side coordinates](hyp:q),
[simplex validity](hyp:hq), [action bounds](hyp:l,u), and a [center parameter](hyp:theta0), the
[exact-fiber local minimax value](goal) minimizes risk over decisions and maximizes over parameters with the same side law. -/
noncomputable def fiberMinimaxValue (p : Theta → X → ℝ) (tau : Theta → ℝ)
    (q : Theta → C → ℝ) (hq : ∀ theta, q theta ∈ stdSimplex ℝ C)
    (l u : ℝ) (theta0 : Theta) : ℝ :=
  minimaxValue (fun (d : BoundedDecision X l u)
    (theta : {theta : Theta // sidePmf q hq theta = sidePmf q hq theta0}) ↦
      finiteSquaredRisk p tau d theta.1)

/-- Given [label probabilities](hyp:p), a [target](hyp:tau), [side coordinates](hyp:q),
[simplex validity](hyp:hq), [action bounds and a radius](hyp:l,u,r), and a [center parameter](hyp:theta0),
the [local minimax value](goal) minimizes risk over decisions and maximizes over parameters whose side law is nearby. -/
noncomputable def localMinimaxValue (p : Theta → X → ℝ) (tau : Theta → ℝ)
    (q : Theta → C → ℝ) (hq : ∀ theta, q theta ∈ stdSimplex ℝ C)
    (l u r : ℝ) (theta0 : Theta) : ℝ :=
  minimaxValue (fun (d : BoundedDecision X l u)
    (theta : {theta : Theta // dist (sidePmf q hq theta) (sidePmf q hq theta0) ≤ r}) ↦
      finiteSquaredRisk p tau d theta.1)

/-- Given [label probabilities](hyp:p), [side coordinates](hyp:q), a [target](hyp:tau),
[simplex-valid probabilities](hyp:hp,hq), [continuous coordinates and target](hyp:hpcont,hqcont,htau),
[ordered action bounds](hyp:hlu), a [target in those bounds](hyp:htau_mem), and a [center parameter](hyp:theta0)
in a compact parameter space, [local minimax values converge to the exact-fiber minimax value](goal)
as their side-law radii shrink. -/
theorem localMinimaxValue_tendsto_fiber (p : Theta → X → ℝ)
    (q : Theta → C → ℝ) (tau : Theta → ℝ)
    (hp : ∀ theta, p theta ∈ stdSimplex ℝ X)
    (hq : ∀ theta, q theta ∈ stdSimplex ℝ C)
    (hpcont : ∀ x, Continuous (fun theta ↦ p theta x))
    (hqcont : ∀ c, Continuous (fun theta ↦ q theta c)) (htau : Continuous tau)
    (hlu : l ≤ u) (htau_mem : ∀ theta, tau theta ∈ Set.Icc l u) (theta0 : Theta) :
    Tendsto (fun n : ℕ ↦ localMinimaxValue p tau q hq l u (1 / (n + 1 : ℝ)) theta0)
      atTop (nhds (fiberMinimaxValue p tau q hq l u theta0)) := by
  -- Proof plan: compactness gives convergent subsequences of near-optimal bounded decisions and
  -- parameters; continuity identifies every zero-radius cluster point with the exact fiber.
  -- A direct epsilon proof is also available and avoids choosing exact minimizers: restriction
  -- gives `fiberMinimaxValue ≤ localMinimaxValue`; choose a decision whose exact-fiber
  -- worst-case risk is within `ε / 2` of the infimum.  The strict sublevel set of its continuous
  -- risk contains the compact exact fiber.  Compactness of the complementary parameter set and
  -- continuity of `sidePmf` then give a positive side-law radius whose inverse image lies in that
  -- sublevel set.  Eventually `1 / (n + 1)` is below this radius, yielding the reverse epsilon
  -- bound.  `finiteSquaredRisk_bounds` supplies every conditional-completeness side condition.
  letI : Nonempty (BoundedDecision X l u) :=
    ⟨fun _ ↦ ⟨l, le_rfl, hlu⟩⟩
  have hrisk (d : BoundedDecision X l u) (theta : Theta) :
      0 ≤ finiteSquaredRisk p tau d theta ∧
        finiteSquaredRisk p tau d theta ≤ (u - l) ^ 2 :=
    finiteSquaredRisk_bounds p tau (fun theta x ↦ (hp theta).1 x)
      (fun theta ↦ (hp theta).2) hlu htau_mem d theta
  have hfiber_le_local (r : ℝ) (hr : 0 ≤ r) :
      fiberMinimaxValue p tau q hq l u theta0 ≤
        localMinimaxValue p tau q hq l u r theta0 := by
    unfold fiberMinimaxValue localMinimaxValue
    refine minimaxValue_mono_class_of_nonneg
      (fun theta ↦ ⟨theta.1, ?_⟩) ?_ ?_ ?_ ?_
    · simpa [theta.property] using hr
    · exact fun d theta ↦ (hrisk d theta.1).1
    · exact fun d theta ↦ (hrisk d theta.1).1
    · intro d
      refine ⟨(u - l) ^ 2, ?_⟩
      rintro _ ⟨theta, rfl⟩
      exact (hrisk d theta.1).2
    · exact fun _ _ ↦ le_rfl
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [] with n
    exact ha.trans_le (hfiber_le_local _ (by positivity))
  · intro b hb
    let c := (fiberMinimaxValue p tau q hq l u theta0 + b) / 2
    have hvalue_lt_c : fiberMinimaxValue p tau q hq l u theta0 < c := by
      dsimp [c]
      linarith
    have hc_lt_b : c < b := by
      dsimp [c]
      linarith
    let fiberRisk := fun (d : BoundedDecision X l u)
      (theta : {theta : Theta // sidePmf q hq theta = sidePmf q hq theta0}) ↦
        finiteSquaredRisk p tau d theta.1
    have hnonnegFiber : ∀ d theta, 0 ≤ fiberRisk d theta :=
      fun d theta ↦ (hrisk d theta.1).1
    have hbddBelow : BddBelow (Set.range (worstCaseRisk fiberRisk)) :=
      bddBelow_range_worstCaseRisk hnonnegFiber
    have hvalue : (⨅ d, worstCaseRisk fiberRisk d) < c := by
      simpa [fiberMinimaxValue, minimaxValue, fiberRisk] using hvalue_lt_c
    obtain ⟨d, hd⟩ := (ciInf_lt_iff hbddBelow).1 hvalue
    have hbddFiber : BddAbove (Set.range (fiberRisk d)) := by
      refine ⟨(u - l) ^ 2, ?_⟩
      rintro _ ⟨theta, rfl⟩
      exact (hrisk d theta.1).2
    have hfiberRisk_lt (theta : Theta)
        (htheta : sidePmf q hq theta = sidePmf q hq theta0) :
        finiteSquaredRisk p tau d theta < c := by
      exact (le_worstCaseRisk hbddFiber ⟨theta, htheta⟩).trans_lt hd
    let bad : Set Theta := {theta | c ≤ finiteSquaredRisk p tau d theta}
    have hbadClosed : IsClosed bad := by
      change IsClosed ((fun theta ↦ finiteSquaredRisk p tau d theta) ⁻¹' Set.Ici c)
      exact isClosed_Ici.preimage (continuous_finiteSquaredRisk p tau hpcont htau d)
    have hbadCompact : IsCompact bad := hbadClosed.isCompact
    have hsideCont : Continuous (sidePmf q hq) := continuous_sidePmf q hq hqcont
    have himageClosed : IsClosed (sidePmf q hq '' bad) :=
      (hbadCompact.image hsideCont).isClosed
    have hcenterNotImage : sidePmf q hq theta0 ∉ sidePmf q hq '' bad := by
      rintro ⟨theta, hthetaBad, hthetaSide⟩
      exact (not_lt_of_ge hthetaBad) (hfiberRisk_lt theta hthetaSide)
    have himageComplNhds : (sidePmf q hq '' bad)ᶜ ∈ nhds (sidePmf q hq theta0) :=
      himageClosed.isOpen_compl.mem_nhds hcenterNotImage
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 himageComplNhds
    have hnear (theta : Theta)
        (htheta : dist (sidePmf q hq theta) (sidePmf q hq theta0) < δ) :
        finiteSquaredRisk p tau d theta < c := by
      by_contra hnot
      have hthetaBad : theta ∈ bad := by
        simpa [bad] using le_of_not_gt hnot
      have hthetaImage : sidePmf q hq theta ∈ sidePmf q hq '' bad :=
        ⟨theta, hthetaBad, rfl⟩
      have hthetaBall : sidePmf q hq theta ∈ Metric.ball (sidePmf q hq theta0) δ := by
        simpa [Metric.mem_ball, dist_comm] using htheta
      exact (hball hthetaBall) hthetaImage
    have hradius : ∀ᶠ n : ℕ in atTop, 1 / (n + 1 : ℝ) < δ :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually_lt_const hδ
    filter_upwards [hradius] with n hn
    haveI : Nonempty {theta : Theta //
        dist (sidePmf q hq theta) (sidePmf q hq theta0) ≤ 1 / (n + 1 : ℝ)} :=
      ⟨⟨theta0, by simp only [dist_self]; positivity⟩⟩
    let localRisk : BoundedDecision X l u →
        {theta : Theta //
          dist (sidePmf q hq theta) (sidePmf q hq theta0) ≤ 1 / (n + 1 : ℝ)} → ℝ :=
      fun d theta ↦ finiteSquaredRisk p tau d theta.1
    change minimaxValue localRisk < b
    have hlocalNonneg : ∀ d theta, 0 ≤ localRisk d theta := by
      intro d theta
      exact (hrisk d theta.1).1
    calc
      minimaxValue localRisk ≤ worstCaseRisk localRisk d :=
        minimaxValue_le_worstCaseRisk_of_nonneg hlocalNonneg d
      _ < b := (worstCaseRisk_le fun theta ↦
        (hnear theta.1 (theta.2.trans_lt hn)).le).trans_lt hc_lt_b

end Causalean.Stat.Minimax.FiniteSideInformation

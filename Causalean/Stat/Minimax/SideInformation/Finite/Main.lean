/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Minimax.SideInformation.Finite.Approximation

/-!
# Finite side-information minimax convergence

This module proves that bounded squared-loss minimax values based on finitely
many iid observations from a finite side law converge to the minimax value in
the experiment that reveals that side-law vector exactly.
-/

public section

open Filter Topology Set

namespace Causalean.Stat.Minimax.FiniteSideInformation

/-- For a [compact parameter space](hyp:Theta), [finite labeled and finite nonempty side
alphabets](hyp:X,C), [continuous simplex-valid label and side probabilities](hyp:hp,hq,hpcont,hqcont),
and a [continuous target contained in an ordered bounded action interval](hyp:htau,hlu,htau_mem),
the [bounded squared-loss empirical-side minimax values converge to the exact-side minimax
benchmark](goal) as the iid side sample size tends to infinity. -/
theorem finiteSideInfo_minimax_tendsto
    {Theta X C : Type*} [TopologicalSpace Theta] [CompactSpace Theta] [Nonempty Theta]
    [Fintype X] [Fintype C] [DecidableEq C] [Nonempty C]
    (p : Theta → X → ℝ) (q : Theta → C → ℝ) (tau : Theta → ℝ)
    (hp : ∀ theta, p theta ∈ stdSimplex ℝ X)
    (hq : ∀ theta, q theta ∈ stdSimplex ℝ C)
    (hpcont : ∀ x, Continuous (fun theta ↦ p theta x))
    (hqcont : ∀ c, Continuous (fun theta ↦ q theta c)) (htau : Continuous tau)
    (hlu : l ≤ u) (htau_mem : ∀ theta, tau theta ∈ Set.Icc l u) :
    Tendsto (fun m : ℕ ↦ empiricalSideMinimaxValue p q hq tau l u m) atTop
      (nhds (exactSideMinimaxValue p q hq tau l u)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun m ↦
      ha.trans_le
        (exactSideMinimaxValue_le_empiricalSideMinimaxValue
          p q tau hp hq hlu htau_mem m)
  · intro b hb
    have hemp_nonneg (m : ℕ) (d : EmpiricalSideProcedure X C m l u) (theta : Theta) :
        0 ≤ empiricalSideRisk p q hq tau m d theta :=
      empiricalSideRisk_nonneg p q hp hq tau m d theta
    have hminimax_le (m : ℕ) :
        empiricalSideMinimaxValue p q hq tau l u m ≤ (u - l) ^ 2 := by
      let d0 : EmpiricalSideProcedure X C m l u := fun _ _ ↦ ⟨l, le_rfl, hlu⟩
      have hbdd (d : EmpiricalSideProcedure X C m l u) :
          BddAbove (Set.range (empiricalSideRisk p q hq tau m d)) := by
        refine ⟨(u - l) ^ 2, ?_⟩
        rintro _ ⟨theta, rfl⟩
        exact empiricalSideRisk_le p q hp hq tau hlu htau_mem m d theta
      have hbridge := minimaxValueENNRealOfReal_toReal_of_nonneg_of_bddAbove
        (hemp_nonneg m) hbdd
      unfold empiricalSideMinimaxValue
      change Causalean.Stat.minimaxValueReal (empiricalSideRisk p q hq tau m) ≤
        (u - l) ^ 2
      calc
        Causalean.Stat.minimaxValueReal (empiricalSideRisk p q hq tau m) ≤
            Causalean.Stat.worstCaseRiskReal (empiricalSideRisk p q hq tau m) d0 :=
          Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg (hemp_nonneg m) d0
        _ ≤ (u - l) ^ 2 := Causalean.Stat.worstCaseRisk_le fun theta ↦
          empiricalSideRisk_le p q hp hq tau hlu htau_mem m d0 theta
    have hbounded : Filter.IsBoundedUnder (fun x y : ℝ ↦ x ≤ y) atTop
        (fun m : ℕ ↦ empiricalSideMinimaxValue p q hq tau l u m) :=
      Filter.isBoundedUnder_of_eventually_le (Filter.Eventually.of_forall hminimax_le)
    exact Filter.eventually_lt_of_limsup_lt
      ((empiricalSideMinimax_limsup_le_exact
        p q tau hp hq hpcont hqcont htau hlu htau_mem).trans_lt hb) hbounded

end Causalean.Stat.Minimax.FiniteSideInformation

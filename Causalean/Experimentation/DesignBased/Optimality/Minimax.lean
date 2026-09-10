/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Minimax designs and regret

When the risk of a design depends on an unknown *state of nature* `y` (e.g. the finite population's
potential-outcome table), the experimenter ranks designs by their **worst-case risk** over a family
of states.  This file defines the worst-case risk of a design over a nonempty finite set of states,
the **minimax** design (one minimizing the worst-case risk in a family), and the **regret** of a
design at a state (its risk minus the best risk achievable in the family there).  Minimax existence
over a finite design family is immediate from the generic optimal-design existence theorem applied
to the worst-case-risk criterion.
-/

import Causalean.Experimentation.DesignBased.Optimality

/-! # Minimax design criteria

Minimax designs minimize worst-case risk over a finite family of states of nature.

The definition `worstRisk` takes the maximum of `R y D` over a nonempty finite state set, and
`IsMinimaxOn` asks a design to minimize that criterion inside a design family. The theorem
`exists_isMinimaxOn` inherits finite-family existence from `exists_isOptimalOn`. The declarations
`bestRisk`, `regret`, and `regret_nonneg` formalize statewise regret relative to the best design
available in the same finite family.
-/

open scoped BigOperators

namespace Causalean
namespace Experimentation
namespace DesignBased

variable {Ω : Type*} [Fintype Ω] {Y : Type*}

/-- For [a finite set of states of nature](hyp:s) that [is nonempty](hyp:hs), [a risk criterion
indexed by states and randomization designs](hyp:R), and [a randomization design](hyp:D), [the
worst-case risk](goal) is the largest risk incurred by that design as the state ranges over the
given set, provided risk values admit pairwise least upper bounds. -/
noncomputable def worstRisk {α : Type*} [SemilatticeSup α] (s : Finset Y) (hs : s.Nonempty)
    (R : Y → FiniteDesign Ω → α) (D : FiniteDesign Ω) : α :=
  s.sup' hs (fun y => R y D)

/-- The worst-case risk dominates the risk at every state in the family. -/
lemma le_worstRisk {α : Type*} [SemilatticeSup α] (s : Finset Y) (hs : s.Nonempty)
    (R : Y → FiniteDesign Ω → α) (D : FiniteDesign Ω) {y : Y} (hy : y ∈ s) :
    R y D ≤ worstRisk s hs R D :=
  Finset.le_sup' (fun y => R y D) hy

/-- For [a family of randomization designs](hyp:𝒟), [a finite set of states of nature](hyp:s) that
[is nonempty](hyp:hs), [a risk criterion indexed by states and randomization designs](hyp:R), and
[a candidate randomization design](hyp:D₀), [the minimax condition](goal) holds precisely when
[the candidate belongs to the family](step:1) and [its worst-case risk over the state set is no
greater than that of every design in the family](step:2), provided risk values admit pairwise
least upper bounds. -/
def IsMinimaxOn (𝒟 : DesignFamily Ω) (s : Finset Y) (hs : s.Nonempty)
    {α : Type*} [SemilatticeSup α]
    (R : Y → FiniteDesign Ω → α) (D₀ : FiniteDesign Ω) : Prop :=
  D₀ ∈ 𝒟 ∧ ∀ D ∈ 𝒟, worstRisk s hs R D₀ ≤ worstRisk s hs R D

/-- **Existence of a minimax design.** For a design family `𝒟` and a risk criterion `R` indexed by
states of nature, if [the state set `s` is nonempty](hyp:hs), [the design family `𝒟` is
finite](hyp:hfin), and [`𝒟` is nonempty](hyp:hne), then [there exists a design in `𝒟` that is
minimax — it minimizes the worst-case risk over `s` among all members of `𝒟`](goal). Immediate
from `exists_isOptimalOn` applied to the worst-case-risk criterion. -/
theorem exists_isMinimaxOn (𝒟 : DesignFamily Ω) (s : Finset Y) (hs : s.Nonempty)
    {α : Type*} [LinearOrder α]
    (R : Y → FiniteDesign Ω → α) (hfin : 𝒟.Finite) (hne : 𝒟.Nonempty) :
    ∃ D₀, IsMinimaxOn 𝒟 s hs R D₀ :=
  exists_isOptimalOn 𝒟 (worstRisk s hs R) hfin hne

/-- For [a family of randomization designs](hyp:𝒟) that [is finite](hyp:hfin) and [nonempty](hyp:hne),
[a risk criterion indexed by states and randomization designs](hyp:R), and [a state of nature](hyp:y),
[the best achievable risk](goal) is the least risk at that state among designs in the family,
provided risk values are linearly ordered.

It is defined through a chosen minimizing design; the subsequent comparison lemmas characterize
the resulting value. -/
noncomputable def bestRisk {α : Type*} [LinearOrder α] (𝒟 : DesignFamily Ω) (hfin : 𝒟.Finite)
    (hne : 𝒟.Nonempty) (R : Y → FiniteDesign Ω → α) (y : Y) : α :=
  R y (Classical.choose (exists_isOptimalOn 𝒟 (R y) hfin hne))

/-- The best achievable risk is attained, hence no larger than the risk of any family member. -/
lemma bestRisk_le {α : Type*} [LinearOrder α] (𝒟 : DesignFamily Ω) (hfin : 𝒟.Finite)
    (hne : 𝒟.Nonempty) (R : Y → FiniteDesign Ω → α) (y : Y) {D : FiniteDesign Ω}
    (hD : D ∈ 𝒟) :
    bestRisk 𝒟 hfin hne R y ≤ R y D :=
  (Classical.choose_spec (exists_isOptimalOn 𝒟 (R y) hfin hne)).2 D hD

/-- For [a family of randomization designs](hyp:𝒟) that [is finite](hyp:hfin) and [nonempty](hyp:hne),
[a risk criterion indexed by states and randomization designs](hyp:R), [a state of nature](hyp:y),
and [a randomization design](hyp:D), [the design's regret](goal) is its risk at that state minus
the least risk achievable there within the family, provided risk values form a linearly ordered
additive group whose order is preserved by right addition. -/
noncomputable def regret (𝒟 : DesignFamily Ω) (hfin : 𝒟.Finite) (hne : 𝒟.Nonempty)
    {α : Type*} [AddGroup α] [LinearOrder α] [AddRightMono α]
    (R : Y → FiniteDesign Ω → α) (y : Y) (D : FiniteDesign Ω) : α :=
  R y D - bestRisk 𝒟 hfin hne R y

/-- Regret is nonnegative for every member of the family. -/
lemma regret_nonneg (𝒟 : DesignFamily Ω) (hfin : 𝒟.Finite) (hne : 𝒟.Nonempty)
    {α : Type*} [AddGroup α] [LinearOrder α] [AddRightMono α]
    (R : Y → FiniteDesign Ω → α) (y : Y) {D : FiniteDesign Ω} (hD : D ∈ 𝒟) :
    0 ≤ regret 𝒟 hfin hne R y D :=
  sub_nonneg.mpr (bestRisk_le 𝒟 hfin hne R y hD)

end DesignBased
end Experimentation
end Causalean

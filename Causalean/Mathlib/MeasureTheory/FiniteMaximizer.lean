/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Mathlib.Data.List.MinMax
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Measurable Maximizers for Finite Real-Valued Classes

This file gives a deterministic, measurably tie-broken maximizer for a nonempty
finite family of real-valued measurable functions. The construction is generic
measurable-selection infrastructure and does not depend on concentration theory.
-/

@[expose] public section

open MeasureTheory

namespace Causalean.Mathlib.MeasureTheory

universe u v

/-- Given [a score family `score`](hyp:score), [an initial index `a`](hyp:a), and a list of
remaining indices, the [finite maximizer fold](goal) returns its selected-index
function and selected-score function: [an empty list retains the initial index](step:1), while
[a nonempty list compares the initial score with the recursively selected tail score](step:2). -/
noncomputable def listMaximizerPair {Omega : Type u} {I : Type v}
    (score : I → Omega → ℝ) (a : I) : List I → (Omega → I) × (Omega → ℝ)
  | [] => (fun _ => a, score a)
  | b :: rest =>
      let tail := listMaximizerPair score b rest
      (fun omega => if score a omega < tail.2 omega then tail.1 omega else a,
        fun omega => if score a omega < tail.2 omega then tail.2 omega else score a omega)

private lemma listMaximizerPair_spec {Omega : Type u} {I : Type v}
    (score : I → Omega → ℝ) (a : I) (rest : List I) (omega : Omega) :
    let selected := (listMaximizerPair score a rest).1 omega
    let value := (listMaximizerPair score a rest).2 omega
    value = score selected omega ∧ ∀ i ∈ a :: rest, score i omega ≤ value := by
  induction rest generalizing a with
  | nil => simp [listMaximizerPair]
  | cons b rest ih =>
      let tail := listMaximizerPair score b rest
      have htail := ih b
      change
        (if score a omega < tail.2 omega then tail.2 omega else score a omega) =
            score (if score a omega < tail.2 omega then tail.1 omega else a) omega ∧
          ∀ i ∈ a :: b :: rest, score i omega ≤
            (if score a omega < tail.2 omega then tail.2 omega else score a omega)
      by_cases hlt : score a omega < tail.2 omega
      · simp only [if_pos hlt]
        constructor
        · exact htail.1
        · intro i hi
          simp only [List.mem_cons] at hi
          rcases hi with rfl | hi
          · exact hlt.le
          · exact htail.2 i (by simpa using hi)
      · simp only [if_neg hlt]
        constructor
        · trivial
        · intro i hi
          simp only [List.mem_cons] at hi
          rcases hi with rfl | hi
          · exact le_rfl
          · exact (htail.2 i (by simpa using hi)).trans (le_of_not_gt hlt)

private lemma measurable_listMaximizerPair {Omega : Type u} {I : Type v}
    [MeasurableSpace Omega] (score : I → Omega → ℝ)
    (hscore : ∀ i, Measurable (score i)) (a : I) (rest : List I) :
    @Measurable Omega I _ ⊤ (listMaximizerPair score a rest).1 ∧
      Measurable (listMaximizerPair score a rest).2 := by
  induction rest generalizing a with
  | nil => exact ⟨measurable_const, hscore a⟩
  | cons b rest ih =>
      let tail := listMaximizerPair score b rest
      have htail := ih b
      have hset : MeasurableSet {omega | score a omega < tail.2 omega} :=
        measurableSet_lt (hscore a) htail.2
      constructor
      · exact htail.1.ite hset measurable_const
      · exact htail.2.ite hset (hscore a)

/-- Given [a nonempty finite index type `I`](hyp:I) and [a real-valued score family
`score`](hyp:score), the [finite-class maximizer](goal) is the index selected by a fixed fold
through the finite enumeration, retaining the earlier index when scores tie. -/
noncomputable def finiteClassMaximizer {Omega : Type u} (I : Type v)
    [Fintype I] [Nonempty I] (score : I → Omega → ℝ) : Omega → I :=
  (listMaximizerPair score (Classical.choice ‹Nonempty I›) Finset.univ.toList).1

/-- If [every score in a nonempty finite family is measurable](hyp:hscore), then [its selected
finite-class maximizer is measurable into the discrete measurable index space](goal). -/
@[fun_prop]
theorem measurable_finiteClassMaximizer
    {Omega : Type u} {I : Type v} [MeasurableSpace Omega] [Fintype I] [Nonempty I]
    {score : I → Omega → ℝ} (hscore : ∀ i, Measurable (score i)) :
    @Measurable Omega I _ ⊤ (finiteClassMaximizer I score) := by
  unfold finiteClassMaximizer
  exact (measurable_listMaximizerPair score hscore
    (Classical.choice ‹Nonempty I›) Finset.univ.toList).1

/-- For [a nonempty finite score family `score`](hyp:score), [every member's score is at most
the score at the selected finite-class maximizer](goal). -/
theorem finiteClassMaximizer_spec
    {Omega : Type u} {I : Type v} [Fintype I] [Nonempty I]
    (score : I → Omega → ℝ) (omega : Omega) (i : I) :
    score i omega ≤ score (finiteClassMaximizer I score omega) omega := by
  let a := Classical.choice ‹Nonempty I›
  have hspec := listMaximizerPair_spec score a Finset.univ.toList omega
  have hi : i ∈ a :: Finset.univ.toList := by simp
  change score i omega ≤
    score ((listMaximizerPair score a Finset.univ.toList).1 omega) omega
  rw [← hspec.1]
  exact hspec.2 i hi

end Causalean.Mathlib.MeasureTheory

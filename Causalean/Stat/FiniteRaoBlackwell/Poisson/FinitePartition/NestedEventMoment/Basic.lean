module
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Basic
public import Causalean.Stat.UStatistic.OrderM.Basic

/-!
# Counts of nested events and their ordered-tuple expansion

This module defines event counts in a finite sample and a weighted falling
factorial. The key combinatorial statement expands that statistic as a sum over
injective ordered tuples, with the first point in the smaller event and every
remaining point in the larger event.
-/

@[expose] public section

open MeasureTheory

namespace Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat

variable {X : Type*} [MeasurableSpace X]

/-- A [finite sample](hyp:s) and an [event](hyp:A) determine the [event count](goal),
given by filtering all sample positions for membership and taking the resulting cardinality
(step:1). -/
noncomputable def eventCount (s : FiniteSample X) (A : Set X) : ℕ := by
  classical
  exact (Finset.univ.filter fun i : Fin s.count => s.points i ∈ A).card

/-- Two [events](hyp:A,B), an [order](hyp:v), and a [finite sample](hyp:s) determine
the [weighted nested-event factorial count](goal), given by the smaller-event count
times the falling factorial of one fewer larger-event observations (step:1). -/
noncomputable def weightedFactorial (A B : Set X) (v : ℕ)
    (s : FiniteSample X) : ℝ :=
  (eventCount s A : ℝ) * ((eventCount s B - 1).descFactorial (v - 1) : ℝ)

/-- Two [events](hyp:A,B), an [order](hyp:v) with [positive order](hyp:hv), and an
[ordered observation tuple](hyp:x) determine the [nested-event kernel](goal), given by
one when its first observation is in the first event and all remaining observations are
in the second event, and zero otherwise (step:1). -/
noncomputable def nestedEventKernel (A B : Set X) (v : ℕ) (hv : 1 ≤ v)
    (x : Fin v → X) : ℝ := by
  classical
  exact if x ⟨0, hv⟩ ∈ A ∧ ∀ j : Fin v, j.val ≠ 0 → x j ∈ B then 1 else 0

/-- Fixing the first entry of an injective tuple leaves an embedding into the
remaining permitted positions. -/
private theorem card_injectiveTuples_first (k n : ℕ) (s : Finset (Fin n))
    (i : Fin n) (hi : i ∈ s) :
    ((injectiveTuples (k + 1) n).filter
      (fun t => t 0 = i ∧ ∀ j : Fin k, t j.succ ∈ s)).card =
      (s.card - 1).descFactorial k := by
  classical
  let T := (injectiveTuples (k + 1) n).filter
      (fun t => t 0 = i ∧ ∀ j : Fin k, t j.succ ∈ s)
  let E := Fin k ↪ (s.erase i : Finset (Fin n))
  have hcongr : T.card = Fintype.card E := by
    let e : T ≃ E := {
      toFun := fun t =>
        ⟨fun j => ⟨t.1 j.succ, by
          have hp : t.1 ∈ injectiveTuples (k + 1) n ∧
              (t.1 0 = i ∧ ∀ j : Fin k, t.1 j.succ ∈ s) := by
            simpa only [T, Finset.mem_filter] using t.2
          have ht : Function.Injective t.1 := by
            simpa [injectiveTuples] using hp.1
          have hfirst : t.1 0 = i := hp.2.1
          have hne : t.1 j.succ ≠ i := by
            intro he
            have : j.succ = (0 : Fin (k + 1)) := ht (he.trans hfirst.symm)
            exact Fin.succ_ne_zero j this
          exact Finset.mem_erase.mpr ⟨hne, hp.2.2 j⟩⟩,
          by
            have hp : t.1 ∈ injectiveTuples (k + 1) n ∧
                (t.1 0 = i ∧ ∀ j : Fin k, t.1 j.succ ∈ s) := by
              simpa only [T, Finset.mem_filter] using t.2
            intro a b hab
            have ht : Function.Injective t.1 := by
              simpa [injectiveTuples] using hp.1
            exact Fin.succ_inj.mp (ht (congrArg Subtype.val hab))⟩
      invFun := fun f => ⟨Fin.cons i (fun j => (f j).1), by
        simp only [T, Finset.mem_filter]
        constructor
        · simp only [injectiveTuples, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [Fin.cons_injective_iff]
          constructor
          · rintro ⟨j, hj⟩
            have hmem := (f j).2
            simp only [Finset.mem_erase] at hmem
            exact hmem.1 hj
          · exact fun a b hab => f.injective (Subtype.ext hab)
        · simp only [Fin.cons_zero, Fin.cons_succ, true_and]
          intro j
          exact (Finset.mem_erase.mp (f j).2).2⟩
      left_inv := by
        intro t
        have hp : t.1 ∈ injectiveTuples (k + 1) n ∧
            (t.1 0 = i ∧ ∀ j : Fin k, t.1 j.succ ∈ s) := by
          simpa only [T, Finset.mem_filter] using t.2
        apply Subtype.ext
        funext j
        refine Fin.cases ?_ ?_ j
        · exact hp.2.1.symm
        · intro a
          rfl
      right_inv := by
        intro f
        apply Function.Embedding.ext
        intro j
        apply Subtype.ext
        rfl }
    simpa [E] using (Fintype.card_congr e)
  rw [show ((injectiveTuples (k + 1) n).filter
      (fun t => t 0 = i ∧ ∀ j : Fin k, t j.succ ∈ s)).card = T.card by rfl,
    hcongr, show Fintype.card E = (s.erase i).card.descFactorial k by
      simpa only [E, Fintype.card_fin, Fintype.card_coe] using
        (Fintype.card_embedding_eq (α := Fin k)
        (β := (s.erase i : Finset (Fin n))))]
  rw [Finset.card_erase_of_mem hi]

/-- Given [two events](hyp:A,B) with [the first contained in the second](hyp:hAB), an
[order](hyp:v) with [positive order](hyp:hv), a [sample size](hyp:n), and [fixed
observations](hyp:x), the [weighted nested-event factorial equals the sum of the
nested-event kernel over injective ordered position tuples](goal). -/
theorem weightedFactorial_eq_injectiveTupleSum (A B : Set X)
    (hAB : A ⊆ B) (v n : ℕ) (hv : 1 ≤ v) (x : Fin n → X) :
    weightedFactorial A B v (fixedSizeEmbed n x) =
      ∑ t ∈ injectiveTuples v n,
        nestedEventKernel A B v hv (fun j => x (t j)) := by
  classical
  cases v with
  | zero => omega
  | succ k =>
    let sA : Finset (Fin n) := Finset.univ.filter (fun i => x i ∈ A)
    let sB : Finset (Fin n) := Finset.univ.filter (fun i => x i ∈ B)
    have htail (t : Fin (k + 1) → Fin n) :
        (∀ j : Fin (k + 1), j.val ≠ 0 → x (t j) ∈ B) ↔
          ∀ j : Fin k, x (t j.succ) ∈ B := by
      constructor
      · intro h j
        exact h j.succ (by simp)
      · intro h j hj
        induction j using Fin.cases with
        | zero => exact False.elim (hj rfl)
        | succ a => exact h a
    have hinner (i : Fin n) :
        (∑ t ∈ (injectiveTuples (k + 1) n).filter (fun t => t 0 = i),
          nestedEventKernel A B (k + 1) hv (fun j => x (t j))) =
        if x i ∈ A then ((sB.card - 1).descFactorial k : ℝ) else 0 := by
      by_cases hiA : x i ∈ A
      · have hiB : i ∈ sB := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAB hiA⟩
        simp only [hiA, ite_true]
        have hpoint : ∀ t ∈ (injectiveTuples (k + 1) n).filter (fun t => t 0 = i),
            nestedEventKernel A B (k + 1) hv (fun j => x (t j)) =
              if ∀ j : Fin k, x (t j.succ) ∈ B then 1 else 0 := by
          intro t ht
          have hfirst : t 0 = i := (Finset.mem_filter.mp ht).2
          change (if x (t 0) ∈ A ∧
              (∀ j : Fin (k + 1), j.val ≠ 0 → x (t j) ∈ B) then (1 : ℝ) else 0) = _
          simp only [hfirst, hiA, true_and, htail]
        rw [Finset.sum_congr rfl hpoint]
        rw [Finset.sum_boole]
        have hfilt : ((injectiveTuples (k + 1) n).filter (fun t => t 0 = i)).filter
            (fun t => ∀ j : Fin k, x (t j.succ) ∈ B) =
            (injectiveTuples (k + 1) n).filter
              (fun t => t 0 = i ∧ ∀ j : Fin k, t j.succ ∈ sB) := by
          ext t
          simp [sB, Finset.filter_filter]
        rw [hfilt, card_injectiveTuples_first k n sB i hiB]
      · simp only [hiA, ite_false]
        apply Finset.sum_eq_zero
        intro t ht
        have hfirst : t 0 = i := (Finset.mem_filter.mp ht).2
        simp [nestedEventKernel, hfirst, hiA]
    have hsum :
        (∑ t ∈ injectiveTuples (k + 1) n,
          nestedEventKernel A B (k + 1) hv (fun j => x (t j))) =
        ∑ i : Fin n, if x i ∈ A then ((sB.card - 1).descFactorial k : ℝ) else 0 := by
      calc
        _ = ∑ i : Fin n, ∑ t ∈ (injectiveTuples (k + 1) n).filter (fun t => t 0 = i),
              nestedEventKernel A B (k + 1) hv (fun j => x (t j)) :=
          (Finset.sum_fiberwise (injectiveTuples (k + 1) n)
            (fun t => t 0) (fun t => nestedEventKernel A B (k + 1) hv
              (fun j => x (t j)))).symm
        _ = _ := by simp only [hinner]
    rw [hsum]
    change (sA.card : ℝ) * ((sB.card - 1).descFactorial k : ℝ) =
      ∑ i : Fin n, if x i ∈ A then ((sB.card - 1).descFactorial k : ℝ) else 0
    rw [← Finset.sum_filter]
    change (sA.card : ℝ) * ((sB.card - 1).descFactorial k : ℝ) =
      ∑ _i ∈ sA, ((sB.card - 1).descFactorial k : ℝ)
    simp

end Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment

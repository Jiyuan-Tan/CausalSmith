module
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Ordering finite traces of arbitrary nested families

A nested family, even with an uncountable index type, induces a finite
chain of observation traces. One permutation makes all traces prefixes,
including duplicate observations and traces empty or equal to the full sample.
This combinatorial statement is independent of sign laws and Doob estimates.
-/

public section

namespace Causalean.Stat.EmpiricalProcess.Countable

/-- If [a family of sets](hyp:B) is [nested, any two members being
comparable by inclusion](hyp:hchain), then for [any finite sample](hyp:x)
[there is a permutation of the sample positions after which the
observations lying in each member of the family form an initial
segment](goal).

Ties and repeated observations are retained.
-/
theorem nested_trace_prefix {Ω ι : Type*} (B : ι → Set Ω)
    (hchain : ∀ i k, B i ⊆ B k ∨ B k ⊆ B i) {n : ℕ} (x : Fin n → Ω) :
    ∃ p : Equiv.Perm (Fin n), ∀ i, ∃ k : Fin (n + 1),
      ∀ j : Fin n, x (p j) ∈ B i ↔ j.val < k.val := by
  classical
  let trace : ι → Finset (Fin n) := fun i => Finset.univ.filter (fun j => x j ∈ B i)
  let T := Finset.univ.powerset.filter (fun s : Finset (Fin n) => ∃ i, trace i = s)
  let absent := fun j : Fin n => T.filter (fun s => j ∉ s)
  let rank := fun j => (absent j).card
  have hrank : ∀ i a b, x a ∈ B i → x b ∉ B i → rank a < rank b := by
    intro i a b ha hb
    have hsub : absent a ⊆ absent b := by
      intro s hs
      obtain ⟨hsT, has⟩ := Finset.mem_filter.mp hs
      obtain ⟨k, rfl⟩ := (Finset.mem_filter.mp hsT).2
      refine Finset.mem_filter.mpr ⟨hsT, ?_⟩
      simp only [trace, Finset.mem_filter, Finset.mem_univ, true_and] at has ⊢
      rcases hchain k i with hki | hik
      · exact fun hbk => hb (hki hbk)
      · exact (has (hik ha)).elim
    have hmem : trace i ∈ absent b := by
      simp only [absent, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · simp [T, Finset.mem_powerset, Finset.subset_univ]
      · simpa [trace] using hb
    have hnmem : trace i ∉ absent a := by
      simp [absent, trace, ha]
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
    intro heq
    exact hnmem (heq.symm ▸ hmem)
  let p := Tuple.sort rank
  have hdown : ∀ i (j k : Fin n), j ≤ k → x (p k) ∈ B i → x (p j) ∈ B i := by
    intro i j k hjk hk
    by_contra hj
    have hlt := hrank i (p k) (p j) hk hj
    have hle := Tuple.monotone_sort rank hjk
    exact (not_lt_of_ge hle) hlt
  refine ⟨p, fun i => ?_⟩
  let S := Finset.univ.filter (fun j : Fin n => x (p j) ∈ B i)
  have hcard : S.card ≤ n := by
    simpa using Finset.card_le_card (Finset.filter_subset (fun j => x (p j) ∈ B i) Finset.univ)
  refine ⟨⟨S.card, Nat.lt_succ_of_le hcard⟩, fun j => ?_⟩
  change x (p j) ∈ B i ↔ j.val < S.card
  constructor
  · intro hj
    have hsub : Finset.Iic j ⊆ S := by
      intro k hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdown i k j (Finset.mem_Iic.mp hk) hj⟩
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hc
    exact Nat.lt_of_succ_le hc
  · intro hj
    by_contra hnot
    have hsub : S ⊆ Finset.Iio j := by
      intro k hk
      apply Finset.mem_Iio.mpr
      by_contra hkj
      exact hnot (hdown i j k (le_of_not_gt hkj) (Finset.mem_filter.mp hk).2)
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hc
    exact (not_lt_of_ge hc) hj

end Causalean.Stat.EmpiricalProcess.Countable

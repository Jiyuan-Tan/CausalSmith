module
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Count-vector degree reindexing

Regrouping of a real series indexed by a pair (t, c), with t a natural number and c a vector of
natural-number counts on a finite index set I, according to the combined degree s = t + ∑ᵢ cᵢ.
The pairs are in bijection with triples (s, r, c) where r ≤ s and c is a count vector of total r
(so t = s − r). For a nonnegative summand, summability of the degree-grouped series
s ↦ ∑_{r ≤ s} ∑_{|c| = r} f(s − r, c) implies summability of the original series, and for a
summable series the total sum equals the sum of the degree-grouped series.

## Main definitions

* `countTaylorDegreeEquiv` — the bijection between pairs (t, c) and triples (s, r, c) with |c| = r,
  r ≤ s.

## Main results

* `countTaylorDegree_fiber_sum` — the sum over one degree fibre is the finite double sum over r ≤ s
  and count vectors of total r.
* `summable_countTaylor_of_degree` — a nonnegative series is summable once its degree grouping is.
* `tsum_countTaylor_eq_degree` — a summable series has the same total as its degree grouping.
-/

@[expose] public section

noncomputable section

namespace Causalean.Mathlib.Algebra.BigOperators.NatAntidiagonal

/-- For a [finite coordinate type](hyp:I), reindex a Taylor order and count vector
by their combined degree, the observed degree, and the count vector in the
corresponding antidiagonal fiber. The result is [the equivalence that groups Taylor/count pairs by combined degree](goal). -/
noncomputable def countTaylorDegreeEquiv (I : Type*) [Fintype I] [DecidableEq I] :
    (ℕ × (I → ℕ)) ≃
      Σ s : ℕ, Σ r : Fin (s + 1),
        ↥((Finset.univ : Finset I).piAntidiag r.val) := by
  classical
  refine
    { toFun := fun x => ⟨x.1 + ∑ i, x.2 i,
        ⟨∑ i, x.2 i, by omega⟩,
        ⟨x.2, Finset.mem_piAntidiag.mpr ⟨rfl, by simp⟩⟩⟩
      invFun := fun x => (x.1 - x.2.1.val, x.2.2.val)
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    simp
  · rintro ⟨s, ⟨r, hr⟩, ⟨c, hc'⟩⟩
    have hc : ∑ i, c i = r := (Finset.mem_piAntidiag.mp hc').1
    dsimp only
    subst r
    have hs : s - (∑ i, c i) + (∑ i, c i) = s := by omega
    generalize ht : s - (∑ i, c i) = t at *
    subst s
    rfl

/-- For a [count-vector summand](hyp:f) and [combined degree](hyp:s), summing over
the reindexed fiber equals the finite sum over observed degrees and their count
antidiagonals. The result is [the equality between a reindexed fiber sum and its antidiagonal sum](goal). -/
lemma countTaylorDegree_fiber_sum {I : Type*} [Fintype I] [DecidableEq I]
    (f : ℕ → (I → ℕ) → ℝ) (s : ℕ) :
    (∑ x : Σ r : Fin (s + 1), ↥((Finset.univ : Finset I).piAntidiag r.val),
      f (s - x.1.val) x.2.val) =
      ∑ r ∈ Finset.range (s + 1),
        ∑ c ∈ (Finset.univ : Finset I).piAntidiag r, f (s - r) c := by
  classical
  rw [Fintype.sum_sigma]
  simp_rw [Finset.sum_coe_sort]
  exact Fin.sum_univ_eq_sum_range
    (fun r => ∑ c ∈ (Finset.univ : Finset I).piAntidiag r, f (s - r) c) (s + 1)

/-- For a [nonnegative Taylor/count summand](hyp:f,hf), if its [combined-degree
grouping is summable](hyp:hs), then the original series over Taylor orders and
count vectors is summable. The result is [summability of the original Taylor/count series](goal). -/
lemma summable_countTaylor_of_degree {I : Type*} [Fintype I] [DecidableEq I]
    (f : ℕ → (I → ℕ) → ℝ) (hf : ∀ t c, 0 ≤ f t c)
    (hs : Summable (fun s : ℕ => ∑ r ∈ Finset.range (s + 1),
      ∑ c ∈ (Finset.univ : Finset I).piAntidiag r, f (s - r) c)) :
    Summable (fun x : ℕ × (I → ℕ) => f x.1 x.2) := by
  classical
  let F : (Σ s : ℕ, Σ r : Fin (s + 1),
      ↥((Finset.univ : Finset I).piAntidiag r.val)) → ℝ :=
    fun x => f (x.1 - x.2.1.val) x.2.2.val
  have hF : Summable F := by
    apply (summable_sigma_of_nonneg (fun x => hf _ _)).mpr
    constructor
    · intro s
      exact summable_of_hasFiniteSupport (Set.toFinite _)
    · simpa only [F, tsum_fintype, countTaylorDegree_fiber_sum] using hs
  exact (countTaylorDegreeEquiv I).symm.summable_iff.mp hF

/-- For a [summable Taylor/count series](hyp:f,hf), its total sum equals the
iterated sum grouped by combined degree, observed degree, and count-vector
antidiagonal. The result is [the equality between the original total sum and its combined-degree grouping](goal). -/
lemma tsum_countTaylor_eq_degree {I : Type*} [Fintype I] [DecidableEq I]
    (f : ℕ → (I → ℕ) → ℝ)
    (hf : Summable (fun x : ℕ × (I → ℕ) => f x.1 x.2)) :
    (∑' x : ℕ × (I → ℕ), f x.1 x.2) =
      ∑' s : ℕ, ∑ r ∈ Finset.range (s + 1),
        ∑ c ∈ (Finset.univ : Finset I).piAntidiag r, f (s - r) c := by
  classical
  let F : (Σ s : ℕ, Σ r : Fin (s + 1),
      ↥((Finset.univ : Finset I).piAntidiag r.val)) → ℝ :=
    fun x => f (x.1 - x.2.1.val) x.2.2.val
  have hF : Summable F := (countTaylorDegreeEquiv I).symm.summable_iff.mpr hf
  calc
    _ = ∑' x, F x := ((countTaylorDegreeEquiv I).symm.tsum_eq _).symm
    _ = _ := by
      rw [hF.tsum_sigma]
      simp only [F, tsum_fintype, countTaylorDegree_fiber_sum]



end Causalean.Mathlib.Algebra.BigOperators.NatAntidiagonal

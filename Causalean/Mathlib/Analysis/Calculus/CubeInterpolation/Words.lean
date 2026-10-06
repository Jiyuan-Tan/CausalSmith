module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Counts
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Multiindex
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.List.Permutation

/-!
# Word fibers and multinomial grouping

Coordinate words are grouped by their multiplicity vectors at arbitrary order.
These results are combinatorial: no smoothness, degree-two restriction, or
Taylor realization is a premise. The grouped-sum lemma is the interface used
by the Taylor layer.

The word count and factorial quotient conventions agree with the primary
multinomial definition and formula https://dlmf.nist.gov/26.4#i and
https://dlmf.nist.gov/26.4.E2, including admissible empty coordinate sets.
-/

@[expose] public section

open scoped BigOperators
noncomputable section
namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- The [word fiber](goal) for [a word length k](hyp:k) and [a vector of coordinate counts](hyp:κ)
is [the finite set of all length-k coordinate words in which each coordinate occurs exactly as
often as its count prescribes](step:1). -/
def wordFiber {d : ℕ} (k : ℕ) (κ : Fin d → ℕ) : Finset (Fin k → Fin d) :=
  Finset.univ.filter fun w => coordCount w = κ

/-- For [a coordinate word of length k](hyp:w), [its coordinate counts have total order k](goal). -/
theorem coordCount_order {d k : ℕ} (w : Fin k → Fin d) :
    multiOrder (coordCount w) = k := by
  simpa [multiOrder, coordCount] using
    Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Fin k)) (Finset.univ : Finset (Fin d)) w

/-- For [a vector of coordinate counts](hyp:κ), [each coordinate occurs in the sorted word exactly
as often as its count prescribes](goal). -/
theorem sortedWord_count {d : ℕ} (κ : Fin d → ℕ) :
    coordCount (sortedWord κ) = κ := by
  funext i
  let v : List.Vector (Fin d) (multiOrder κ) := ⟨countList κ, countList_length κ⟩
  have hcount : coordCount (sortedWord κ) i = (countList κ).count i := by
    have hv : v.get = sortedWord κ := by
      funext r
      rfl
    change (Finset.univ.filter fun r => sortedWord κ r = i).card = _
    rw [← hv]
    exact Fin.card_filter_univ_eq_vector_get_eq_count i v
  rw [hcount]
  simp [countList, List.count_flatten, List.map_ofFn, List.sum_ofFn,
    List.count_replicate, beq_iff_eq]

/-- [Two coordinate words of the same length](hyp:v,w) [have the same coordinate counts exactly
when one is obtained from the other by permuting positions](goal). -/
theorem coordCount_eq_iff_perm {d k : ℕ} (v w : Fin k → Fin d) :
    coordCount v = coordCount w ↔ ∃ σ : Equiv.Perm (Fin k), v = w ∘ σ := by
  -- List.ofFn translates count equality into List.Perm. Its position bijection
  -- gives the permutation; the reverse direction reindexes finite fibers.
  -- Alternatively, Equiv.ofFiberEquiv and Equiv.ofFiberEquiv_map assemble
  -- coordinate-fiber equivalences obtained from equal finite cardinalities.
  classical
  constructor
  · intro h
    have hc (i : Fin d) : Fintype.card {r // v r = i} =
        Fintype.card {r // w r = i} := by
      simpa [Fintype.card_subtype, coordCount] using congrFun h i
    let e (i : Fin d) : {r // v r = i} ≃ {r // w r = i} :=
      Fintype.equivOfCardEq (hc i)
    exact ⟨Equiv.ofFiberEquiv e, funext fun r => (Equiv.ofFiberEquiv_map e r).symm⟩
  · rintro ⟨σ, rfl⟩
    funext i
    have hc := Fintype.card_congr (σ.subtypeEquiv
      (p := fun r => (w ∘ σ) r = i) (q := fun r => w r = i) (by intro r; rfl))
    simpa [Fintype.card_subtype, coordCount] using hc

/-- For [a vector of coordinate counts](hyp:κ) [whose total order is k](hyp:hκ), [the number of
length-k words with those counts is k factorial divided by the product of the factorials of the
counts](goal). -/
theorem word_fiber_card_eq_multinomial {d k : ℕ} (κ : Fin d → ℕ)
    (hκ : multiOrder κ = k) :
    (wordFiber k κ).card = k.factorial / multiFactorial κ := by
  classical
  let a : Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm κ
  have ha : a.sum (fun _ n => n) = k := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    exact hκ
  have hcoeff (w : Fin k → Fin d) :
      MvPolynomial.coeff a (∏ r, (MvPolynomial.X (w r) : MvPolynomial (Fin d) ℕ)) =
        if coordCount w = κ then 1 else 0 := by
    have hp : (∏ r, (MvPolynomial.X (w r) : MvPolynomial (Fin d) ℕ)) =
        ∏ i, MvPolynomial.X i ^ coordCount w i := by
      simpa [coordCount] using
        (Finset.prod_fiberwise' (Finset.univ : Finset (Fin k)) w
          (fun i => (MvPolynomial.X i : MvPolynomial (Fin d) ℕ))).symm
    rw [hp, MvPolynomial.coeff_prod_X_pow]
    have he : a = Finsupp.indicator Finset.univ (fun i _ => coordCount w i) ↔
        coordCount w = κ := by
      constructor
      · intro h
        funext i
        simpa [a, Finsupp.indicator_apply] using (congrArg (fun b => b i) h).symm
      · intro h
        ext i
        simp [a, Finsupp.indicator_apply, h]
    simp only [he]
  have hc := MvPolynomial.coeff_sum_X_pow_of_fintype (R := ℕ) a k
  rw [if_pos ha, Fintype.sum_pow, MvPolynomial.coeff_sum] at hc
  simp_rw [hcoeff] at hc
  rw [Finset.sum_boole] at hc
  rw [Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)] at hc
  simpa [wordFiber, Nat.multinomial, ← hκ, multiOrder, multiFactorial, a] using hc

/-- For [a vector of coordinate counts](hyp:κ) [whose total order is k](hyp:hκ), [the number of
length-k words with those counts, multiplied by the product of the factorials of the counts, equals
k factorial](goal). -/
theorem word_fiber_card_mul_factorial {d k : ℕ} (κ : Fin d → ℕ)
    (hκ : multiOrder κ = k) :
    (wordFiber k κ).card * multiFactorial κ = k.factorial := by
  rw [word_fiber_card_eq_multinomial κ hκ]
  have h := Nat.multinomial_spec Finset.univ κ
  simpa [Nat.multinomial, ← hκ, multiOrder, multiFactorial, Nat.mul_comm] using h

/-- For [a coordinate word](hyp:w) and [a real vector z](hyp:z), [the product of the coordinates of
z selected along the word equals the product over coordinates of each coordinate of z raised to the
number of times it occurs in the word](goal). -/
theorem word_product_eq_count_product {d k : ℕ} (w : Fin k → Fin d)
    (z : Fin d → ℝ) :
    (∏ r, z (w r)) = ∏ i, z i ^ coordCount w i := by
  simpa [coordCount] using
    (Finset.prod_fiberwise' (Finset.univ : Finset (Fin k)) w z).symm

/-- For [a real function of length-k coordinate words](hyp:F) that [takes equal values on words
with the same coordinate counts](hyp:hF), [its sum over all words equals the sum over count vectors
of total order k of the multinomial number k factorial over the product of count factorials, times
the function's value at the sorted word of that count vector](goal). -/
theorem group_word_sum_by_count {d k : ℕ} (F : (Fin k → Fin d) → ℝ)
    (hF : ∀ v w, coordCount v = coordCount w → F v = F w) :
    (∑ w, F w) = ∑ κ : ExactIndex d k,
      ((k.factorial / multiFactorial κ.1 : ℕ) : ℝ) * F (sortedWordOfOrder κ) := by
  classical
  let count : (Fin k → Fin d) → ExactIndex d k :=
    fun w => ⟨coordCount w, coordCount_order w⟩
  have hs (κ : ExactIndex d k) : coordCount (sortedWordOfOrder κ) = κ.1 := by
    rcases κ with ⟨κ, hκ⟩
    subst k
    have hw : sortedWordOfOrder ⟨κ, rfl⟩ = sortedWord κ := by
      funext r
      rfl
    rw [hw]
    exact sortedWord_count κ
  rw [← Finset.sum_fiberwise Finset.univ count F]
  apply Finset.sum_congr rfl
  intro κ _
  have hf : (Finset.univ.filter fun w => count w = κ) = wordFiber k κ.1 := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, wordFiber]
    exact Subtype.ext_iff
  rw [hf]
  calc
    ∑ w ∈ wordFiber k κ.1, F w = ∑ _w ∈ wordFiber k κ.1, F (sortedWordOfOrder κ) := by
      apply Finset.sum_congr rfl
      intro w hw
      apply hF
      exact (Finset.mem_filter.mp hw).2.trans (hs κ).symm
    _ = ((wordFiber k κ.1).card : ℝ) * F (sortedWordOfOrder κ) := by simp
    _ = _ := by rw [word_fiber_card_eq_multinomial κ.1 κ.2]

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation


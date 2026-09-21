
open scoped BigOperators

variable {σ κ : Type*}

/-- For [a real multivariate polynomial](hyp:p), its [real zero locus](goal) is the set of real
assignments at which the polynomial evaluates to zero. -/
def mvPolynomialZeroLocus (p : MvPolynomial σ ℝ) : Set (σ → ℝ) :=
  {x | MvPolynomial.eval x p = 0}

/-- For [a finite set of polynomial indices](hyp:s) and [an indexed family of real multivariate
polynomials](hyp:p), the [zero locus of their product equals the union of their zero loci](goal). -/
theorem mvPolynomialZeroLocus_finset_prod
    (s : Finset κ) (p : κ → MvPolynomial σ ℝ) :
    mvPolynomialZeroLocus (∏ i ∈ s, p i) =
      ⋃ i ∈ s, mvPolynomialZeroLocus (p i) := by
  ext x
  simp only [mvPolynomialZeroLocus, Set.mem_ofPred_eq, MvPolynomial.eval_prod,
    Finset.prod_eq_zero_iff]
  simp

/-- If [every factor in a finite indexed family of real multivariate polynomials is nonzero](hyp:h),
then [their finite product is nonzero](goal). -/
theorem mvPolynomial_finset_prod_ne_zero
    (s : Finset κ) (p : κ → MvPolynomial σ ℝ)
    (h : ∀ i ∈ s, p i ≠ 0) :
    (∏ i ∈ s, p i) ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr h

/-- For [a finite-type-indexed family of real multivariate polynomials](hyp:p), the [zero locus
of the product over all indices equals the union of all factor zero loci](goal). -/
theorem mvPolynomialZeroLocus_fintype_prod [Fintype κ]
    (p : κ → MvPolynomial σ ℝ) :
    mvPolynomialZeroLocus (∏ i, p i) = ⋃ i, mvPolynomialZeroLocus (p i) := by
  simpa using mvPolynomialZeroLocus_finset_prod (Finset.univ) p

/-- If [every member of a finite-type-indexed family of real multivariate polynomials is
nonzero](hyp:h), then [the product over the whole index type is nonzero](goal). -/
theorem mvPolynomial_fintype_prod_ne_zero [Fintype κ]
    (p : κ → MvPolynomial σ ℝ) (h : ∀ i, p i ≠ 0) :
    (∏ i, p i) ≠ 0 := by
  apply mvPolynomial_finset_prod_ne_zero Finset.univ p
  simpa using h

/-- Given [a finite set of indices](hyp:s) and [a polynomial for every member of its finite
subtype](hyp:p), the [zero locus of the subtype product equals the union of the subtype-indexed
zero loci](goal). -/
theorem mvPolynomialZeroLocus_subtype_prod
    (s : Finset κ) (p : {i // i ∈ s} → MvPolynomial σ ℝ) :
    mvPolynomialZeroLocus (∏ i, p i) = ⋃ i, mvPolynomialZeroLocus (p i) := by
  exact mvPolynomialZeroLocus_fintype_prod p

/-- Given [a finite set of indices](hyp:s), [a polynomial for every member of its finite subtype](hyp:p),
and [a proof that every factor is nonzero](hyp:h), the [product of the subtype-indexed factors is
nonzero](goal). -/
theorem mvPolynomial_subtype_prod_ne_zero
    (s : Finset κ) (p : {i // i ∈ s} → MvPolynomial σ ℝ)
    (h : ∀ i, p i ≠ 0) :
    (∏ i, p i) ≠ 0 := by
  exact mvPolynomial_fintype_prod_ne_zero p h

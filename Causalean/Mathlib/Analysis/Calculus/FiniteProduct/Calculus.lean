module
public import Causalean.Mathlib.Analysis.Calculus.FiniteProduct.Basic

/-!
# Coordinate derivative certification for the explicit finite jets

The local hypotheses are exactly the supplied coordinate chains. The two elementary
insertion identities and two single-summand derivative rules isolate the bookkeeping
from differentiation of the outer finite sums. No higher first-coordinate derivatives
or mixed-coordinate interchange theorem is used.
-/

public section

open scoped BigOperators
noncomputable section

namespace Causalean.Mathlib.Analysis.Calculus.FiniteProduct

variable {ι : Type*} [DecidableEq ι]

/-- For [factor jets J of a finite index set I](hyp:I,J), [hit lists xs and ys](hyp:xs,ys) and
[a point (a, u)](hyp:a,u), if [an index k](hyp:k) [belongs to I](hyp:hk), then [prepending k to
the first-coordinate hit list turns the Leibniz summand into the factor jet of k with its
first-coordinate order raised by one, times the unchanged jets of the other factors](goal). -/
theorem leibnizTerm_cons_a (I : Finset ι) (J : FactorJets ι) (xs ys : List ι)
    (k : ι) (a u : ℝ) (hk : k ∈ I) :
    leibnizTerm I J (k :: xs) ys a u =
      factorJet J k (xs.count k + 1) (ys.count k) a u *
        ∏ i ∈ I.erase k, factorJet J i (xs.count i) (ys.count i) a u := by
  unfold leibnizTerm
  rw [← Finset.mul_prod_erase I _ hk]
  simp only [List.count_cons, beq_self_eq_true, ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hne : k ≠ i := (Finset.mem_erase.mp hi).1.symm
  simp [hne]

/-- For [factor jets J of a finite index set I](hyp:I,J), [hit lists xs and ys](hyp:xs,ys) and
[a point (a, u)](hyp:a,u), if [an index k](hyp:k) [belongs to I](hyp:hk), then [prepending k to
the second-coordinate hit list turns the Leibniz summand into the factor jet of k with its
second-coordinate order raised by one, times the unchanged jets of the other factors](goal). -/
theorem leibnizTerm_cons_u (I : Finset ι) (J : FactorJets ι) (xs ys : List ι)
    (k : ι) (a u : ℝ) (hk : k ∈ I) :
    leibnizTerm I J xs (k :: ys) a u =
      factorJet J k (xs.count k) (ys.count k + 1) a u *
        ∏ i ∈ I.erase k, factorJet J i (xs.count i) (ys.count i) a u := by
  unfold leibnizTerm
  rw [← Finset.mul_prod_erase I _ hk]
  simp only [List.count_cons, beq_self_eq_true, ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hne : k ≠ i := (Finset.mem_erase.mp hi).1.symm
  simp [hne]

omit [DecidableEq ι] in
/-- If [the factor jets J of a finite index set I have the first-coordinate derivative chains at a
point (a, u)](hyp:I,J,a,u,h), then for [every index i of I](hyp:i,hi) and [every first-coordinate
order p](hyp:p) [at most one](hyp:hp), [the factor jet of i at orders (p, 0), as a function of
the first coordinate, has derivative at a equal to its jet at orders (p + 1, 0)](goal). -/
theorem hasDerivAt_factorJet_a (I : Finset ι) (J : FactorJets ι) (a u : ℝ)
    (h : AChainsAt I J a u) (i : ι) (hi : i ∈ I) (p : ℕ) (hp : p ≤ 1) :
    HasDerivAt (fun b => factorJet J i p 0 b u)
      (factorJet J i (p + 1) 0 a u) a := by
  obtain rfl | rfl : p = 0 ∨ p = 1 := by omega
  · exact h.da00 i hi
  · exact h.da10 i hi

omit [DecidableEq ι] in
/-- If [the factor jets J of a finite index set I have the second-coordinate derivative chains at a
point (a, u)](hyp:I,J,a,u,h), then for [every index i of I](hyp:i,hi) and orders
[p and q](hyp:p,q) with [p at most two](hyp:hp) and [q at most one](hyp:hq), [the factor jet of i
at orders (p, q), as a function of the second coordinate, has derivative at u equal to its jet at
orders (p, q + 1)](goal). -/
theorem hasDerivAt_factorJet_u (I : Finset ι) (J : FactorJets ι) (a u : ℝ)
    (h : UChainsAt I J a u) (i : ι) (hi : i ∈ I)
    (p q : ℕ) (hp : p ≤ 2) (hq : q ≤ 1) :
    HasDerivAt (fun v => factorJet J i p q a v)
      (factorJet J i p (q + 1) a u) u := by
  obtain rfl | rfl | rfl : p = 0 ∨ p = 1 ∨ p = 2 := by omega
  · obtain rfl | rfl : q = 0 ∨ q = 1 := by omega
    · exact h.du00 i hi
    · exact h.du01 i hi
  · obtain rfl | rfl : q = 0 ∨ q = 1 := by omega
    · exact h.du10 i hi
    · exact h.du11 i hi
  · obtain rfl | rfl : q = 0 ∨ q = 1 := by omega
    · exact h.du20 i hi
    · exact h.du21 i hi

/-- If [the factor jets J of a finite index set I have the first-coordinate derivative chains at a
point (a, u)](hyp:I,J,a,u,h) and [a first-coordinate hit list xs](hyp:xs) has [at most one
entry](hyp:hlen), then [the Leibniz summand with hits xs and no second-coordinate hits, as a
function of the first coordinate, has derivative at a equal to the sum over k in I of the summand
with k prepended to xs](goal). -/
theorem hasDerivAt_leibnizTerm_a (I : Finset ι) (J : FactorJets ι)
    (xs : List ι) (a u : ℝ) (h : AChainsAt I J a u) (hlen : xs.length ≤ 1) :
    HasDerivAt (fun b => leibnizTerm I J xs [] b u)
      (∑ k ∈ I, leibnizTerm I J (k :: xs) [] a u) a := by
  have hd := HasDerivAt.fun_finsetProd (fun i hi =>
    hasDerivAt_factorJet_a I J a u h i hi (xs.count i)
      ((List.count_le_length).trans hlen))
  have hs : (∑ k ∈ I, leibnizTerm I J (k :: xs) [] a u) =
      ∑ k ∈ I, (∏ i ∈ I.erase k, factorJet J i (xs.count i) 0 a u) •
        factorJet J k (xs.count k + 1) 0 a u := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [leibnizTerm_cons_a I J xs [] k a u hk]
    simp only [List.count_nil, smul_eq_mul, mul_comm]
  rw [← hs] at hd
  exact hd

/-- If [the factor jets J of a finite index set I have the second-coordinate derivative chains at a
point (a, u)](hyp:I,J,a,u,h), and [a first-coordinate hit list](hyp:xs) has [at most two
entries](hyp:hxs) and [a second-coordinate hit list](hyp:ys) has [at most one entry](hyp:hys),
then [the Leibniz summand, as a function of the second coordinate, has derivative at u equal to
the sum over k in I of the summand with k prepended to the second-coordinate list](goal). -/
theorem hasDerivAt_leibnizTerm_u (I : Finset ι) (J : FactorJets ι)
    (xs ys : List ι) (a u : ℝ) (h : UChainsAt I J a u)
    (hxs : xs.length ≤ 2) (hys : ys.length ≤ 1) :
    HasDerivAt (fun v => leibnizTerm I J xs ys a v)
      (∑ k ∈ I, leibnizTerm I J xs (k :: ys) a u) u := by
  have hd := HasDerivAt.fun_finsetProd (fun i hi =>
    hasDerivAt_factorJet_u I J a u h i hi (xs.count i) (ys.count i)
      ((List.count_le_length).trans hxs) ((List.count_le_length).trans hys))
  have hs : (∑ k ∈ I, leibnizTerm I J xs (k :: ys) a u) =
      ∑ k ∈ I, (∏ i ∈ I.erase k, factorJet J i (xs.count i) (ys.count i) a u) •
        factorJet J k (xs.count k) (ys.count k + 1) a u := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [leibnizTerm_cons_u I J xs ys k a u hk]
    simp only [smul_eq_mul, mul_comm]
  rw [← hs] at hd
  exact hd

/-- If [the factor jets J of a finite index set I have the first-coordinate derivative chains at a
point (a, u)](hyp:I,J,a,u,h), then [the finite product of the base factors, as a function of the
first coordinate, has derivative at a equal to the explicit first first-coordinate jet](goal). -/
theorem hasDerivAt_product_a (I : Finset ι) (J : FactorJets ι) (a u : ℝ)
    (h : AChainsAt I J a u) :
    HasDerivAt (fun b => product I J b u) (productJet10 I J a u) a := by
  simpa only [product, productJet10, leibnizTerm, List.count_nil, factorJet] using
    hasDerivAt_leibnizTerm_a I J [] a u h (by simp)

/-- If [the factor jets J of a finite index set I have the first-coordinate derivative chains at a
point (a, u)](hyp:I,J,a,u,h), then [the first first-coordinate jet of the finite product, as a
function of the first coordinate, has derivative at a equal to the explicit second
first-coordinate jet](goal). -/
theorem hasDerivAt_productJet10_a (I : Finset ι) (J : FactorJets ι) (a u : ℝ)
    (h : AChainsAt I J a u) :
    HasDerivAt (fun b => productJet10 I J b u) (productJet20 I J a u) a := by
  have hd := HasDerivAt.fun_sum (u := I) (fun i _ =>
    hasDerivAt_leibnizTerm_a I J [i] a u h (by simp))
  rw [Finset.sum_comm] at hd
  exact hd

/-- If [the factor jets J of a finite index set I have the second-coordinate derivative chains at a
point (a, u)](hyp:I,J,a,u,h), then [the second first-coordinate jet of the finite product, as a
function of the second coordinate, has derivative at u equal to the explicit mixed (2,1)
jet](goal). -/
theorem hasDerivAt_productJet20_u (I : Finset ι) (J : FactorJets ι) (a u : ℝ)
    (h : UChainsAt I J a u) :
    HasDerivAt (fun v => productJet20 I J a v) (productJet21 I J a u) u := by
  exact HasDerivAt.fun_sum (u := I) (fun i _ =>
    HasDerivAt.fun_sum (u := I) (fun j _ =>
      hasDerivAt_leibnizTerm_u I J [i, j] [] a u h (by simp) (by simp)))

/-- If [the factor jets J of a finite index set I have the second-coordinate derivative chains at a
point (a, u)](hyp:I,J,a,u,h), then [the mixed (2,1) jet of the finite product, as a function of
the second coordinate, has derivative at u equal to the explicit mixed (2,2) jet](goal). -/
theorem hasDerivAt_productJet21_u (I : Finset ι) (J : FactorJets ι) (a u : ℝ)
    (h : UChainsAt I J a u) :
    HasDerivAt (fun v => productJet21 I J a v) (productJet22 I J a u) u := by
  unfold productJet21 productJet22
  apply HasDerivAt.fun_sum
  intro i hi
  apply HasDerivAt.fun_sum
  intro j hj
  have hd := HasDerivAt.fun_sum (u := I) (fun k _ =>
    hasDerivAt_leibnizTerm_u I J [i, j] [k] a u h (by simp) (by simp))
  rw [Finset.sum_comm] at hd
  exact hd

end Causalean.Mathlib.Analysis.Calculus.FiniteProduct

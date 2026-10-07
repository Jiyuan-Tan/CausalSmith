module
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.Count

/-!
# Coordinate finite-product jets: explicit ordered-hit formulas

Two lists record which factors each coordinate differentiation hits. Repeated hits are
counted, rather than collapsed to a set. The seven supplied factor jets suffice: second
second-coordinate derivatives at first-coordinate orders zero and one are zero.
Ordered pairs of first-coordinate hits automatically give coefficient two for distinct
factors, without division or nonvanishing assumptions. All sums are explicit finite sums.
-/

@[expose] public section

open scoped BigOperators
noncomputable section

namespace Causalean.Mathlib.Analysis.Calculus.FiniteProduct

variable {ι : Type*} [DecidableEq ι]

/-- A family of factor jets on [an index type](hyp:ι) supplies the [base,
first-coordinate, and second-coordinate functions](hyp:f00,f10,f20,f01,f11,f21,f22)
needed through order two in each coordinate. -/
structure FactorJets (ι : Type*) where
  f00 : ι → ℝ → ℝ → ℝ
  f10 : ι → ℝ → ℝ → ℝ
  f20 : ι → ℝ → ℝ → ℝ
  f01 : ι → ℝ → ℝ → ℝ
  f11 : ι → ℝ → ℝ → ℝ
  f21 : ι → ℝ → ℝ → ℝ
  f22 : ι → ℝ → ℝ → ℝ

/-- The [selected factor jet](goal) of [a supplied family](hyp:J) at
[an index](hyp:i), [two derivative orders](hyp:p,q), and [a point](hyp:a,u)
is the supplied function for that pair of orders when the pair is one of (0,0), (1,0), (2,0),
(0,1), (1,1), (2,1), (2,2), and zero for every other pair.

The pairs (0,2) and (1,2) are zero because each factor is treated as affine in the second
coordinate at first-coordinate orders zero and one. Pairs with an order above two are also
defined to be zero, but the calculus theorems only use first orders at most two and second orders
at most two. -/
def factorJet (J : FactorJets ι) (i : ι) (p q : ℕ) (a u : ℝ) : ℝ :=
  match p, q with
  | 0, 0 => J.f00 i a u
  | 1, 0 => J.f10 i a u
  | 2, 0 => J.f20 i a u
  | 0, 1 => J.f01 i a u
  | 1, 1 => J.f11 i a u
  | 2, 1 => J.f21 i a u
  | 2, 2 => J.f22 i a u
  | _, _ => 0

/-- An [ordered-hit Leibniz summand](goal) for [a finite set](hyp:I),
[factor jets](hyp:J), [first and second coordinate hit lists](hyp:xs,ys),
and [a point](hyp:a,u) is the product, over the indices in the finite set, of each factor's
jet at the point whose first- and second-coordinate orders are the numbers of times that index
occurs in the first and second hit lists. Thus the derivative assignments are inspectable factor
by factor. -/
def leibnizTerm (I : Finset ι) (J : FactorJets ι) (xs ys : List ι)
    (a u : ℝ) : ℝ :=
  ∏ i ∈ I, factorJet J i (xs.count i) (ys.count i) a u

/-- The [finite product](goal) of [the factors](hyp:J) over
[a finite index set](hyp:I) is evaluated at [a point](hyp:a,u). -/
def product (I : Finset ι) (J : FactorJets ι) (a u : ℝ) : ℝ :=
  ∏ i ∈ I, J.f00 i a u

/-- The [first first-coordinate jet](goal) of [the finite product](hyp:I,J)
at [a point](hyp:a,u) sums over the factor hit by one differentiation. -/
def productJet10 (I : Finset ι) (J : FactorJets ι) (a u : ℝ) : ℝ :=
  ∑ i ∈ I, leibnizTerm I J [i] [] a u

/-- The [second first-coordinate jet](goal) of [the finite product](hyp:I,J)
at [a point](hyp:a,u) sums over two ordered first-coordinate hits. Equal hits
use the second jet of one factor; distinct hits use the first jets of two factors. -/
def productJet20 (I : Finset ι) (J : FactorJets ι) (a u : ℝ) : ℝ :=
  ∑ i ∈ I, ∑ j ∈ I, leibnizTerm I J [i, j] [] a u

/-- The [mixed jet of orders two and one](goal) of [the finite product](hyp:I,J)
at [a point](hyp:a,u) sums over two ordered first-coordinate hits and one
second-coordinate hit. -/
def productJet21 (I : Finset ι) (J : FactorJets ι) (a u : ℝ) : ℝ :=
  ∑ i ∈ I, ∑ j ∈ I, ∑ k ∈ I, leibnizTerm I J [i, j] [k] a u

/-- The [mixed jet of orders two and two](goal) of [the finite product](hyp:I,J)
at [a point](hyp:a,u) sums over four ordered hits. Repeated second-coordinate
hits vanish unless all four hits are the same factor, which supplies its (2,2) jet. -/
def productJet22 (I : Finset ι) (J : FactorJets ι) (a u : ℝ) : ℝ :=
  ∑ i ∈ I, ∑ j ∈ I, ∑ k ∈ I, ∑ l ∈ I,
    leibnizTerm I J [i, j] [k, l] a u

/-- First-coordinate derivative data for [a finite family](hyp:I,J) at
[a point](hyp:a,u) consists of [the derivative from the base factor to its
first jet](hyp:da00) and [the derivative from that first jet to its second
jet](hyp:da10). -/
structure AChainsAt (I : Finset ι) (J : FactorJets ι) (a u : ℝ) : Prop where
  da00 : ∀ i ∈ I, HasDerivAt (fun b => J.f00 i b u) (J.f10 i a u) a
  da10 : ∀ i ∈ I, HasDerivAt (fun b => J.f10 i b u) (J.f20 i a u) a

/-- Second-coordinate derivative data for [a finite family](hyp:I,J) at
[a point](hyp:a,u) consists of [the six required factor derivative
identities](hyp:du00,du01,du10,du11,du20,du21). The zero derivatives of the
(0,1) and (1,1) jets express second-coordinate affinity. -/
structure UChainsAt (I : Finset ι) (J : FactorJets ι) (a u : ℝ) : Prop where
  du00 : ∀ i ∈ I, HasDerivAt (J.f00 i a) (J.f01 i a u) u
  du01 : ∀ i ∈ I, HasDerivAt (J.f01 i a) 0 u
  du10 : ∀ i ∈ I, HasDerivAt (J.f10 i a) (J.f11 i a u) u
  du11 : ∀ i ∈ I, HasDerivAt (J.f11 i a) 0 u
  du20 : ∀ i ∈ I, HasDerivAt (J.f20 i a) (J.f21 i a u) u
  du21 : ∀ i ∈ I, HasDerivAt (J.f21 i a) (J.f22 i a u) u

/-- Factor envelopes for [a finite family](hyp:I,J) at [a point](hyp:a,u)
consist of [the bound of two on the base factors](hyp:bound00) and [the bounds
of four on the six positive-order jets](hyp:bound10,bound20,bound01,bound11,bound21,bound22). -/
structure FactorBoundsAt (I : Finset ι) (J : FactorJets ι) (a u : ℝ) : Prop where
  bound00 : ∀ i ∈ I, |J.f00 i a u| ≤ 2
  bound10 : ∀ i ∈ I, |J.f10 i a u| ≤ 4
  bound20 : ∀ i ∈ I, |J.f20 i a u| ≤ 4
  bound01 : ∀ i ∈ I, |J.f01 i a u| ≤ 4
  bound11 : ∀ i ∈ I, |J.f11 i a u| ≤ 4
  bound21 : ∀ i ∈ I, |J.f21 i a u| ≤ 4
  bound22 : ∀ i ∈ I, |J.f22 i a u| ≤ 4

end Causalean.Mathlib.Analysis.Calculus.FiniteProduct

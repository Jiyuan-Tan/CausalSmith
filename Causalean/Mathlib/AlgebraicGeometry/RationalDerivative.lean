import Causalean.Mathlib.AlgebraicGeometry.RationalMap
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Combinatorics.Nullstellensatz

/-!
# Rational scalar derivative compiler

This module compiles vanishing of the full Fréchet derivative of a finite-dimensional real
rational scalar coordinate into one polynomial equation.  The quotient-rule numerators are
combined by a sum of squares; nonzeroness follows either from formal nonconstancy, an explicit
derivative witness, or semantic nonconstancy on a convex domain.
-/

open Set
open scoped BigOperators

namespace Causalean.Mathlib.AlgebraicGeometry

variable {S : Type*}

/-- A real rational scalar coordinate is a numerator and denominator multivariate polynomial. -/
structure RationalScalar (S : Type*) where
  num : MvPolynomial S ℝ
  den : MvPolynomial S ℝ

namespace RationalScalar

/-- For a [rational scalar](hyp:r) and [source assignment](hyp:x), the [evaluated scalar](goal)
is its numerator evaluation divided by its denominator evaluation. -/
noncomputable def eval (r : RationalScalar S) (x : S → ℝ) : ℝ :=
  MvPolynomial.eval x r.num / MvPolynomial.eval x r.den

/-- For a [rational scalar](hyp:r) and [domain](hyp:D), [being defined on the domain](goal) means
that its denominator never vanishes there. -/
def DefinedOn (r : RationalScalar S) (D : Set (S → ℝ)) : Prop :=
  ∀ x ∈ D, MvPolynomial.eval x r.den ≠ 0

/-- For a [rational scalar](hyp:r) and [source coordinate](hyp:i), the [cleared quotient-rule
numerator](goal) is the polynomial numerator of that coordinate derivative. -/
noncomputable def derivativeNumerator (r : RationalScalar S) (i : S) : MvPolynomial S ℝ :=
  MvPolynomial.pderiv i r.num * r.den -
    r.num * MvPolynomial.pderiv i r.den

/-- For a [rational scalar](hyp:r), [formal nonconstancy](goal) means that at least one cleared
partial-derivative numerator is a nonzero polynomial. -/
def IsFormallyNonconstant (r : RationalScalar S) : Prop :=
  ∃ i, r.derivativeNumerator i ≠ 0

/-- For a [rational scalar](hyp:r), the [full derivative certificate polynomial](goal) is the sum
of squares of all cleared quotient-rule partial numerators. -/
noncomputable def derivativePolynomial [Fintype S]
    (r : RationalScalar S) : MvPolynomial S ℝ :=
  conjunctionPolynomial r.derivativeNumerator

private noncomputable def polynomialDerivative [Fintype S]
    (p : MvPolynomial S ℝ) (x : S → ℝ) : (S → ℝ) →L[ℝ] ℝ :=
  ∑ i, MvPolynomial.eval x (MvPolynomial.pderiv i p) •
    ContinuousLinearMap.proj i

private theorem hasFDerivAt_polynomial_eval [Fintype S] [DecidableEq S]
    (p : MvPolynomial S ℝ) (x : S → ℝ) :
    HasFDerivAt (fun y => MvPolynomial.eval y p) (polynomialDerivative p x) x := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simpa [polynomialDerivative] using (hasFDerivAt_const (x := x) (c := a))
  | add p q hp hq =>
      have heq : polynomialDerivative (p + q) x =
          polynomialDerivative p x + polynomialDerivative q x := by
        ext v
        simp [polynomialDerivative, Finset.sum_add_distrib, add_smul]
      rw [heq]
      convert hp.add hq using 1 <;> try rfl
      funext y
      simp
  | mul_X p n hp =>
      have heq : polynomialDerivative (p * MvPolynomial.X n) x =
          MvPolynomial.eval x p • ContinuousLinearMap.proj n +
            x n • polynomialDerivative p x := by
        have hs : (∑ i : S, MvPolynomial.eval x
            (MvPolynomial.pderiv i (MvPolynomial.X n)) •
              (ContinuousLinearMap.proj i : (S → ℝ) →L[ℝ] ℝ)) =
            (ContinuousLinearMap.proj n : (S → ℝ) →L[ℝ] ℝ) := by
          ext v
          simp [MvPolynomial.pderiv_X, Pi.single_apply]
        simp only [polynomialDerivative, MvPolynomial.pderiv_mul, map_add,
          MvPolynomial.eval_mul, MvPolynomial.eval_X, add_smul,
          Finset.sum_add_distrib]
        rw [show (∑ i : S,
            (MvPolynomial.eval x (MvPolynomial.pderiv i p) * x n) •
              (ContinuousLinearMap.proj i : (S → ℝ) →L[ℝ] ℝ)) =
            x n • ∑ i : S, MvPolynomial.eval x (MvPolynomial.pderiv i p) •
              ContinuousLinearMap.proj i by
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [mul_comm]
          simp only [smul_smul]]
        rw [show (∑ i : S, (MvPolynomial.eval x p *
            MvPolynomial.eval x (MvPolynomial.pderiv i (MvPolynomial.X n))) •
              (ContinuousLinearMap.proj i : (S → ℝ) →L[ℝ] ℝ)) =
            MvPolynomial.eval x p • ∑ i : S, MvPolynomial.eval x
              (MvPolynomial.pderiv i (MvPolynomial.X n)) •
                ContinuousLinearMap.proj i by
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [smul_smul]]
        rw [hs]
        ac_rfl
      rw [heq]
      convert hp.mul (hasFDerivAt_apply n x) using 1 <;> try rfl
      funext y
      simp

private noncomputable def rationalDerivative [Fintype S]
    (r : RationalScalar S) (x : S → ℝ) : (S → ℝ) →L[ℝ] ℝ :=
  MvPolynomial.eval x r.num •
      (ContinuousLinearMap.toSpanSingleton ℝ
        (-(MvPolynomial.eval x r.den ^ 2)⁻¹)).comp
          (polynomialDerivative r.den x) +
    (MvPolynomial.eval x r.den)⁻¹ • polynomialDerivative r.num x

private theorem hasFDerivAt_eval [Fintype S] [DecidableEq S]
    (r : RationalScalar S) (x : S → ℝ)
    (hden : MvPolynomial.eval x r.den ≠ 0) :
    HasFDerivAt r.eval (rationalDerivative r x) x := by
  have hn := hasFDerivAt_polynomial_eval r.num x
  have hd := hasFDerivAt_polynomial_eval r.den x
  have hinv := (hasFDerivAt_inv hden).comp x hd
  have hmul := hn.mul hinv
  convert hmul using 1 <;> try rfl

private theorem rationalDerivative_single [Fintype S] [DecidableEq S]
    (r : RationalScalar S) (x : S → ℝ)
    (hden : MvPolynomial.eval x r.den ≠ 0) (i : S) :
    rationalDerivative r x (Pi.single i 1) =
      MvPolynomial.eval x (r.derivativeNumerator i) /
        MvPolynomial.eval x r.den ^ 2 := by
  simp [rationalDerivative, polynomialDerivative, derivativeNumerator,
    ContinuousLinearMap.toSpanSingleton_apply, Pi.single_apply, div_eq_mul_inv]
  field_simp
  ring

private theorem continuousLinearMap_eq_zero_iff_single [Fintype S] [DecidableEq S]
    (L : (S → ℝ) →L[ℝ] ℝ) :
    L = 0 ↔ ∀ i, L (Pi.single i 1) = 0 := by
  constructor
  · intro h i
    rw [h]
    rfl
  · intro h
    ext v
    have hv : v = ∑ i : S, v i • Pi.single i 1 := by
      ext j
      simp [Pi.single_apply]
    rw [hv, map_sum]
    simp [h]

private theorem exists_polynomial_eval_ne_zero [Finite S]
    (p : MvPolynomial S ℝ) (hp : p ≠ 0) :
    ∃ x : S → ℝ, MvPolynomial.eval x p ≠ 0 := by
  classical
  obtain ⟨t, ht, hdegree⟩ := Finset.exists_mem_eq_sup p.support
    (MvPolynomial.support_nonempty.mpr hp)
    (fun m => Multiset.card (Finsupp.toMultiset m))
  have hcoeff : MvPolynomial.coeff t p ≠ 0 :=
    MvPolynomial.mem_support_iff.mp ht
  have htotal : p.totalDegree = Finsupp.degree t := by
    rw [MvPolynomial.totalDegree_eq, hdegree, Finsupp.card_toMultiset]
    rfl
  obtain ⟨x, _, hx⟩ :=
    MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero
      p t hcoeff htotal
      (fun i => (Finset.range (t i + 1)).map Nat.castEmbedding)
      (fun i => by simp)
  exact ⟨x, hx⟩

/-- Given a [rational scalar](hyp:r), [source assignment](hyp:x), and [nonzero denominator at that
assignment](hyp:hden), the [full Fréchet derivative vanishes exactly when its certificate
polynomial vanishes](goal). -/
theorem fderiv_eq_zero_iff_derivativePolynomial_eq_zero [Fintype S] [DecidableEq S]
    (r : RationalScalar S) (x : S → ℝ)
    (hden : MvPolynomial.eval x r.den ≠ 0) :
    fderiv ℝ r.eval x = 0 ↔
      MvPolynomial.eval x r.derivativePolynomial = 0 := by
  rw [(hasFDerivAt_eval r x hden).fderiv,
    continuousLinearMap_eq_zero_iff_single]
  change (∀ i, rationalDerivative r x (Pi.single i 1) = 0) ↔
    MvPolynomial.eval x (conjunctionPolynomial r.derivativeNumerator) = 0
  rw [eval_conjunctionPolynomial_eq_zero_iff]
  constructor
  · intro h i
    have hz := h i
    rw [rationalDerivative_single r x hden i] at hz
    rcases div_eq_zero_iff.mp hz with hi | hpow
    · exact hi
    · exact (pow_ne_zero 2 hden hpow).elim
  · intro h i
    rw [rationalDerivative_single r x hden i, h i, zero_div]

/-- Given a rational scalar coordinate [r](hyp:r) on a [domain](hyp:D) where [its denominator does
not vanish](hyp:hD), the [points where its full Fréchet derivative vanishes are exactly one real
polynomial zero locus within that domain](goal). -/
theorem derivative_zero_locus [Fintype S] [DecidableEq S]
    (r : RationalScalar S) (D : Set (S → ℝ)) (hD : r.DefinedOn D) :
    {x | x ∈ D ∧ fderiv ℝ r.eval x = 0} =
      D ∩ Causalean.Mathlib.MeasureTheory.mvPolynomialZeroLocus r.derivativePolynomial := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff,
    Causalean.Mathlib.MeasureTheory.mvPolynomialZeroLocus]
  apply and_congr_right
  intro hx
  exact fderiv_eq_zero_iff_derivativePolynomial_eq_zero r x (hD x hx)

/-- Given a [rational scalar](hyp:r) satisfying [formal nonconstancy](hyp:h), the [full derivative
certificate polynomial is nonzero](goal). -/
theorem derivativePolynomial_ne_zero_of_formallyNonconstant [Fintype S]
    (r : RationalScalar S) (h : r.IsFormallyNonconstant) :
    r.derivativePolynomial ≠ 0 := by
  rcases h with ⟨i, hi⟩
  rcases exists_polynomial_eval_ne_zero (r.derivativeNumerator i) hi with ⟨x, hx⟩
  exact conjunctionPolynomial_ne_zero_of_witness r.derivativeNumerator x i hx

/-- Given a [rational scalar](hyp:r), [source assignment](hyp:x), [coordinate](hyp:i), and [a
nonzero cleared derivative numerator there](hyp:h), the [full derivative certificate polynomial is
nonzero](goal). -/
theorem derivativePolynomial_ne_zero_of_witness [Fintype S]
    (r : RationalScalar S) (x : S → ℝ) (i : S)
    (h : MvPolynomial.eval x (r.derivativeNumerator i) ≠ 0) :
    r.derivativePolynomial ≠ 0 := by
  exact conjunctionPolynomial_ne_zero_of_witness r.derivativeNumerator x i h

/-- Given a [rational scalar](hyp:r) on a [convex domain](hyp:D,hconvex), [a nowhere-vanishing
denominator](hyp:hD), [two domain points](hyp:x,y,hx,hy), and [distinct rational values](hyp:hne),
the [full derivative certificate polynomial is nonzero](goal). -/
theorem derivativePolynomial_ne_zero_of_nonconstantOn_convex
    [Fintype S] [DecidableEq S]
    (r : RationalScalar S) (D : Set (S → ℝ)) (hconvex : Convex ℝ D)
    (hD : r.DefinedOn D)
    (x y : S → ℝ) (hx : x ∈ D) (hy : y ∈ D) (hne : r.eval x ≠ r.eval y) :
    r.derivativePolynomial ≠ 0 := by
  intro hzero
  have hdiffAt : ∀ z ∈ D, DifferentiableAt ℝ r.eval z := by
    intro z hz
    exact (hasFDerivAt_eval r z (hD z hz)).differentiableAt
  have hfderiv : ∀ z ∈ D, fderiv ℝ r.eval z = 0 := by
    intro z hz
    apply (fderiv_eq_zero_iff_derivativePolynomial_eq_zero r z (hD z hz)).mpr
    rw [hzero]
    simp
  have hdiffOn : DifferentiableOn ℝ r.eval D := by
    intro z hz
    exact (hdiffAt z hz).differentiableWithinAt
  have hfderivWithin : ∀ z ∈ D, fderivWithin ℝ r.eval D z = 0 := by
    intro z hz
    have hzeroAt : HasFDerivAt r.eval (0 : (S → ℝ) →L[ℝ] ℝ) z := by
      rw [← hfderiv z hz]
      exact (hdiffAt z hz).hasFDerivAt
    rw [fderivWithin_def]
    simp [hzeroAt.hasFDerivWithinAt]
  exact hne (hconvex.is_const_of_fderivWithin_eq_zero
    hdiffOn hfderivWithin hx hy)

end RationalScalar

end Causalean.Mathlib.AlgebraicGeometry


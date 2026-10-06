module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.ChebyshevOneNorm
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.ParametricTensor
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Four-variable tensor Chebyshev polynomials

Tensor products of first-kind Chebyshev polynomials in four variables: the basis, the
polynomial with prescribed tensor coefficients, and the integral coefficient functional against
the normalized product cosine kernel. The file proves one-variable cosine orthogonality and
finite spanning, recovery of the tensor coefficients of a coordinatewise degree-bounded
polynomial, the factorization of monomial coefficients of a basis polynomial, and the resulting
coefficient one-norm bound.
-/

@[expose] public section

noncomputable section

open Causalean.Mathlib.Analysis.JacksonApproximation
open MeasureTheory
open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev

/-- [A degree bound and tensor index](hyp:D,k) determine [the corresponding four-variable tensor Chebyshev basis polynomial](goal).

The four-variable tensor product of first-kind Chebyshev polynomials at multi-index `k`.
-/
def tensorChebyshevBasis (D : ℕ) (k : Fin 4 → Fin (D + 1)) :
    MvPolynomial (Fin 4) ℝ :=
  ∏ i : Fin 4,
    (Polynomial.Chebyshev.T ℝ ((k i : ℕ) : ℤ)).toMvPolynomial i

/-- [A degree bound and tensor coefficient vector](hyp:D,c) determine [their tensor Chebyshev polynomial](goal).

The polynomial obtained from a finite tensor Chebyshev coefficient vector.
-/
def tensorChebyshevPolynomial (D : ℕ)
    (c : (Fin 4 → Fin (D + 1)) → ℝ) : MvPolynomial (Fin 4) ℝ :=
  ∑ k, MvPolynomial.C (c k) * tensorChebyshevBasis D k

/-- [A degree bound, multivariate polynomial, and tensor index](hyp:D,p,k) determine [the matching product-cosine integral coefficient](goal).

The tensor Chebyshev coefficient obtained by integrating a polynomial against the
corresponding product cosine function on the four-dimensional period box.
-/
def tensorChebyshevCoefficient (D : ℕ) (p : MvPolynomial (Fin 4) ℝ)
    (k : Fin 4 → Fin (D + 1)) : ℝ :=
  (∏ i : Fin 4,
      if (k i : ℕ) = 0 then (1 / (2 * Real.pi) : ℝ) else 1 / Real.pi) *
    ∫ u in periodBox 4,
      (∏ i : Fin 4, Real.cos ((k i : ℕ) * u i)) *
        MvPolynomial.eval (fun i => Real.cos (u i)) p

/-- Normalized cosine integration on the full period recovers the coefficient of a single
one-variable Chebyshev basis polynomial. The zero frequency has normalization `1/(2π)`, and
every positive frequency has normalization `1/π`.

The unnormalized integral is `2π` at frequency zero, `π` at a matching positive frequency,
and zero otherwise. Mathlib's `Polynomial.Chebyshev` orthogonality uses `measureT` on `[-1,1]`;
convert that theorem to the period interval, or prove the cosine product integral directly.
-/
theorem chebyshev_one_variable_cosine_orthogonality (k m : ℕ) :
    (if k = 0 then (1 / (2 * Real.pi) : ℝ) else 1 / Real.pi) *
      (∫ u in Set.Icc (-Real.pi) Real.pi,
        Real.cos (k * u) *
          Polynomial.eval (Real.cos u) (Polynomial.Chebyshev.T ℝ (m : ℤ))) =
      if k = m then 1 else 0 := by
  let f : ℝ → ℝ := fun u => Real.cos (k * u) *
    Polynomial.eval (Real.cos u) (Polynomial.Chebyshev.T ℝ (m : ℤ))
  have hf : Continuous f := by fun_prop
  have heven (u : ℝ) : f (-u) = f u := by
    simp [f, mul_neg, Real.cos_neg]
  have hleft : (∫ u in -Real.pi..0, f u) = ∫ u in 0..Real.pi, f u := by
    simpa only [neg_zero, neg_neg] using
      (intervalIntegral.integral_comp_neg (f := f) (a := 0) (b := Real.pi)).symm.trans
        (intervalIntegral.integral_congr (fun u hu => heven u))
  have hfull : (∫ u in Set.Icc (-Real.pi) Real.pi, f u) =
      2 * ∫ u in 0..Real.pi, f u := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _), hleft]
    ring
  have hmeasure : (∫ u in 0..Real.pi, f u) =
      ∫ x, (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval x *
        (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval x
          ∂Polynomial.Chebyshev.measureT := by
    rw [Polynomial.Chebyshev.integral_measureT_eq_integral_cos]
    apply intervalIntegral.integral_congr
    intro u hu
    simp only [f, Polynomial.Chebyshev.T_real_cos]
    congr 1
  change (if k = 0 then (1 / (2 * Real.pi) : ℝ) else 1 / Real.pi) *
      (∫ u in Set.Icc (-Real.pi) Real.pi, f u) = if k = m then 1 else 0
  rw [hfull, hmeasure]
  by_cases hkm : k = m
  · subst m
    by_cases hk : k = 0
    · subst k
      simp only [Nat.cast_zero]
      rw [Polynomial.Chebyshev.integral_eval_T_real_mul_self_measureT_zero]
      simp only [if_true]
      field_simp
    · rw [Polynomial.Chebyshev.integral_T_real_mul_self_measureT_of_ne_zero hk]
      simp only [if_neg hk]
      field_simp
      simp
  · simp [hkm, Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne hkm]

/-- A real polynomial of degree at most `D` is a finite linear combination of the first
`D+1` first-kind Chebyshev polynomials, with constant real coefficients.

Induct on degree using the nonzero leading coefficient of `T_D`. The lower degree remainder
is handled by the induction hypothesis; equivalently construct the triangular change of basis.
-/
theorem chebyshev_one_variable_finite_span (D : ℕ) (p : Polynomial ℝ)
    (hdeg : p.natDegree ≤ D) :
    ∃ c : Fin (D + 1) → ℝ,
      p = ∑ k : Fin (D + 1),
        Polynomial.C (c k) * Polynomial.Chebyshev.T ℝ ((k : ℕ) : ℤ) := by
  let S := Polynomial.Chebyshev.chebyshevTsequence ℝ
  have hcoeff : ∀ i < D + 1, IsUnit (S i).leadingCoeff := by
    intro i hi
    change IsUnit (Polynomial.Chebyshev.T ℝ (i : ℤ)).leadingCoeff
    rw [Polynomial.Chebyshev.leadingCoeff_T]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  have hp : p ∈ Submodule.span ℝ (S '' Set.Iio (D + 1)) := by
    rw [S.span_degreeLT hcoeff, Polynomial.mem_degreeLT]
    by_cases hp0 : p = 0
    · simp [hp0]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hp0).mp (Nat.lt_succ_of_le hdeg)
  obtain ⟨c, hc⟩ := (Fintype.mem_span_image_iff_exists_fun ℝ).mp hp
  let e : Fin (D + 1) ≃ (Set.Iio (D + 1) : Set ℕ) := (Fin.orderIsoSubtype).toEquiv
  refine ⟨fun k => c (e k), ?_⟩
  rw [← hc]
  have he (k : Fin (D + 1)) : (e k).1 = k.1 := rfl
  simpa only [he, S, Polynomial.Chebyshev.chebyshevTsequence,
    Polynomial.smul_eq_C_mul] using
    (Fintype.sum_equiv e (fun k : Fin (D + 1) =>
      c (e k) • S (e k).1) (fun i => c i • S i.1) (fun k => rfl)).symm

/-- Integrating a four-coordinate tensor Chebyshev basis against the normalized product
cosine kernel yields one at the matching multi-index and zero at every other index.

Use Fubini on the product period box, factor the integrand into four one-variable factors,
then apply `chebyshev_one_variable_cosine_orthogonality` coordinatewise.
-/
theorem tensorChebyshevCoefficient_basis (D : ℕ)
    (k m : Fin 4 → Fin (D + 1)) :
    tensorChebyshevCoefficient D (tensorChebyshevBasis D m) k =
      if k = m then 1 else 0 := by
  have heval (u : Fin 4 → ℝ) :
      MvPolynomial.eval (fun i => Real.cos (u i)) (tensorChebyshevBasis D m) =
        ∏ i : Fin 4,
          Polynomial.eval (Real.cos (u i)) (Polynomial.Chebyshev.T ℝ ((m i : ℕ) : ℤ)) := by
    simp [tensorChebyshevBasis, MvPolynomial.eval_toMvPolynomial]
  have hcont (i : Fin 4) : Continuous (fun u : ℝ =>
      Real.cos ((k i : ℕ) * u) *
        Polynomial.eval (Real.cos u) (Polynomial.Chebyshev.T ℝ ((m i : ℕ) : ℤ))) := by
    fun_prop
  unfold tensorChebyshevCoefficient
  simp_rw [heval, ← Finset.prod_mul_distrib]
  rw [integral_periodBox_prod _ (fun i => (hcont i).integrableOn_Icc), ← Finset.prod_mul_distrib]
  simp_rw [chebyshev_one_variable_cosine_orthogonality]
  by_cases hkm : k = m
  · subst m
    simp
  · have hi : ∃ i : Fin 4, k i ≠ m i := by
      by_contra h
      apply hkm
      funext i
      exact of_not_not (not_exists.mp h i)
    obtain ⟨i, hi⟩ := hi
    rw [if_neg hkm]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [Fin.val_ne_of_ne hi]

/-- Each bounded-degree tensor monomial is a finite real linear combination of the tensor
Chebyshev basis polynomials with indices at most `D` in every coordinate.

Expand each univariate monomial with `chebyshev_one_variable_finite_span`, map the expansions
to distinct multivariate coordinates, and distribute the finite product.
-/
theorem tensorChebyshevBasis_monomial_span (D : ℕ)
    (a : Fin 4 → Fin (D + 1)) :
    ∃ c : (Fin 4 → Fin (D + 1)) → ℝ,
      MvPolynomial.monomial (tensorExponent a) (1 : ℝ) =
        tensorChebyshevPolynomial D c := by
  classical
  have hdeg (i : Fin 4) : (Polynomial.X ^ (a i : ℕ) : Polynomial ℝ).natDegree ≤ D := by
    simpa only [Polynomial.natDegree_X_pow] using (Nat.lt_succ_iff.mp (a i).isLt)
  choose c hc using fun i => chebyshev_one_variable_finite_span D
    (Polynomial.X ^ (a i : ℕ)) (hdeg i)
  refine ⟨fun k => ∏ i, c i (k i), ?_⟩
  have hexp : (∑ i : Fin 4, Finsupp.single i (a i : ℕ)) = tensorExponent a := by
    ext i
    simp [tensorExponent, Finsupp.single_apply]
  have hmon : MvPolynomial.monomial (tensorExponent a) (1 : ℝ) =
      ∏ i : Fin 4, (Polynomial.X ^ (a i : ℕ) : Polynomial ℝ).toMvPolynomial i := by
    calc
      _ = MvPolynomial.monomial (∑ i : Fin 4, Finsupp.single i (a i : ℕ))
          (∏ _i : Fin 4, (1 : ℝ)) := by simp [hexp]
      _ = ∏ i : Fin 4,
          MvPolynomial.monomial (Finsupp.single i (a i : ℕ)) (1 : ℝ) := by
            rw [MvPolynomial.monomial_sum_prod]
      _ = _ := by simp [MvPolynomial.X_pow_eq_monomial]
  rw [hmon]
  have hcoord (i : Fin 4) :
      (Polynomial.X ^ (a i : ℕ) : Polynomial ℝ).toMvPolynomial i =
        ∑ j : Fin (D + 1),
          MvPolynomial.C (c i j) *
            (Polynomial.Chebyshev.T ℝ ((j : ℕ) : ℤ)).toMvPolynomial i := by
    have h := congrArg (fun p : Polynomial ℝ => p.toMvPolynomial i) (hc i)
    simpa only [map_sum, map_mul, Polynomial.toMvPolynomial_C] using h
  simp_rw [hcoord]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib, ← map_prod]
  rfl

/-- Every four-variable polynomial of coordinatewise degree at most `D` lies in the span of
the tensor Chebyshev basis indexed by `(Fin (D+1))^4`.

Expand the fixed monomial basis from `tensorPolynomial_tensorCoeffs`; apply
`chebyshev_one_variable_finite_span` to each coordinate and distribute the finite products.
-/
theorem tensorChebyshevBasis_finite_span (D : ℕ)
    (p : MvPolynomial (Fin 4) ℝ)
    (hdeg : ∀ i, p.degreeOf i ≤ D) :
    ∃ c : (Fin 4 → Fin (D + 1)) → ℝ,
      p = tensorChebyshevPolynomial D c := by
  classical
  choose c hc using fun a : Fin 4 → Fin (D + 1) =>
    tensorChebyshevBasis_monomial_span D a
  refine ⟨fun k => ∑ a, tensorCoeffs (D := D) p a * c a k, ?_⟩
  have hscale (a : Fin 4 → Fin (D + 1)) :
      MvPolynomial.monomial (tensorExponent a) (tensorCoeffs (D := D) p a) =
        MvPolynomial.C (tensorCoeffs (D := D) p a) *
          tensorChebyshevPolynomial D (c a) := by
    rw [← hc a]
    rw [MvPolynomial.C_mul_monomial]
    simp
  calc
    p = tensorPolynomial (tensorCoeffs (D := D) p) :=
      (tensorPolynomial_tensorCoeffs p hdeg).symm
    _ = tensorChebyshevPolynomial D
        (fun k => ∑ a, tensorCoeffs (D := D) p a * c a k) := by
      unfold tensorPolynomial tensorChebyshevPolynomial
      simp_rw [hscale]
      simp only [tensorChebyshevPolynomial, Finset.mul_sum, ← mul_assoc,
        ← map_mul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, ← map_sum]

/-- [Every four-variable polynomial](hyp:p) [of coordinatewise degree at most `D`](hyp:hdeg)
[equals the tensor Chebyshev expansion of its explicit product-cosine integral
coefficients](goal).

Apply one-variable cosine orthogonality successively to the four coordinates. Use polynomial
extensionality after expanding each coordinate in the Chebyshev basis; the degree bound makes
the expansion finite. The zero frequency uses normalization `1/(2π)`.
-/
theorem tensorChebyshev_coeff_recovery (D : ℕ)
    (p : MvPolynomial (Fin 4) ℝ)
    (hdeg : ∀ i, p.degreeOf i ≤ D) :
    p = tensorChebyshevPolynomial D (tensorChebyshevCoefficient D p) := by
  classical
  obtain ⟨c, hc⟩ := tensorChebyshevBasis_finite_span D p hdeg
  have hcompact : IsCompact (periodBox 4) := by
    change IsCompact {u : Fin 4 → ℝ | ∀ i, u i ∈ Set.Icc (-Real.pi) Real.pi}
    exact isCompact_pi_infinite fun _ => isCompact_Icc
  have hlin (k : Fin 4 → Fin (D + 1)) :
      tensorChebyshevCoefficient D (tensorChebyshevPolynomial D c) k =
        ∑ m, c m * tensorChebyshevCoefficient D (tensorChebyshevBasis D m) k := by
    have hint (m : Fin 4 → Fin (D + 1)) :
        IntegrableOn (fun u : Fin 4 → ℝ =>
          (∏ i : Fin 4, Real.cos ((k i : ℕ) * u i)) *
            (c m * MvPolynomial.eval (fun i => Real.cos (u i))
              (tensorChebyshevBasis D m))) (periodBox 4) := by
      have hcos : Continuous (fun u : Fin 4 → ℝ => fun i => Real.cos (u i)) := by
        fun_prop
      have hcont : Continuous (fun u : Fin 4 → ℝ =>
          (∏ i : Fin 4, Real.cos ((k i : ℕ) * u i)) *
            (c m * MvPolynomial.eval (fun i => Real.cos (u i))
              (tensorChebyshevBasis D m))) := by
        have heval := ((tensorChebyshevBasis D m).continuous_eval).comp hcos
        fun_prop (disch := assumption)
      exact hcont.continuousOn.integrableOn_compact hcompact
    unfold tensorChebyshevCoefficient tensorChebyshevPolynomial
    simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C,
      Finset.mul_sum]
    rw [integral_finsetSum Finset.univ (fun m _ => hint m)]
    simp_rw [show ∀ (m : Fin 4 → Fin (D + 1)) (u : Fin 4 → ℝ),
      (∏ i : Fin 4, Real.cos ((k i : ℕ) * u i)) *
          (c m * MvPolynomial.eval (fun i => Real.cos (u i)) (tensorChebyshevBasis D m)) =
        c m * ((∏ i : Fin 4, Real.cos ((k i : ℕ) * u i)) *
          MvPolynomial.eval (fun i => Real.cos (u i)) (tensorChebyshevBasis D m))
      from fun m u => by ring]
    simp_rw [integral_const_mul]
    rw [Finset.mul_sum]
    congr 1
    ext m
    ring
  have hcoeff : tensorChebyshevCoefficient D p = c := by
    funext k
    rw [hc, hlin]
    simp [tensorChebyshevCoefficient_basis]
  simpa [hcoeff] using hc


/-- Each fixed monomial coefficient of a four-variable tensor Chebyshev basis polynomial is
the product of the corresponding one-variable Chebyshev coefficients.

Expand each `Polynomial.toMvPolynomial` into monomials and distribute the product. Distinct
coordinates make the exponent-sum map injective, so the desired coefficient is one product.
-/
theorem tensorChebyshevBasis_coeff_factorization (D : ℕ)
    (k a : Fin 4 → Fin (D + 1)) :
    tensorCoeffs (D := D) (tensorChebyshevBasis D k) a =
      ∏ i : Fin 4,
        (Polynomial.Chebyshev.T ℝ ((k i : ℕ) : ℤ)).coeff (a i : ℕ) := by
  classical
  let p : Fin 4 → Polynomial ℝ :=
    fun i => Polynomial.Chebyshev.T ℝ ((k i : ℕ) : ℤ)
  have hpdeg (i : Fin 4) : (p i).natDegree < D + 1 := by
    simp only [p, Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast]
    exact (k i).isLt
  have hto (i : Fin 4) :
      (p i).toMvPolynomial i =
        ∑ j : Fin (D + 1),
          MvPolynomial.C ((p i).coeff (j : ℕ)) *
            MvPolynomial.X i ^ (j : ℕ) := by
    have h := Polynomial.as_sum_range_C_mul_X_pow' (p i) (hpdeg i)
    have h' := congrArg (fun q : Polynomial ℝ => q.toMvPolynomial i) h
    simpa only [map_sum, map_mul, map_pow, Polynomial.toMvPolynomial_C,
      Polynomial.toMvPolynomial_X, ← Fin.sum_univ_eq_sum_range] using h'
  have hexp (b : Fin 4 → Fin (D + 1)) :
      (∑ i : Fin 4, Finsupp.single i (b i : ℕ)) = tensorExponent b := by
    ext i
    simp [tensorExponent, Finsupp.single_apply]
  have hmon (b : Fin 4 → Fin (D + 1)) :
      (∏ i : Fin 4,
        MvPolynomial.C ((p i).coeff (b i : ℕ)) *
          MvPolynomial.X i ^ (b i : ℕ)) =
        MvPolynomial.monomial (tensorExponent b)
          (∏ i : Fin 4, (p i).coeff (b i : ℕ)) := by
    calc
      _ = ∏ i : Fin 4,
          MvPolynomial.monomial (Finsupp.single i (b i : ℕ))
            ((p i).coeff (b i : ℕ)) := by
              apply Finset.prod_congr rfl
              intro i hi
              simp [MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial]
      _ = MvPolynomial.monomial (∑ i : Fin 4, Finsupp.single i (b i : ℕ))
          (∏ i : Fin 4, (p i).coeff (b i : ℕ)) := by
            rw [MvPolynomial.monomial_sum_prod]
      _ = _ := by rw [hexp]
  have hinj : Function.Injective (tensorExponent (d := 4) (D := D)) := by
    intro b c h
    funext i
    apply Fin.ext
    have hi := congrArg (fun m : Fin 4 →₀ ℕ => m i) h
    simpa [tensorExponent] using hi
  change (∏ i : Fin 4, (p i).toMvPolynomial i).coeff (tensorExponent a) =
    ∏ i : Fin 4, (p i).coeff (a i : ℕ)
  simp_rw [hto]
  rw [Fintype.prod_sum]
  simp_rw [hmon]
  simp only [MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    have hne : tensorExponent b ≠ tensorExponent a := fun h => hba (hinj h)
    simp [MvPolynomial.coeff_monomial, hne]
  · intro ha
    exact (ha (Finset.mem_univ a)).elim

/-- The sum of the absolute monomial coefficients of one four-variable tensor Chebyshev basis
polynomial is at most `(1+√2)^(4D)` for every index bounded by `D`.

Use the submultiplicativity of `polynomialCoeffOneNorm`, its multivariate tensor-product
counterpart, and `polynomialCoeffOneNorm_chebyshev_le` in each coordinate.
-/
theorem tensorChebyshevBasis_coeff_oneNorm_le (D : ℕ)
    (k : Fin 4 → Fin (D + 1)) :
    (∑ a : Fin 4 → Fin (D + 1),
      |tensorCoeffs (D := D) (tensorChebyshevBasis D k) a|) ≤
        (1 + Real.sqrt 2) ^ (4 * D) := by
  classical
  let r : ℝ := 1 + Real.sqrt 2
  have hr : 1 ≤ r := by dsimp [r]; linarith [Real.sqrt_nonneg 2]
  have hsum (i : Fin 4) :
      (∑ j : Fin (D + 1),
        |(Polynomial.Chebyshev.T ℝ ((k i : ℕ) : ℤ)).coeff (j : ℕ)|) ≤ r ^ D := by
    let p := Polynomial.Chebyshev.T ℝ ((k i : ℕ) : ℤ)
    have hdeg : p.natDegree < D + 1 := by
      simp only [p, Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast]
      exact (k i).isLt
    have heq : (∑ j : Fin (D + 1), |p.coeff (j : ℕ)|) =
        polynomialCoeffOneNorm p := by
      change _ = p.sum (fun _ c => |c|)
      rw [p.sum_over_range' (fun _ => abs_zero) (D + 1) hdeg]
      simp only [← Fin.sum_univ_eq_sum_range]
    calc
      _ = polynomialCoeffOneNorm p := heq
      _ ≤ r ^ (k i : ℕ) := polynomialCoeffOneNorm_chebyshev_le _
      _ ≤ r ^ D := pow_le_pow_right₀ hr (Nat.le_of_lt_succ (k i).isLt)
  calc
    (∑ a : Fin 4 → Fin (D + 1),
      |tensorCoeffs (D := D) (tensorChebyshevBasis D k) a|)
        = ∑ a : Fin 4 → Fin (D + 1),
            ∏ i : Fin 4,
              |(Polynomial.Chebyshev.T ℝ ((k i : ℕ) : ℤ)).coeff (a i : ℕ)| := by
          simp_rw [tensorChebyshevBasis_coeff_factorization, Finset.abs_prod]
    _ = ∏ i : Fin 4, ∑ j : Fin (D + 1),
          |(Polynomial.Chebyshev.T ℝ ((k i : ℕ) : ℤ)).coeff (j : ℕ)| := by
          rw [Fintype.prod_sum]
    _ ≤ ∏ _i : Fin 4, r ^ D := by
          apply Finset.prod_le_prod
          · intro i hi
            positivity
          · intro i hi
            exact hsum i
    _ = r ^ (4 * D) := by
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          rw [← pow_mul, Nat.mul_comm]

end Causalean.Mathlib.Analysis.Approximation.Chebyshev

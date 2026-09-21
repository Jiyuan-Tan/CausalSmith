module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Szego
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.NormNum.Parity

/-!
# Algebraic and analytic foundations of the order-four Jackson kernel

This module defines the raw and normalized fourth-power Jackson kernels, relates the raw kernel
to Chebyshev polynomials, and proves the finite cosine and integral identities needed later. It
also establishes continuity, measurability, integrability, nonnegativity, and evenness of the raw
kernel. Exact mass, moment bounds, and trigonometric degree are proved in `Kernel_Part2`.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.JacksonApproximation

open MeasureTheory Real
open scoped BigOperators
/-- [A nonnegative integer order](hyp:K) and [a real argument](hyp:t) determine [the raw
order-four Jackson kernel](goal), obtained from the fourth power of the Dirichlet sine
quotient with its removable singularities filled continuously.
-/
noncomputable def jraw (K : ℕ) (t : ℝ) : ℝ :=
  if Real.sin (t / 2) = 0 then (K : ℝ) ^ 4
  else (Real.sin ((K : ℝ) * t / 2) / Real.sin (t / 2)) ^ 4

/-- [An integer order](hyp:K) determines [the raw Jackson mass](goal), the integral of the raw
kernel over the standard period from minus π to π.
-/
noncomputable def jrawMass (K : ℕ) : ℝ :=
  ∫ t in Set.Icc (-Real.pi) Real.pi, jraw K t

/-- [An integer order](hyp:K) and [a real argument](hyp:t) determine [the normalized order-four
Jackson kernel](goal), equal to the raw kernel divided by its mass over the standard period. It is
normalized for positive order; at order zero the raw kernel and its mass vanish and the value is
zero by the division convention.
-/
noncomputable def jackson (K : ℕ) (t : ℝ) : ℝ := jraw K t / jrawMass K

/-- At [order K](hyp:K) and [argument t](hyp:t), if [the denominator sine is nonzero](hyp:ht),
then [the raw kernel equals the displayed fourth power of the sine quotient](goal).
-/
theorem jraw_eq_of_sin_ne_zero (K : ℕ) {t : ℝ} (ht : Real.sin (t / 2) ≠ 0) :
    jraw K t = (Real.sin ((K : ℝ) * t / 2) / Real.sin (t / 2)) ^ 4 := by
  simp [jraw, ht]

/-- At [order K](hyp:K) and [argument t](hyp:t), if [the denominator sine vanishes](hyp:ht), then
[the raw kernel equals K to the fourth power](goal).
-/
theorem jraw_eq_of_sin_eq_zero (K : ℕ) {t : ℝ} (ht : Real.sin (t / 2) = 0) :
    jraw K t = (K : ℝ) ^ 4 := by
  simp [jraw, ht]

/-- At [a strictly positive kernel order](hyp:K,hK) and [a real argument](hyp:t), [the raw
Jackson kernel equals the fourth power of the corresponding Chebyshev polynomial of the second
kind evaluated at the half-angle cosine](goal). -/
lemma jraw_eq_chebyshev (K : ℕ) (hK : 0 < K) (t : ℝ) :
    jraw K t =
      ((Polynomial.Chebyshev.U ℝ ((K - 1 : ℕ) : ℤ)).eval (Real.cos (t / 2))) ^ 4 := by
  by_cases ht : Real.sin (t / 2) = 0
  · rw [jraw_eq_of_sin_eq_zero K ht]
    rcases Real.sin_eq_zero_iff_cos_eq.mp ht with hc | hc
    · rw [hc, Polynomial.Chebyshev.U_eval_one]
      norm_num
      congr 1
      norm_cast
      omega
    · rw [hc, Polynomial.Chebyshev.U_eval_neg_one]
      norm_num
      have hcast : ((K - 1 : ℕ) : ℝ) + 1 = (K : ℝ) := by
        norm_cast
        omega
      rw [hcast, mul_pow, ← pow_mul]
      norm_num
  · rw [jraw_eq_of_sin_ne_zero K ht]
    congr 1
    apply (div_eq_iff ht).2
    have hu := Polynomial.Chebyshev.U_real_cos (t / 2) ((K - 1 : ℕ) : ℤ)
    have hn : K - 1 + 1 = K := by omega
    have harg : (((((K - 1 : ℕ) : ℤ) : ℝ)) + 1) * (t / 2) =
        (K : ℝ) * t / 2 := by
      have hcast : (((((K - 1 : ℕ) : ℤ) : ℝ)) + 1) = (K : ℝ) := by
        exact_mod_cast hn
      rw [hcast]
      ring
    exact (congrArg Real.sin harg).symm.trans hu.symm

private lemma coeff_comp_neg_X (p : Polynomial ℝ) (k : ℕ) :
    (p.comp (-Polynomial.X)).coeff k = (-1 : ℝ) ^ k * p.coeff k := by
  rw [p.as_sum_range_C_mul_X_pow]
  simp
  by_cases hk : k ≤ p.natDegree
  · rw [Finset.sum_eq_single k]
    · rw [show (-Polynomial.X : Polynomial ℝ) =
          Polynomial.C (-1) * Polynomial.X by simp, mul_pow]
      rw [← Polynomial.C_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      simp [hk]
      ring
    · intro b hb hbk
      rw [show (-Polynomial.X : Polynomial ℝ) =
          Polynomial.C (-1) * Polynomial.X by simp, mul_pow]
      rw [← Polynomial.C_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      simp [hbk.symm]
    · simp [hk]
  · rw [Finset.sum_eq_zero]
    · simp [hk]
    · intro b hb
      have hbk : b ≠ k := by
        intro h
        subst b
        exact hk (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb))
      rw [show (-Polynomial.X : Polynomial ℝ) =
          Polynomial.C (-1) * Polynomial.X by simp, mul_pow]
      rw [← Polynomial.C_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      simp [hbk.symm]

/-- If [a real polynomial](hyp:p) [takes the same value at every pair of opposite
arguments](hyp:hp), then [it is a polynomial in the square variable, with the outer polynomial's
degree at most half the original degree](goal). -/
lemma exists_comp_sq_of_eval_neg_eq (p : Polynomial ℝ)
    (hp : ∀ x : ℝ, p.eval (-x) = p.eval x) :
    ∃ q : Polynomial ℝ, q.natDegree ≤ p.natDegree / 2 ∧
      p = q.comp (Polynomial.X ^ 2) := by
  have hpoly : p.comp (-Polynomial.X) = p := by
    apply Polynomial.funext
    intro x
    simpa [Polynomial.eval_comp] using hp x
  have hcoeff (i : ℕ) (hi : Odd i) : p.coeff i = 0 := by
    have h := congrArg (fun q : Polynomial ℝ => q.coeff i) hpoly
    rw [coeff_comp_neg_X, hi.neg_one_pow] at h
    linarith
  have heven (i : ℕ) (hi : i ∈ p.support) : Even i := by
    rcases Nat.even_or_odd i with h | h
    · exact h
    · exact ((Polynomial.mem_support_iff.mp hi) (hcoeff i h)).elim
  let q : Polynomial ℝ :=
    ∑ i ∈ p.support, Polynomial.C (p.coeff i) * Polynomial.X ^ (i / 2)
  refine ⟨q, ?_, ?_⟩
  · apply (Polynomial.natDegree_sum_le_of_forall_le _ _)
    intro i hi
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
      (Nat.div_le_div_right (Polynomial.le_natDegree_of_mem_supp i hi) :
        i / 2 ≤ p.natDegree / 2)
  · rw [p.as_sum_support_C_mul_X_pow]
    simp only [q, Polynomial.sum_comp, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.pow_comp, Polynomial.X_comp]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    rw [← pow_mul]
    congr 1
    exact (Nat.two_mul_div_two_of_even (heven i hi)).symm

private lemma complex_sin_sq_step (a b : ℂ) :
    Complex.sin (a + b) ^ 2 - Complex.sin a ^ 2 =
      Complex.sin (2 * a + b) * Complex.sin b := by
  rw [show 2 * a + b = a + (a + b) by ring]
  simp_rw [Complex.sin_add, Complex.cos_add]
  ring_nf
  rw [Complex.cos_sq' a, Complex.cos_sq' b]
  ring

private lemma cheb_U_sq_sub (n : ℕ) :
    Polynomial.Chebyshev.U ℂ ((n + 1 : ℕ) : ℤ) ^ 2 -
        Polynomial.Chebyshev.U ℂ (n : ℤ) ^ 2 =
      Polynomial.Chebyshev.U ℂ ((2 * n + 2 : ℕ) : ℤ) := by
  apply Polynomial.funext
  intro x
  obtain ⟨θ, rfl⟩ := Complex.cos_surjective x
  by_cases hs : Complex.sin θ = 0
  · rcases Complex.sin_eq_zero_iff_cos_eq.mp hs with hc | hc
    · rw [hc, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_pow,
        Polynomial.Chebyshev.U_eval_one, Polynomial.Chebyshev.U_eval_one,
        Polynomial.Chebyshev.U_eval_one]
      push_cast
      ring
    · rw [hc, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_pow,
        Polynomial.Chebyshev.U_eval_neg_one, Polynomial.Chebyshev.U_eval_neg_one,
        Polynomial.Chebyshev.U_eval_neg_one]
      push_cast
      have heven : Even (2 * (n : ℤ) + 2) := ⟨n + 1, by ring⟩
      rw [Int.negOnePow_even _ heven]
      norm_num
      rw [mul_pow, mul_pow]
      simp only [← pow_mul]
      norm_num
      ring
  · have h1 := Polynomial.Chebyshev.U_complex_cos θ ((n + 1 : ℕ) : ℤ)
    have h0 := Polynomial.Chebyshev.U_complex_cos θ (n : ℤ)
    have h2 := Polynomial.Chebyshev.U_complex_cos θ ((2 * n + 2 : ℕ) : ℤ)
    have e1 := (eq_div_iff hs).2 h1
    have e0 := (eq_div_iff hs).2 h0
    have e2 := (eq_div_iff hs).2 h2
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_pow, e1, e0, e2]
    field_simp
    have htrig := complex_sin_sq_step (((n + 1 : ℕ) : ℂ) * θ) θ
    push_cast at htrig ⊢
    convert htrig using 1 <;> ring

private lemma cheb_U_sq_sub_real (n : ℕ) :
    Polynomial.Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ) ^ 2 -
        Polynomial.Chebyshev.U ℝ (n : ℤ) ^ 2 =
      Polynomial.Chebyshev.U ℝ ((2 * n + 2 : ℕ) : ℤ) := by
  apply Polynomial.map_injective Complex.ofRealHom Complex.ofReal_injective
  simpa using cheb_U_sq_sub n

private lemma cheb_U_even_eval (r : ℕ) (t : ℝ) :
    (Polynomial.Chebyshev.U ℝ ((2 * r : ℕ) : ℤ)).eval (Real.cos (t / 2)) =
      1 + 2 * ∑ j ∈ Finset.range r, Real.cos (((j + 1 : ℕ) : ℝ) * t) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [show 2 * (r + 1) = 2 * r + 2 by omega]
      have hidx : ((2 * r + 2 : ℕ) : ℤ) = 2 * (r : ℤ) + 2 := by omega
      rw [hidx, Polynomial.Chebyshev.U_eq_two_mul_T_add_U ℝ (2 * r : ℤ)]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
      rw [Polynomial.Chebyshev.T_real_cos]
      have ih' :
          (Polynomial.Chebyshev.U ℝ (2 * (r : ℤ))).eval (Real.cos (t / 2)) =
            1 + 2 * ∑ j ∈ Finset.range r,
              Real.cos (((j + 1 : ℕ) : ℝ) * t) := by
        convert ih using 1 <;> norm_num
      rw [ih', Finset.sum_range_succ]
      have harg : ((((2 * (r : ℤ) + 2 : ℤ) : ℝ)) * (t / 2)) =
          ((r + 1 : ℕ) : ℝ) * t := by
        push_cast
        ring
      rw [harg]
      ring

/-- At [a nonnegative integer order](hyp:n) and [a real angle](hyp:t), [the square of the
corresponding Chebyshev polynomial of the second kind equals its finite cosine expansion](goal). -/
lemma cheb_U_sq_eval (n : ℕ) (t : ℝ) :
    (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval (Real.cos (t / 2)) ^ 2 =
      (n + 1 : ℝ) + 2 * ∑ j ∈ Finset.range n,
        (n - j : ℝ) * Real.cos (((j + 1 : ℕ) : ℝ) * t) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hd := congrArg (fun p : Polynomial ℝ => p.eval (Real.cos (t / 2)))
        (cheb_U_sq_sub_real n)
      simp only [Polynomial.eval_sub, Polynomial.eval_pow] at hd
      calc
        (Polynomial.Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ)).eval
              (Real.cos (t / 2)) ^ 2 =
            (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval (Real.cos (t / 2)) ^ 2 +
              (Polynomial.Chebyshev.U ℝ ((2 * n + 2 : ℕ) : ℤ)).eval
                (Real.cos (t / 2)) := by linarith
        _ = ((n + 1 : ℝ) + 2 * ∑ j ∈ Finset.range n,
              (n - j : ℝ) * Real.cos (((j + 1 : ℕ) : ℝ) * t)) +
            (1 + 2 * ∑ j ∈ Finset.range (n + 1),
              Real.cos (((j + 1 : ℕ) : ℝ) * t)) := by
                rw [ih]
                convert congrArg (fun z : ℝ =>
                  ((n + 1 : ℝ) + 2 * ∑ j ∈ Finset.range n,
                    (n - j : ℝ) * Real.cos (((j + 1 : ℕ) : ℝ) * t)) + z)
                    (cheb_U_even_eval (n + 1) t) using 1 <;> congr 3 <;> omega
        _ = (((n + 1 : ℕ) : ℝ) + 1) + 2 * ∑ j ∈ Finset.range (n + 1),
              ((((n + 1 : ℕ) : ℝ) - (j : ℝ)) *
                Real.cos (((j + 1 : ℕ) : ℝ) * t)) := by
          have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
          rw [hcast, Finset.sum_range_succ, Finset.sum_range_succ]
          have hsum :
              (∑ j ∈ Finset.range n,
                  (n - j : ℝ) * Real.cos (((j + 1 : ℕ) : ℝ) * t)) +
                ∑ j ∈ Finset.range n, Real.cos (((j + 1 : ℕ) : ℝ) * t) =
              ∑ j ∈ Finset.range n,
                (n + 1 - j : ℝ) * Real.cos (((j + 1 : ℕ) : ℝ) * t) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j hj
            ring
          linear_combination 2 * hsum

/-- For [a strictly positive integer frequency](hyp:n,hn), [the cosine of that frequency has
integral zero over the closed interval from negative π to π](goal). -/
lemma integral_cos_nat (n : ℕ) (hn : 0 < n) :
    (∫ t in Set.Icc (-Real.pi) Real.pi, Real.cos ((n : ℝ) * t)) = 0 := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (a := -Real.pi) (b := Real.pi)
      (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [intervalIntegral.integral_comp_mul_left Real.cos hn0, integral_cos]
  simp

private lemma integral_cos_int (k : ℤ) (hk : k ≠ 0) :
    (∫ t in Set.Icc (-Real.pi) Real.pi, Real.cos ((k : ℝ) * t)) = 0 := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (a := -Real.pi) (b := Real.pi)
      (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  rw [intervalIntegral.integral_comp_mul_left Real.cos hk0, integral_cos]
  simp

/-- For [a real constant](hyp:c), [its integral over the closed interval from negative π to π
equals twice π times that constant](goal). -/
lemma integral_const_Icc (c : ℝ) :
    (∫ _t in Set.Icc (-Real.pi) Real.pi, c) = 2 * Real.pi * c := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (a := -Real.pi) (b := Real.pi)
      (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  have hc : True ∨ c = 0 := Or.inl trivial
  simp [hc]
  ring
  exact hc

private lemma integral_cos_mul_cos (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (∫ t in Set.Icc (-Real.pi) Real.pi,
      Real.cos ((m : ℝ) * t) * Real.cos ((n : ℝ) * t)) =
        if m = n then Real.pi else 0 := by
  have hpoint (t : ℝ) :
      Real.cos ((m : ℝ) * t) * Real.cos ((n : ℝ) * t) =
        (Real.cos (((m : ℤ) - (n : ℤ) : ℤ) * t) +
          Real.cos (((m : ℤ) + (n : ℤ) : ℤ) * t)) / 2 := by
    have hsub : ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t) =
        (m : ℝ) * t - (n : ℝ) * t := by push_cast; ring
    have hadd : ((((m : ℤ) + (n : ℤ) : ℤ) : ℝ) * t) =
        (m : ℝ) * t + (n : ℝ) * t := by push_cast; ring
    rw [hsub, hadd, Real.cos_sub, Real.cos_add]
    ring
  simp_rw [hpoint]
  rw [MeasureTheory.integral_div]
  have hi₁ : IntegrableOn (fun t : ℝ =>
      Real.cos ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t))
      (Set.Icc (-Real.pi) Real.pi) := by
    exact (show Continuous (fun t : ℝ =>
      Real.cos ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t)) by fun_prop).continuousOn
        |>.integrableOn_compact isCompact_Icc
  have hi₂ : IntegrableOn (fun t : ℝ =>
      Real.cos ((((m : ℤ) + (n : ℤ) : ℤ) : ℝ) * t))
      (Set.Icc (-Real.pi) Real.pi) := by
    exact (show Continuous (fun t : ℝ =>
      Real.cos ((((m : ℤ) + (n : ℤ) : ℤ) : ℝ) * t)) by fun_prop).continuousOn
        |>.integrableOn_compact isCompact_Icc
  rw [MeasureTheory.integral_add hi₁ hi₂]
  by_cases hmn : m = n
  · subst n
    simp only [sub_self, Int.cast_zero, zero_mul, Real.cos_zero]
    rw [show (∫ _t in Set.Icc (-Real.pi) Real.pi, (1 : ℝ)) = 2 * Real.pi by
      simp [Real.pi_pos.le]; ring]
    rw [integral_cos_int ((m : ℤ) + (m : ℤ)) (by omega)]
    simp
  · rw [if_neg hmn]
    have hsub0 : (m : ℤ) - (n : ℤ) ≠ 0 := by omega
    have hadd0 : (m : ℤ) + (n : ℤ) ≠ 0 := by omega
    rw [integral_cos_int _ hsub0, integral_cos_int _ hadd0]
    norm_num

/-- Given [a number of cosine terms](hyp:N), [a constant coefficient](hyp:c), and [a sequence of
cosine coefficients](hyp:a), [the integral over the closed interval from negative π to π of
the squared finite cosine sum equals twice π times the squared constant coefficient plus π
times the sum of the squared cosine coefficients](goal). -/
lemma integral_sq_cos_sum (N : ℕ) (c : ℝ) (a : ℕ → ℝ) :
    (∫ t in Set.Icc (-Real.pi) Real.pi,
      (c + ∑ j ∈ Finset.range N,
        a j * Real.cos (((j + 1 : ℕ) : ℝ) * t)) ^ 2) =
      2 * Real.pi * c ^ 2 + Real.pi * ∑ j ∈ Finset.range N, (a j) ^ 2 := by
  let S : ℝ → ℝ := fun t => ∑ j ∈ Finset.range N,
    a j * Real.cos (((j + 1 : ℕ) : ℝ) * t)
  have hcontS : Continuous S := by dsimp [S]; fun_prop
  have hzero : (∫ t in Set.Icc (-Real.pi) Real.pi, S t) = 0 := by
    dsimp [S]
    calc
      (∫ t in Set.Icc (-Real.pi) Real.pi, ∑ j ∈ Finset.range N,
          a j * Real.cos (((j + 1 : ℕ) : ℝ) * t)) =
          ∑ j ∈ Finset.range N, ∫ t in Set.Icc (-Real.pi) Real.pi,
            a j * Real.cos (((j + 1 : ℕ) : ℝ) * t) :=
        MeasureTheory.integral_finsetSum (Finset.range N) (by
          intro j hj
          exact (show Continuous (fun t : ℝ =>
            a j * Real.cos (((j + 1 : ℕ) : ℝ) * t)) by fun_prop).continuousOn
              |>.integrableOn_compact isCompact_Icc)
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [MeasureTheory.integral_const_mul, integral_cos_nat (j + 1) (by omega)]
        ring
  have hsq : (∫ t in Set.Icc (-Real.pi) Real.pi, (S t) ^ 2) =
      Real.pi * ∑ j ∈ Finset.range N, (a j) ^ 2 := by
    have hterm (i j : ℕ) : IntegrableOn (fun t : ℝ =>
        (a i * a j) * (Real.cos (((i + 1 : ℕ) : ℝ) * t) *
          Real.cos (((j + 1 : ℕ) : ℝ) * t))) (Set.Icc (-Real.pi) Real.pi) := by
      exact (show Continuous (fun t : ℝ =>
        (a i * a j) * (Real.cos (((i + 1 : ℕ) : ℝ) * t) *
          Real.cos (((j + 1 : ℕ) : ℝ) * t))) by fun_prop).continuousOn
            |>.integrableOn_compact isCompact_Icc
    have hexpand : (fun t => (S t) ^ 2) = fun t =>
        ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          (a i * a j) * (Real.cos (((i + 1 : ℕ) : ℝ) * t) *
            Real.cos (((j + 1 : ℕ) : ℝ) * t)) := by
      funext t
      dsimp [S]
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hexpand]
    calc
      (∫ t in Set.Icc (-Real.pi) Real.pi,
          ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
            (a i * a j) * (Real.cos (((i + 1 : ℕ) : ℝ) * t) *
              Real.cos (((j + 1 : ℕ) : ℝ) * t))) =
          ∑ i ∈ Finset.range N, ∫ t in Set.Icc (-Real.pi) Real.pi,
            ∑ j ∈ Finset.range N,
              (a i * a j) * (Real.cos (((i + 1 : ℕ) : ℝ) * t) *
                Real.cos (((j + 1 : ℕ) : ℝ) * t)) :=
        MeasureTheory.integral_finsetSum (Finset.range N) (by
          intro i hi
          exact integrable_finsetSum (Finset.range N) (fun j hj => hterm i j))
      _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
            ∫ t in Set.Icc (-Real.pi) Real.pi,
              (a i * a j) * (Real.cos (((i + 1 : ℕ) : ℝ) * t) *
                Real.cos (((j + 1 : ℕ) : ℝ) * t)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact MeasureTheory.integral_finsetSum (Finset.range N) (by
            intro j hj
            exact hterm i j)
      _ = Real.pi * ∑ j ∈ Finset.range N, (a j) ^ 2 := by
        calc
          ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
              ∫ t in Set.Icc (-Real.pi) Real.pi,
                (a i * a j) * (Real.cos (((i + 1 : ℕ) : ℝ) * t) *
                  Real.cos (((j + 1 : ℕ) : ℝ) * t)) =
              ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
                (a i * a j) * (if i = j then Real.pi else 0) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            rw [MeasureTheory.integral_const_mul,
              integral_cos_mul_cos (i + 1) (j + 1) (by omega) (by omega)]
            simp
          _ = Real.pi * ∑ j ∈ Finset.range N, (a j) ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.sum_eq_single j]
            · simp
              ring
            · intro b hb hbj
              simp [hbj.symm]
            · exact fun hnot => (hnot hj).elim
  have hconst : (∫ _t in Set.Icc (-Real.pi) Real.pi, c ^ 2) =
      2 * Real.pi * c ^ 2 := by
    exact integral_const_Icc (c ^ 2)
  have hpoint : (fun t => (c + S t) ^ 2) =
      fun t => c ^ 2 + (2 * c) * S t + (S t) ^ 2 := by
    funext t
    ring
  rw [show (fun t => (c + ∑ j ∈ Finset.range N,
      a j * Real.cos (((j + 1 : ℕ) : ℝ) * t)) ^ 2) =
      fun t => (c + S t) ^ 2 by rfl, hpoint]
  have hiConst : IntegrableOn (fun _t : ℝ => c ^ 2) (Set.Icc (-Real.pi) Real.pi) :=
    continuous_const.continuousOn.integrableOn_compact isCompact_Icc
  have hiLin : IntegrableOn (fun t => (2 * c) * S t) (Set.Icc (-Real.pi) Real.pi) :=
    (continuous_const.mul hcontS).continuousOn.integrableOn_compact isCompact_Icc
  have hiSq : IntegrableOn (fun t => (S t) ^ 2) (Set.Icc (-Real.pi) Real.pi) :=
    (hcontS.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  calc
    (∫ t in Set.Icc (-Real.pi) Real.pi, c ^ 2 + (2 * c) * S t + S t ^ 2) =
        (∫ t in Set.Icc (-Real.pi) Real.pi, c ^ 2 + (2 * c) * S t) +
          ∫ t in Set.Icc (-Real.pi) Real.pi, S t ^ 2 := by
      exact MeasureTheory.integral_add (hiConst.add hiLin) hiSq
    _ = ((∫ _t in Set.Icc (-Real.pi) Real.pi, c ^ 2) +
          ∫ t in Set.Icc (-Real.pi) Real.pi, (2 * c) * S t) +
          ∫ t in Set.Icc (-Real.pi) Real.pi, S t ^ 2 := by
      rw [MeasureTheory.integral_add hiConst hiLin]
    _ = 2 * Real.pi * c ^ 2 + Real.pi * ∑ j ∈ Finset.range N, (a j) ^ 2 := by
      rw [MeasureTheory.integral_const_mul, hzero, hsq, hconst]
      ring

/-- For [a nonnegative integer](hyp:n), [the sum of the squared integers from one through that
integer equals that integer times its successor times one more than twice it, divided by
six](goal). -/
lemma sum_range_sub_sq (n : ℕ) :
    ∑ j ∈ Finset.range n, ((n : ℝ) - (j : ℝ)) ^ 2 =
      (n : ℝ) * (n + 1) * (2 * n + 1) / 6 := by
  calc
    ∑ j ∈ Finset.range n, ((n : ℝ) - (j : ℝ)) ^ 2 =
        ∑ j ∈ Finset.range n, (((n - 1 - j : ℕ) : ℝ) + 1) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      have hnat : n - j = n - 1 - j + 1 := by omega
      rw [show (n : ℝ) - (j : ℝ) = ((n - j : ℕ) : ℝ) by
        rw [Nat.cast_sub (Nat.le_of_lt hj)]]
      norm_num [hnat]
    _ = ∑ j ∈ Finset.range n, ((j : ℝ) + 1) ^ 2 :=
      Finset.sum_range_reflect (fun j : ℕ => ((j : ℝ) + 1) ^ 2) n
    _ = (n : ℝ) * (n + 1) * (2 * n + 1) / 6 := by
      induction n with
      | zero => norm_num
      | succ n ih =>
          rw [Finset.sum_range_succ, ih]
          push_cast
          ring

/-- For [integer order K](hyp:K), [the raw Jackson kernel is continuous on the real line](goal).
-/
@[fun_prop]
theorem continuous_jraw (K : ℕ) : Continuous (jraw K) := by
  by_cases hK : K = 0
  · subst K
    convert (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ))) using 1
    funext t
    simp [jraw]
  · have hKpos : 0 < K := Nat.pos_of_ne_zero hK
    rw [show jraw K = fun t =>
        ((Polynomial.Chebyshev.U ℝ ((K - 1 : ℕ) : ℤ)).eval (Real.cos (t / 2))) ^ 4 by
      funext t
      exact jraw_eq_chebyshev K hKpos t]
    fun_prop

/-- For [integer order K](hyp:K), [the raw Jackson kernel is Borel measurable](goal).
-/
@[measurability, fun_prop]
theorem measurable_jraw (K : ℕ) : Measurable (jraw K) := by
  exact (continuous_jraw K).measurable

/-- For [integer order K](hyp:K), [the raw Jackson kernel is integrable over the standard
period](goal).
-/
theorem integrableOn_jraw (K : ℕ) : IntegrableOn (jraw K) (Set.Icc (-Real.pi) Real.pi) := by
  exact (continuous_jraw K).continuousOn.integrableOn_compact isCompact_Icc

/-- At [integer order K](hyp:K) and [real argument t](hyp:t), [the raw Jackson kernel is
nonnegative](goal).
-/
theorem jraw_nonneg (K : ℕ) (t : ℝ) : 0 ≤ jraw K t := by
  unfold jraw
  split_ifs <;> positivity

/-- For [integer order K](hyp:K), [the raw Jackson kernel is symmetric about zero](goal).
-/
theorem jraw_even (K : ℕ) : Function.Even (jraw K) := by
  intro t
  by_cases ht : Real.sin (t / 2) = 0
  · have hnt : Real.sin (-t / 2) = 0 := by
      rw [show -t / 2 = -(t / 2) by ring, Real.sin_neg, ht, neg_zero]
    rw [jraw_eq_of_sin_eq_zero K hnt, jraw_eq_of_sin_eq_zero K ht]
  · have hnt : Real.sin (-t / 2) ≠ 0 := by
      rw [show -t / 2 = -(t / 2) by ring, Real.sin_neg, neg_ne_zero]
      exact ht
    rw [jraw_eq_of_sin_ne_zero K hnt, jraw_eq_of_sin_ne_zero K ht]
    rw [show (K : ℝ) * -t / 2 = -((K : ℝ) * t / 2) by ring,
      show -t / 2 = -(t / 2) by ring, Real.sin_neg]
    have hs : Real.sin (-(t / 2)) = -Real.sin (t / 2) := Real.sin_neg _
    rw [hs]
    congr 1
    field_simp

end Causalean.Mathlib.Analysis.JacksonApproximation

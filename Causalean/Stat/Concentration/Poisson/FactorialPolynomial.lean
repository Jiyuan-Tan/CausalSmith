module
public import Causalean.Mathlib.Probability.Poisson.Moments
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.RingTheory.Binomial

/-!
# Centered Poisson falling-factorial moments

Exact first and mixed second moments of the normalized, centered falling-factorial lift. The
finite-coordinate product identities and an exponential second-moment envelope are built from the
scalar identities. No research-specific pilot or cell model occurs here.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Causalean.Stat.Concentration.Poisson

open Causalean.Mathlib.Probability.PoissonAddOnePoincare
open Finset Polynomial

private lemma poisson_descFactorial_shift (rate : NNReal) (h k : ℕ) :
    Real.exp (-(rate : ℝ)) * (rate : ℝ) ^ (k + h) /
          ((k + h).factorial : ℝ) * ((k + h).descFactorial h : ℝ) =
      ((rate : ℝ) ^ h * Real.exp (-(rate : ℝ))) *
        ((rate : ℝ) ^ k / (k.factorial : ℝ)) := by
  have hfacNat : k.factorial * (k + h).descFactorial h = (k + h).factorial := by
    simpa [Nat.add_sub_cancel] using
      (Nat.factorial_mul_descFactorial (n := k + h) (k := h) (Nat.le_add_left h k))
  have hfac : (k.factorial : ℝ) * ((k + h).descFactorial h : ℝ) =
      ((k + h).factorial : ℝ) := by
    exact_mod_cast hfacNat
  rw [pow_add]
  field_simp [Nat.factorial_ne_zero]
  linear_combination ((rate : ℝ) ^ k * (rate : ℝ) ^ h) * hfac

private lemma summable_poisson_descFactorial (rate : NNReal) (h : ℕ) :
    Summable (fun N : ℕ =>
      Real.exp (-(rate : ℝ)) * (rate : ℝ) ^ N / (N.factorial : ℝ) *
        (N.descFactorial h : ℝ)) := by
  let f : ℕ → ℝ := fun N =>
    Real.exp (-(rate : ℝ)) * (rate : ℝ) ^ N / (N.factorial : ℝ) *
      (N.descFactorial h : ℝ)
  have hshift : Summable (fun k => f (k + h)) := by
    apply Summable.congr
      ((NormedSpace.expSeries_div_hasSum_exp (rate : ℝ)).summable.mul_left
        ((rate : ℝ) ^ h * Real.exp (-(rate : ℝ))))
    intro k
    exact (poisson_descFactorial_shift rate h k).symm
  exact (summable_nat_add_iff h).mp hshift

/-- [a normalization, center, natural count, and order](hyp:m,z,N,h) determine [the normalized centered falling-factorial lift](goal).

The normalized falling-factorial lift of `(q-z)^h`, evaluated at a natural count.
-/
def factorialLift (m z : ℝ) (N h : ℕ) : ℝ :=
  ∑ t ∈ Finset.range (h + 1),
    (h.choose t : ℝ) * (-z) ^ (h - t) * (N.descFactorial t : ℝ) / m ^ t

/-- The falling factorial of a Poisson count has mean equal to the corresponding power of its
rate. A direct proof shifts the Poisson series by `h` and cancels factorials.
-/
theorem poisson_descFactorial_moment (rate : NNReal) (h : ℕ) :
    (∫ N : ℕ, (N.descFactorial h : ℝ) ∂poissonMeasure rate) =
      (rate : ℝ) ^ h := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  let f : ℕ → ℝ := fun N =>
    Real.exp (-(rate : ℝ)) * (rate : ℝ) ^ N / (N.factorial : ℝ) *
      (N.descFactorial h : ℝ)
  have hshift : Summable (fun k => f (k + h)) :=
    (summable_nat_add_iff h).mpr (summable_poisson_descFactorial rate h)
  have hprefix : ∑ k ∈ Finset.range h, f k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkh : k < h := Finset.mem_range.mp hk
    simp [f, Nat.descFactorial_eq_zero_iff_lt.mpr hkh]
  calc
    ∑' N, Real.exp (-(rate : ℝ)) * (rate : ℝ) ^ N / ↑N.factorial *
        ↑(N.descFactorial h) = ∑' N, f N := by rfl
    _ = ∑ k ∈ Finset.range h, f k + ∑' k, f (k + h) :=
      (hshift.sum_add_tsum_nat_add').symm
    _ = ∑' k, (((rate : ℝ) ^ h * Real.exp (-(rate : ℝ))) *
        ((rate : ℝ) ^ k / (k.factorial : ℝ))) := by
      rw [hprefix, zero_add]
      congr 1
      funext k
      exact poisson_descFactorial_shift rate h k
    _ = ((rate : ℝ) ^ h * Real.exp (-(rate : ℝ))) * Real.exp (rate : ℝ) := by
      rw [tsum_mul_left]
      simpa only [Real.exp_eq_exp_ℝ] using congrArg
        (fun z : ℝ => ((rate : ℝ) ^ h * Real.exp (-(rate : ℝ))) * z)
        (NormedSpace.expSeries_div_hasSum_exp (rate : ℝ)).tsum_eq
    _ = (rate : ℝ) ^ h := by
      rw [mul_assoc, ← Real.exp_add]
      ring_nf
      simp

private lemma descPochhammer_mul_linearization (h t : ℕ) :
    descPochhammer ℤ h * descPochhammer ℤ t =
      ∑ r ∈ Finset.range (min h t + 1),
        Polynomial.C (Nat.choose h r * Nat.choose t r * r.factorial : ℤ) *
          descPochhammer ℤ (h + t - r) := by
  classical
  wlog hht : h ≤ t generalizing h t
  · rw [mul_comm]
    simpa [Nat.min_comm, mul_comm, Nat.add_comm] using this t h (le_of_not_ge hht)
  rw [Nat.min_eq_left hht]
  have hadd := Ring.descPochhammer_smeval_add (R := ℤ[X]) t
    (Commute.all (X - C (h : ℤ)) (C (h : ℤ)))
  simp only [sub_add_cancel] at hadd
  have hsX (p : ℤ[X]) : p.smeval X = p := by
    rw [← Polynomial.eval₂_smulOneHom_eq_smeval]
    simpa using Polynomial.eval₂_C_X p
  have hscomp (p : ℤ[X]) : p.smeval (X - C (h : ℤ)) =
      p.comp (X - C (h : ℤ)) := by
    rw [← Polynomial.eval₂_smulOneHom_eq_smeval]
    have hhom : (RingHom.smulOneHom : ℤ →+* ℤ[X]) = C := by
      ext z
      simp
    rw [hhom]
    rfl
  have hsC (p : ℤ[X]) : p.smeval (C (h : ℤ)) = C (p.eval (h : ℤ)) := by
    rw [← Polynomial.eval₂_smulOneHom_eq_smeval]
    simpa using Polynomial.eval₂_at_apply C (h : ℤ) (p := p)
  simp only [hsX, hscomp, hsC] at hadd
  rw [← Finset.Nat.sum_antidiagonal_swap] at hadd
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hadd
  simp only [Prod.swap, Prod.fst, Prod.snd, Nat.succ_eq_add_one] at hadd
  have heval (r : ℕ) : (descPochhammer ℤ r).eval (h : ℤ) =
      (h.descFactorial r : ℤ) := by
    simpa [Polynomial.eval_eq_smeval] using
      (Polynomial.descPochhammer_smeval_eq_descFactorial (R := ℤ) h r)
  have htform : descPochhammer ℤ t =
      ∑ r ∈ range (t + 1),
        C ((t.choose r : ℤ) * (h.descFactorial r : ℤ)) *
          (descPochhammer ℤ (t - r)).comp (X - C (h : ℤ)) := by
    rw [hadd]
    apply Finset.sum_congr rfl
    intro r hr
    rw [heval]
    have hr' : r ≤ t := Nat.le_of_lt_succ (by simpa using Finset.mem_range.mp hr)
    rw [Nat.choose_symm hr']
    simp
    ring
  calc
    descPochhammer ℤ h * descPochhammer ℤ t =
        descPochhammer ℤ h *
          (∑ r ∈ range (t + 1),
            C ((t.choose r : ℤ) * (h.descFactorial r : ℤ)) *
              (descPochhammer ℤ (t - r)).comp (X - C (h : ℤ))) := by rw [htform]
    _ = ∑ r ∈ range (t + 1),
          C ((t.choose r : ℤ) * (h.descFactorial r : ℤ)) *
            descPochhammer ℤ (h + (t - r)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      calc
        descPochhammer ℤ h *
            (C ((t.choose r : ℤ) * (h.descFactorial r : ℤ)) *
              (descPochhammer ℤ (t - r)).comp (X - C (h : ℤ))) =
            C ((t.choose r : ℤ) * (h.descFactorial r : ℤ)) *
              (descPochhammer ℤ h *
                (descPochhammer ℤ (t - r)).comp (X - C (h : ℤ))) := by ring
        _ = _ := by
          rw [show C (h : ℤ) = (h : ℤ[X]) by simp]
          rw [descPochhammer_mul]
    _ = ∑ r ∈ range (h + 1),
          C ((t.choose r : ℤ) * (h.descFactorial r : ℤ)) *
            descPochhammer ℤ (h + (t - r)) := by
      symm
      apply Finset.sum_subset
      · intro r hr
        exact Finset.mem_range.mpr
          ((Finset.mem_range.mp hr).trans_le (Nat.succ_le_succ hht))
      · intro r hrBig hrSmall
        have hh_lt : h < r := by
          have := Finset.mem_range.mp hrBig
          simpa [Finset.mem_range] using hrSmall
        rw [Nat.descFactorial_eq_zero_iff_lt.mpr hh_lt]
        simp
    _ = ∑ r ∈ range (h + 1),
          C (Nat.choose h r * Nat.choose t r * r.factorial : ℤ) *
            descPochhammer ℤ (h + t - r) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hr' : r ≤ h := Nat.le_of_lt_succ (by simpa using Finset.mem_range.mp hr)
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      congr 1
      · push_cast
        ring
      · rw [Nat.add_sub_assoc (le_trans hr' hht) h]

/-- The product of two falling factorials expands by their overlap count. This identity is
purely combinatorial and also supplies the Poisson mixed second moment after integration.
-/
theorem descFactorial_mul (N h t : ℕ) :
    (N.descFactorial h : ℝ) * (N.descFactorial t : ℝ) =
      ∑ r ∈ Finset.range (min h t + 1),
        (h.choose r : ℝ) * (t.choose r : ℝ) * (Nat.factorial r : ℝ) *
          (N.descFactorial (h + t - r) : ℝ) := by
  have hp := congrArg (Polynomial.eval (N : ℤ))
    (descPochhammer_mul_linearization h t)
  simp only [Polynomial.eval_mul, Polynomial.eval_finsetSum, Polynomial.eval_C,
    descPochhammer_eval_eq_descFactorial] at hp
  have hn : N.descFactorial h * N.descFactorial t =
      ∑ r ∈ Finset.range (min h t + 1),
        Nat.choose h r * Nat.choose t r * r.factorial *
          N.descFactorial (h + t - r) := by
    exact_mod_cast hp
  exact_mod_cast hn

/-- Every falling factorial of a Poisson count is integrable. This is the integrability
prerequisite for passing finite falling-factorial expansions through the integral.
-/
theorem poisson_descFactorial_integrable (rate : NNReal) (h : ℕ) :
    Integrable (fun N : ℕ => (N.descFactorial h : ℝ)) (poissonMeasure rate) := by
  rw [integrable_poissonMeasure_iff]
  convert summable_poisson_descFactorial rate h using 1
  ext N
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- The mixed raw falling-factorial moment is the overlap sum of powers of the Poisson rate.
It follows by integrating `descFactorial_mul` term by term.
-/
theorem poisson_descFactorial_mixed (rate : NNReal) (h t : ℕ) :
    (∫ N : ℕ, (N.descFactorial h : ℝ) * (N.descFactorial t : ℝ)
      ∂poissonMeasure rate) =
      ∑ r ∈ Finset.range (min h t + 1),
        (h.choose r : ℝ) * (t.choose r : ℝ) * (Nat.factorial r : ℝ) *
          (rate : ℝ) ^ (h + t - r) := by
  calc
    (∫ N : ℕ, (N.descFactorial h : ℝ) * (N.descFactorial t : ℝ)
        ∂poissonMeasure rate) =
        ∫ N : ℕ, ∑ r ∈ Finset.range (min h t + 1),
          (h.choose r : ℝ) * (t.choose r : ℝ) * (Nat.factorial r : ℝ) *
            (N.descFactorial (h + t - r) : ℝ) ∂poissonMeasure rate := by
      congr 1
      funext N
      exact descFactorial_mul N h t
    _ = ∑ r ∈ Finset.range (min h t + 1),
          (h.choose r : ℝ) * (t.choose r : ℝ) * (Nat.factorial r : ℝ) *
            (rate : ℝ) ^ (h + t - r) := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro r _
        rw [integral_const_mul, poisson_descFactorial_moment]
      · intro r _
        exact (poisson_descFactorial_integrable rate (h + t - r)).const_mul _

/-- A normalized centered factorial lift under a Poisson law has expectation `(rate/m-z)^h`.
This is the exact unbiasedness identity for one coordinate.
-/
theorem poisson_factorialLift_mean (rate : NNReal) (m z : ℝ) (hm : m ≠ 0)
    (h : ℕ) :
    (∫ N : ℕ, factorialLift m z N h ∂poissonMeasure rate) =
      ((rate : ℝ) / m - z) ^ h := by
  calc
    (∫ N : ℕ, factorialLift m z N h ∂poissonMeasure rate) =
        ∫ N : ℕ, ∑ t ∈ Finset.range (h + 1),
          ((h.choose t : ℝ) * (-z) ^ (h - t) / m ^ t) *
            (N.descFactorial t : ℝ) ∂poissonMeasure rate := by
      congr 1
      funext N
      simp only [factorialLift]
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = ∑ t ∈ Finset.range (h + 1),
          ((h.choose t : ℝ) * (-z) ^ (h - t) / m ^ t) *
            (rate : ℝ) ^ t := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro t _
        rw [integral_const_mul, poisson_descFactorial_moment]
      · intro t _
        exact (poisson_descFactorial_integrable rate t).const_mul _
    _ = ((rate : ℝ) / m - z) ^ h := by
      rw [sub_eq_add_neg, add_pow]
      apply Finset.sum_congr rfl
      intro t _
      rw [div_pow]
      ring

private lemma factorialLift_shift_sum (x z : ℝ) (h r : ℕ) (hr : r ≤ h) :
    (∑ j ∈ Finset.range (h + 1),
      (h.choose j : ℝ) * (-z) ^ (h - j) * (j.choose r : ℝ) * x ^ (j - r)) =
      (h.choose r : ℝ) * (x - z) ^ (h - r) := by
  have hzero : ∑ j ∈ Finset.range r,
      (h.choose j : ℝ) * (-z) ^ (h - j) * (j.choose r : ℝ) * x ^ (j - r) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hj)]
  rw [show h + 1 = r + (h - r + 1) by omega, Finset.sum_range_add, hzero, zero_add]
  calc
    (∑ i ∈ Finset.range (h - r + 1),
      (h.choose (r + i) : ℝ) * (-z) ^ (h - (r + i)) *
        ((r + i).choose r : ℝ) * x ^ (r + i - r)) =
      (h.choose r : ℝ) *
        ∑ i ∈ Finset.range (h - r + 1),
          x ^ i * (-z) ^ (h - r - i) * ((h - r).choose i : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hchoose := Nat.choose_mul (n := h) (k := r + i) (s := r) (Nat.le_add_right r i)
      have hsub : h - (r + i) = h - r - i := by omega
      have hchoose' : (h.choose (r + i) : ℝ) * ((r + i).choose r : ℝ) =
          (h.choose r : ℝ) * ((h - r).choose i : ℝ) := by
        simpa only [Nat.add_sub_cancel_left, Nat.cast_mul] using
          congrArg (fun n : ℕ => (n : ℝ)) hchoose
      simp only [Nat.add_sub_cancel_left, hsub]
      calc
        _ = ((h.choose (r + i) : ℝ) * ((r + i).choose r : ℝ)) *
              ((-z) ^ (h - r - i) * x ^ i) := by ring
        _ = _ := by rw [hchoose']; ring
    _ = (h.choose r : ℝ) * (x - z) ^ (h - r) := by
      rw [sub_eq_add_neg, add_pow]

/-- The two binomial shifts of a finite overlap polynomial regroup into overlap powers of
`x-z`. This is the finite algebraic identity behind centered Poisson factorial mixed moments.

One proof is to fix the overlap index first, apply
`choose_mul` twice to extract `choose h r * choose t r`, and then apply the binomial theorem
to the remaining indices. No probability or convergence argument is needed here.
-/
theorem factorialLift_mixed_finite_identity (x v z : ℝ) (h t : ℕ) :
    (∑ j ∈ Finset.range (h + 1),
      ∑ k ∈ Finset.range (t + 1),
        (h.choose j : ℝ) * (t.choose k : ℝ) *
          (-z) ^ (h - j + (t - k)) *
          (∑ r ∈ Finset.range (min j k + 1),
            (j.choose r : ℝ) * (k.choose r : ℝ) *
              (Nat.factorial r : ℝ) * v ^ r * x ^ (j + k - 2 * r))) =
      ∑ r ∈ Finset.range (min h t + 1),
        (h.choose r : ℝ) * (t.choose r : ℝ) *
          (Nat.factorial r : ℝ) * v ^ r * (x - z) ^ (h + t - 2 * r) := by
  let A : ℕ → ℕ → ℝ := fun r j =>
    (h.choose j : ℝ) * (-z) ^ (h - j) * (j.choose r : ℝ) * x ^ (j - r)
  let B : ℕ → ℕ → ℝ := fun r k =>
    (t.choose k : ℝ) * (-z) ^ (t - k) * (k.choose r : ℝ) * x ^ (k - r)
  have hfactor (j k r : ℕ) :
      (h.choose j : ℝ) * (t.choose k : ℝ) *
          (-z) ^ (h - j + (t - k)) *
          ((j.choose r : ℝ) * (k.choose r : ℝ) *
            (Nat.factorial r : ℝ) * v ^ r * x ^ (j + k - 2 * r)) =
        A r j * B r k * ((Nat.factorial r : ℝ) * v ^ r) := by
    by_cases hj : r ≤ j
    · by_cases hk : r ≤ k
      · have he : j + k - 2 * r = (j - r) + (k - r) := by omega
        rw [pow_add, he, pow_add]
        dsimp [A, B]
        ring
      · have hk' : k < r := by omega
        simp [B, Nat.choose_eq_zero_of_lt hk']
    · have hj' : j < r := by omega
      simp [A, Nat.choose_eq_zero_of_lt hj']
  have hextend (j k : ℕ) (hj : j ≤ h) (hk : k ≤ t) :
      (∑ r ∈ Finset.range (min j k + 1),
        (j.choose r : ℝ) * (k.choose r : ℝ) *
          (Nat.factorial r : ℝ) * v ^ r * x ^ (j + k - 2 * r)) =
      ∑ r ∈ Finset.range (min h t + 1),
        (j.choose r : ℝ) * (k.choose r : ℝ) *
          (Nat.factorial r : ℝ) * v ^ r * x ^ (j + k - 2 * r) := by
    apply Finset.sum_subset ?_ ?_
    · intro r hr
      simp only [Finset.mem_range] at hr ⊢
      have hm : min j k ≤ min h t := min_le_min hj hk
      omega
    · intro r hr hr'
      simp only [Finset.mem_range] at hr hr'
      have hlt : min j k < r := by omega
      rcases le_total j k with hle | hle
      · have : j < r := by simpa [Nat.min_eq_left hle] using hlt
        simp [Nat.choose_eq_zero_of_lt this]
      · have : k < r := by simpa [Nat.min_eq_right hle] using hlt
        simp [Nat.choose_eq_zero_of_lt this]
  calc
    (∑ j ∈ Finset.range (h + 1),
      ∑ k ∈ Finset.range (t + 1),
        (h.choose j : ℝ) * (t.choose k : ℝ) *
          (-z) ^ (h - j + (t - k)) *
          (∑ r ∈ Finset.range (min j k + 1),
            (j.choose r : ℝ) * (k.choose r : ℝ) *
              (Nat.factorial r : ℝ) * v ^ r * x ^ (j + k - 2 * r))) =
      ∑ j ∈ Finset.range (h + 1),
        ∑ k ∈ Finset.range (t + 1),
          ∑ r ∈ Finset.range (min h t + 1),
            A r j * B r k * ((Nat.factorial r : ℝ) * v ^ r) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      rw [hextend j k (by simpa using hj) (by simpa using hk)]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      exact hfactor j k r
    _ = ∑ r ∈ Finset.range (min h t + 1),
          ((∑ j ∈ Finset.range (h + 1), A r j) *
            (∑ k ∈ Finset.range (t + 1), B r k)) *
            ((Nat.factorial r : ℝ) * v ^ r) := by
      have hswap (j : ℕ) :
          (∑ k ∈ Finset.range (t + 1),
            ∑ r ∈ Finset.range (min h t + 1),
              A r j * B r k * ((Nat.factorial r : ℝ) * v ^ r)) =
          ∑ r ∈ Finset.range (min h t + 1),
            ∑ k ∈ Finset.range (t + 1),
              A r j * B r k * ((Nat.factorial r : ℝ) * v ^ r) :=
        Finset.sum_comm
      simp_rw [hswap]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      calc
        (∑ j ∈ Finset.range (h + 1),
          ∑ k ∈ Finset.range (t + 1),
            A r j * B r k * ((Nat.factorial r : ℝ) * v ^ r)) =
          (∑ j ∈ Finset.range (h + 1),
            ∑ k ∈ Finset.range (t + 1), A r j * B r k) *
              ((Nat.factorial r : ℝ) * v ^ r) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.sum_mul]
        _ = _ := by rw [Finset.sum_mul_sum]
    _ = ∑ r ∈ Finset.range (min h t + 1),
          (h.choose r : ℝ) * (t.choose r : ℝ) *
            (Nat.factorial r : ℝ) * v ^ r * (x - z) ^ (h + t - 2 * r) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrh : r ≤ h := by have := Finset.mem_range.mp hr; omega
      have hrt : r ≤ t := by have := Finset.mem_range.mp hr; omega
      rw [show (∑ j ∈ Finset.range (h + 1), A r j) =
          (h.choose r : ℝ) * (x - z) ^ (h - r) from factorialLift_shift_sum x z h r hrh]
      rw [show (∑ k ∈ Finset.range (t + 1), B r k) =
          (t.choose r : ℝ) * (x - z) ^ (t - r) from factorialLift_shift_sum x z t r hrt]
      have he : h + t - 2 * r = (h - r) + (t - r) := by omega
      rw [he, pow_add]
      ring

/-- The Poisson mixed moment of two centered factorial lifts expands as a finite double
binomial sum of raw falling-factorial overlap moments. The factors `x=rate/m` and
`v=rate/m²` separate centering from Poisson variance.

Expand both lifts, distribute the product, integrate the finite sums using
`poisson_descFactorial_mixed`, then rewrite each power of the rate and `m`.
-/
theorem poisson_factorialLift_mixed_expansion (rate : NNReal) (m z : ℝ)
    (hm : m ≠ 0) (h t : ℕ) :
    (∫ N : ℕ, factorialLift m z N h * factorialLift m z N t
      ∂poissonMeasure rate) =
      ∑ j ∈ Finset.range (h + 1),
        ∑ k ∈ Finset.range (t + 1),
          (h.choose j : ℝ) * (t.choose k : ℝ) *
            (-z) ^ (h - j + (t - k)) *
            (∑ r ∈ Finset.range (min j k + 1),
              (j.choose r : ℝ) * (k.choose r : ℝ) *
                (Nat.factorial r : ℝ) * ((rate : ℝ) / m ^ 2) ^ r *
                ((rate : ℝ) / m) ^ (j + k - 2 * r)) := by
  have hraw (j k : ℕ) :
      Integrable (fun N : ℕ => (N.descFactorial j : ℝ) *
        (N.descFactorial k : ℝ)) (poissonMeasure rate) := by
    have h := integrable_finsetSum (Finset.range (min j k + 1))
      (fun r _ => (poisson_descFactorial_integrable rate (j + k - r)).const_mul
        ((j.choose r : ℝ) * (k.choose r : ℝ) * (Nat.factorial r : ℝ)))
    have heq : (fun N : ℕ => (N.descFactorial j : ℝ) *
        (N.descFactorial k : ℝ)) =
        (fun N : ℕ => ∑ r ∈ Finset.range (min j k + 1),
          (j.choose r : ℝ) * (k.choose r : ℝ) *
            (Nat.factorial r : ℝ) * (N.descFactorial (j + k - r) : ℝ)) := by
      funext N
      exact descFactorial_mul N j k
    rw [heq]
    exact h
  have hnormalize (j k r : ℕ) (hr : r ≤ min j k) :
      (rate : ℝ) ^ (j + k - r) / (m ^ j * m ^ k) =
        ((rate : ℝ) / m ^ 2) ^ r *
          ((rate : ℝ) / m) ^ (j + k - 2 * r) := by
    have h₁ : j + k - r = r + (j + k - 2 * r) := by omega
    have h₂ : j + k = 2 * r + (j + k - 2 * r) := by omega
    calc
      (rate : ℝ) ^ (j + k - r) / (m ^ j * m ^ k) =
          (rate : ℝ) ^ r * (rate : ℝ) ^ (j + k - 2 * r) /
            (m ^ (2 * r) * m ^ (j + k - 2 * r)) := by
        have hden : m ^ j * m ^ k =
            m ^ (2 * r) * m ^ (j + k - 2 * r) := by
          calc
            m ^ j * m ^ k = m ^ (j + k) := (pow_add m j k).symm
            _ = m ^ (2 * r + (j + k - 2 * r)) :=
              congrArg (fun n : ℕ => m ^ n) h₂
            _ = _ := pow_add m (2 * r) (j + k - 2 * r)
        rw [h₁, pow_add, hden]
      _ = ((rate : ℝ) / m ^ 2) ^ r *
            ((rate : ℝ) / m) ^ (j + k - 2 * r) := by
        rw [div_pow, div_pow, pow_mul]
        field_simp [hm]
  calc
    (∫ N : ℕ, factorialLift m z N h * factorialLift m z N t
      ∂poissonMeasure rate) =
        ∫ N : ℕ, ∑ j ∈ Finset.range (h + 1),
          ∑ k ∈ Finset.range (t + 1),
            ((h.choose j : ℝ) * (t.choose k : ℝ) *
              (-z) ^ (h - j + (t - k)) / (m ^ j * m ^ k)) *
              ((N.descFactorial j : ℝ) * (N.descFactorial k : ℝ))
          ∂poissonMeasure rate := by
      congr 1
      funext N
      simp only [factorialLift, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_add]
      ring
    _ = ∑ j ∈ Finset.range (h + 1),
          ∑ k ∈ Finset.range (t + 1),
            ((h.choose j : ℝ) * (t.choose k : ℝ) *
              (-z) ^ (h - j + (t - k)) / (m ^ j * m ^ k)) *
              (∑ r ∈ Finset.range (min j k + 1),
                (j.choose r : ℝ) * (k.choose r : ℝ) *
                  (Nat.factorial r : ℝ) * (rate : ℝ) ^ (j + k - r)) := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro j _
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro k _
          rw [integral_const_mul, poisson_descFactorial_mixed]
        · intro k _
          exact (hraw j k).const_mul _
      · intro j _
        exact integrable_finsetSum _ (fun k _ => (hraw j k).const_mul _)
    _ = ∑ j ∈ Finset.range (h + 1),
          ∑ k ∈ Finset.range (t + 1),
            (h.choose j : ℝ) * (t.choose k : ℝ) *
              (-z) ^ (h - j + (t - k)) *
              (∑ r ∈ Finset.range (min j k + 1),
                (j.choose r : ℝ) * (k.choose r : ℝ) *
                  (Nat.factorial r : ℝ) * ((rate : ℝ) / m ^ 2) ^ r *
                  ((rate : ℝ) / m) ^ (j + k - 2 * r)) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      have hr' : r ≤ min j k := by
        have := Finset.mem_range.mp hr
        omega
      calc
        _ = (h.choose j : ℝ) * (t.choose k : ℝ) *
            (-z) ^ (h - j + (t - k)) *
            ((j.choose r : ℝ) * (k.choose r : ℝ) *
              (Nat.factorial r : ℝ) *
              ((rate : ℝ) ^ (j + k - r) / (m ^ j * m ^ k))) := by ring
        _ = _ := by rw [hnormalize j k r hr']; ring

/-- [A Poisson rate](hyp:rate), [normalization and centering parameters](hyp:m,z), [a nonzero normalization](hyp:hm), and [two factorial orders](hyp:h,t) give [the exact overlap-sum formula for their centered factorial-lift mixed moment](goal).

Two centered factorial lifts under one Poisson law have a mixed moment given by their
overlap sum. It specializes to the exact square moment when `h=t`.

Combine `poisson_factorialLift_mixed_expansion` and `factorialLift_mixed_finite_identity`.
-/
theorem poisson_factorialLift_mixed (rate : NNReal) (m z : ℝ) (hm : m ≠ 0)
    (h t : ℕ) :
    (∫ N : ℕ, factorialLift m z N h * factorialLift m z N t
      ∂poissonMeasure rate) =
      ∑ r ∈ Finset.range (min h t + 1),
        (h.choose r : ℝ) * (t.choose r : ℝ) * (Nat.factorial r : ℝ) *
          ((rate : ℝ) / m ^ 2) ^ r *
          ((rate : ℝ) / m - z) ^ (h + t - 2 * r) := by
  exact (poisson_factorialLift_mixed_expansion rate m z hm h t).trans
    (factorialLift_mixed_finite_identity ((rate : ℝ) / m)
      ((rate : ℝ) / m ^ 2) z h t)

end Causalean.Stat.Concentration.Poisson


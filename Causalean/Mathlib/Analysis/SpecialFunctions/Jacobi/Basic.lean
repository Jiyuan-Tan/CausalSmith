module
public import Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi.EndpointEnergy
public import Mathlib

/-!
# Shifted Jacobi polynomials and their endpoint bound

The finite hypergeometric sum below is the Jacobi polynomial
`Pₖ^(α,β)(1 - 2x)` divided by `Pₖ^(α,β)(1)`.  In particular its
value at zero is one.  The parameter range in `jacobiShifted_abs_le_one`
is exactly the range of DLMF 18.14.1 after shifting `[-1,1]` to `[0,1]`.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi

open Polynomial

/-- A [real starting value](hyp:a) and [natural index](hyp:n) determine [the rising factorial](goal), [given by evaluating the corresponding rising-factorial polynomial](step:1).

The rising factorial `(a)ₙ`, evaluated as a real polynomial. -/
noncomputable def rising (a : ℝ) (n : ℕ) : ℝ :=
  (ascPochhammer ℝ n).eval a

/-- A [degree](hyp:k), [first shape parameter](hyp:α), [second shape parameter](hyp:β), and [evaluation point](hyp:x) determine [the normalized shifted Jacobi polynomial](goal), [given by its finite hypergeometric sum](step:1).

The normalized Jacobi polynomial `Pₖ^(α,β)(1 - 2x) / Pₖ^(α,β)(1)`.
This is the terminating hypergeometric expansion from DLMF 18.5.7. -/
noncomputable def jacobiShifted (k : ℕ) (α β x : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (k + 1),
    (-1 : ℝ) ^ m * (k.choose m : ℝ) *
      (rising ((k : ℝ) + α + β + 1) m / rising (α + 1) m) * x ^ m

/-- A [degree](hyp:k), [shape parameter](hyp:α), and [evaluation point](hyp:x) determine [the one-parameter shifted Jacobi perturbation](goal), [given by the normalized shifted Jacobi polynomial with second shape parameter zero](step:1).

The shifted Jacobi perturbation with the second parameter equal to zero. -/
noncomputable def h (k : ℕ) (α x : ℝ) : ℝ :=
  jacobiShifted k α 0 x

/-- A [positive real starting value](hyp:a) and [natural index](hyp:n), together with [its positivity](hyp:ha), ensure that [the associated rising factorial is positive](goal).

Every rising-factorial denominator used for a positive Jacobi parameter is positive. -/
theorem rising_pos (a : ℝ) (n : ℕ) (ha : 0 < a) : 0 < rising a n := by
  exact ascPochhammer_pos n a ha

/-- Any [degree](hyp:k) and [two shape parameters](hyp:α,β) give [a normalized shifted Jacobi polynomial equal to one at the left endpoint](goal).

The normalized shifted Jacobi polynomial has value one at the left endpoint. -/
theorem jacobiShifted_zero (k : ℕ) (α β : ℝ) : jacobiShifted k α β 0 = 1 := by
  unfold jacobiShifted
  calc
    _ = (-1 : ℝ) ^ 0 * (k.choose 0 : ℝ) *
        (rising ((k : ℝ) + α + β + 1) 0 / rising (α + 1) 0) * (0 : ℝ) ^ 0 := by
      apply Finset.sum_eq_single
      · intro b hb hne
        simp [hne]
      · simp
    _ = 1 := by simp [rising]

/-- A [degree](hyp:k), [coefficient index](hyp:m), and [two shape parameters](hyp:α,β), with [the first parameter above minus one](hyp:hα) and [the index below the degree](hyp:hm), give [the adjacent-coefficient recurrence for the normalized shifted Jacobi sum](goal).

Consecutive coefficients of the normalized shifted Jacobi sum satisfy
the hypergeometric recurrence.  This is the finite algebraic step behind
the Jacobi differential equation; it includes the top index `m = k-1`. -/
theorem jacobiShifted_coefficient_recurrence (k m : ℕ) (α β : ℝ)
    (hα : -1 < α) (hm : m < k) :
    ((m : ℝ) + 1) * (α + (m : ℝ) + 1) *
        ((-1 : ℝ) ^ (m + 1) * (k.choose (m + 1) : ℝ) *
          (rising ((k : ℝ) + α + β + 1) (m + 1) /
            rising (α + 1) (m + 1))) =
      -((k : ℝ) - (m : ℝ)) * ((k : ℝ) + α + β + (m : ℝ) + 1) *
        ((-1 : ℝ) ^ m * (k.choose m : ℝ) *
          (rising ((k : ℝ) + α + β + 1) m /
            rising (α + 1) m)) := by
  have hden : rising (α + 1) m ≠ 0 :=
    ne_of_gt (rising_pos (α + 1) m (by linarith))
  have hstep : α + (m : ℝ) + 1 ≠ 0 := by
    have hmnonneg : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hchoose :
      (k.choose (m + 1) : ℝ) * ((m : ℝ) + 1) =
        (k.choose m : ℝ) * ((k : ℝ) - (m : ℝ)) := by
    have hc := congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_succ_right_eq k m)
    push_cast at hc
    rw [Nat.cast_sub hm.le] at hc
    exact hc
  simp only [rising, ascPochhammer_succ_eval, pow_succ]
  change _ * _ * (_ * _ *
      (((ascPochhammer ℝ m).eval ((k : ℝ) + α + β + 1) *
          (((k : ℝ) + α + β + 1) + (m : ℝ))) /
        ((ascPochhammer ℝ m).eval (α + 1) * ((α + 1) + (m : ℝ))))) = _
  rw [show (α + 1) + (m : ℝ) = α + (m : ℝ) + 1 by ring]
  change (ascPochhammer ℝ m).eval (α + 1) ≠ 0 at hden
  field_simp [hden, hstep]
  linear_combination -((ascPochhammer ℝ m).eval ((k : ℝ) + α + β + 1)) *
    ((k : ℝ) + α + β + (m : ℝ) + 1) * hchoose

/-- A [degree](hyp:k), [two shape parameters](hyp:α,β), and [evaluation point](hyp:x), with [the first parameter above minus one](hyp:hα), give [the shifted Jacobi differential equation](goal).

The normalized shifted Jacobi polynomial satisfies its second-order
Jacobi differential equation when the normalization denominator is nonzero.
This coefficient identity is the first algebraic input to an endpoint
comparison proof; it follows term by term from the finite hypergeometric sum. -/
theorem jacobiShifted_ode (k : ℕ) (α β x : ℝ) (hα : -1 < α) :
    x * (1 - x) * deriv (deriv (jacobiShifted k α β)) x +
      (α + 1 - (α + β + 2) * x) * deriv (jacobiShifted k α β) x +
      (k : ℝ) * ((k : ℝ) + α + β + 1) * jacobiShifted k α β x = 0 := by
  let c : ℕ → ℝ := fun m =>
    (-1 : ℝ) ^ m * (k.choose m : ℝ) *
      (rising ((k : ℝ) + α + β + 1) m / rising (α + 1) m)
  let p : Polynomial ℝ := ∑ m ∈ Finset.range (k + 1), C (c m) * X ^ m
  have hp (m : ℕ) : p.coeff m = if m ≤ k then c m else 0 := by
    simp [p, Finset.mem_range]
  have hc (m : ℕ) (hm : m < k) :
      ((m : ℝ) + 1) * (α + (m : ℝ) + 1) * c (m + 1) =
        -((k : ℝ) - (m : ℝ)) * ((k : ℝ) + α + β + (m : ℝ) + 1) * c m := by
    exact jacobiShifted_coefficient_recurrence k m α β hα hm
  have hcoeff (m : ℕ) (K : ℝ) :
      (X * (1 - X) * derivative (derivative p) +
        (C (α + 1) - C (α + β + 2) * X) * derivative p + C K * p).coeff m =
        ((m : ℝ) + 1) * (α + (m : ℝ) + 1) * p.coeff (m + 1) +
        (K - (m : ℝ) * ((m : ℝ) + α + β + 1)) * p.coeff m := by
    have hform :
        X * (1 - X) * derivative (derivative p) +
        (C (α + 1) - C (α + β + 2) * X) * derivative p + C K * p =
        X * derivative (derivative p) - X * (X * derivative (derivative p)) +
        C (α + 1) * derivative p - X * (C (α + β + 2) * derivative p) +
        C K * p := by ring
    rw [hform]
    cases m with
    | zero =>
        simp only [coeff_add, coeff_sub, coeff_X_mul_zero, coeff_C_mul,
          coeff_derivative, Nat.cast_zero, zero_add, sub_zero]
        ring
    | succ m =>
        cases m with
        | zero =>
            simp only [coeff_add, coeff_sub, coeff_X_mul_zero, coeff_X_mul,
              coeff_C_mul, coeff_derivative, Nat.cast_succ, Nat.cast_zero]
            ring
        | succ m =>
            simp only [coeff_add, coeff_sub, coeff_X_mul, coeff_C_mul,
              coeff_derivative, Nat.cast_succ]
            ring
  have hpoly :
      X * (1 - X) * derivative (derivative p) +
        (C (α + 1) - C (α + β + 2) * X) * derivative p +
        C ((k : ℝ) * ((k : ℝ) + α + β + 1)) * p = 0 := by
    ext m
    rw [hcoeff, coeff_zero, hp, hp]
    by_cases hm : m < k
    · rw [if_pos hm.le, if_pos (Nat.succ_le_iff.mpr hm)]
      linear_combination hc m hm
    · by_cases heq : m = k
      · subst m
        simp only [if_pos le_rfl, if_neg (Nat.not_succ_le_self k), mul_zero, zero_add]
        ring
      · have hk : k < m := by omega
        simp only [if_neg (by omega : ¬ m + 1 ≤ k), if_neg (by omega : ¬ m ≤ k),
          mul_zero, add_zero]
  have heval (y : ℝ) : p.eval y = jacobiShifted k α β y := by
    simp [p, jacobiShifted, c, eval_finsetSum, eval_mul, eval_pow]
  have hfun : jacobiShifted k α β = fun y => p.eval y :=
    funext fun y => (heval y).symm
  rw [hfun]
  have hderivfun : deriv (fun y => p.eval y) = fun y => (derivative p).eval y :=
    funext fun y => Polynomial.deriv p
  rw [hderivfun]
  simp only [Polynomial.deriv]
  have := congrArg (Polynomial.eval x) hpoly
  simpa [eval_add, eval_mul, eval_sub] using this

/-- A [degree](hyp:k) and [two shape parameters](hyp:α,β), with [the first parameter above minus one](hyp:hα), give [the normalized shifted Jacobi value at the right endpoint](goal).

At the right endpoint, the normalized shifted Jacobi polynomial is the
signed ratio of the two rising factorials.  This is the terminating
Vandermonde identity for its finite hypergeometric sum. -/
theorem jacobiShifted_one (k : ℕ) (α β : ℝ) (hα : -1 < α) :
    jacobiShifted k α β 1 =
      (-1 : ℝ) ^ k * rising (β + 1) k / rising (α + 1) k := by
  have hneg (a : ℝ) (n : ℕ) :
      (descPochhammer ℝ n).eval (-a) = (-1 : ℝ) ^ n * rising a n := by
    induction n with
    | zero => simp [rising]
    | succ n ih =>
        rw [descPochhammer_succ_eval]
        simp only [rising, ascPochhammer_succ_eval] at *
        rw [ih]
        ring
  have hcast (n : ℕ) (x : ℝ) :
      (descPochhammer ℤ n).smeval x = (descPochhammer ℝ n).eval x := by
    rw [descPochhammer_smeval_eq_ascPochhammer,
      ascPochhammer_smeval_eq_eval, descPochhammer_eval_eq_ascPochhammer]
  let A : ℝ := (k : ℝ) + α + β + 1
  let C : ℝ := α + 1
  have hC : 0 < C := by dsimp [C]; linarith
  have hden : rising C k ≠ 0 := ne_of_gt (rising_pos C k hC)
  have hmul (m : ℕ) (hm : m ≤ k) :
      rising C m * rising (C + m) (k - m) = rising C k := by
    have h := congrArg (Polynomial.eval C) (ascPochhammer_mul ℝ m (k - m))
    simp only [eval_mul, eval_comp, eval_add, eval_X, eval_natCast] at h
    have heq : m + (k - m) = k := Nat.add_sub_of_le hm
    simpa only [rising, heq] using h
  have hv :
      (descPochhammer ℝ k).eval (-A + (C + (k : ℝ) - 1)) =
        ∑ m ∈ Finset.range (k + 1), (k.choose m : ℝ) *
          ((descPochhammer ℝ m).eval (-A) *
            (descPochhammer ℝ (k - m)).eval (C + (k : ℝ) - 1)) := by
    have h := Ring.descPochhammer_smeval_add k
      (Commute.all (-A) (C + (k : ℝ) - 1))
    simp_rw [hcast] at h
    simpa only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Nat.succ_eq_add_one] using h
  have hv' :
      (-1 : ℝ) ^ k * rising (β + 1) k =
        ∑ m ∈ Finset.range (k + 1), (k.choose m : ℝ) *
          ((-1 : ℝ) ^ m * rising A m * rising (C + m) (k - m)) := by
    convert hv using 1
    · have heq : -A + (C + (k : ℝ) - 1) = -(β + 1) := by dsimp [A, C]; ring
      rw [heq, hneg]
    · apply Finset.sum_congr rfl
      intro m hm
      have hm' : m ≤ k := by
        have := Finset.mem_range.mp hm
        omega
      rw [hneg]
      have heq : C + (k : ℝ) - 1 - (k - m : ℕ) + 1 = C + m := by
        rw [Nat.cast_sub hm']
        ring
      rw [descPochhammer_eval_eq_ascPochhammer, heq]
      dsimp [rising]
  apply (eq_div_iff hden).2
  unfold jacobiShifted
  simp only [one_pow, mul_one, Finset.sum_mul]
  rw [hv']
  apply Finset.sum_congr rfl
  intro m hm
  have hm' : m ≤ k := by
    have := Finset.mem_range.mp hm
    omega
  rw [← hmul m hm']
  have hmden : rising C m ≠ 0 := ne_of_gt (rising_pos C m hC)
  have hA : (k : ℝ) + α + β + 1 = A := rfl
  have hC' : α + 1 = C := rfl
  rw [hA, hC']
  field_simp [hmden]

/-- A [degree](hyp:k), [two shape parameters](hyp:α,β), and [point](hyp:x), when [the second parameter is no larger than the first](hyp:hβα), [the second parameter exceeds minus one](hyp:hβ), [the first parameter is at least minus one half](hyp:hα), and [the point lies in the unit interval](hyp:hx), give [an absolute-value bound of one for the normalized shifted Jacobi polynomial](goal).

DLMF 18.14.1: a normalized Jacobi polynomial is bounded by one
on `[0,1]` when `α ≥ β > -1` and `α ≥ -1/2`. -/
theorem jacobiShifted_abs_le_one (k : ℕ) (α β x : ℝ)
    (hβα : β ≤ α) (hβ : -1 < β) (hα : -(1 / 2 : ℝ) ≤ α)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : |jacobiShifted k α β x| ≤ 1 := by
  have hα' : -1 < α := by linarith
  have hmono (n : ℕ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
      rising a n ≤ rising b n := by
    induction n with
    | zero => simp [rising]
    | succ n ih =>
        rw [rising, ascPochhammer_succ_eval, rising, ascPochhammer_succ_eval]
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have hp : 0 ≤ rising a n := (rising_pos a n ha).le
        calc
          rising a n * (a + n) ≤ rising b n * (a + n) :=
            mul_le_mul_of_nonneg_right ih (by linarith)
          _ ≤ rising b n * (b + n) :=
            mul_le_mul_of_nonneg_left (by linarith) (rising_pos b n (by linarith)).le
  have hright : |jacobiShifted k α β 1| ≤ 1 := by
    rw [jacobiShifted_one k α β hα', abs_div, abs_mul, abs_pow, abs_neg,
      abs_one, one_pow, one_mul]
    have hpβ := rising_pos (β + 1) k (by linarith)
    have hpα := rising_pos (α + 1) k (by linarith)
    rw [abs_of_pos hpβ, abs_of_pos hpα]
    exact (div_le_iff₀ hpα).2 (by simpa using hmono k (β + 1) (α + 1) (by linarith) (by linarith))
  have hleft : |jacobiShifted k α β 0| ≤ 1 := by
    rw [jacobiShifted_zero]
    norm_num
  by_cases hk : k = 0
  · subst k
    simp [jacobiShifted, rising]
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  let f : ℝ → ℝ := jacobiShifted k α β
  let L : ℝ := (k : ℝ) * ((k : ℝ) + α + β + 1)
  have hL : 0 < L := by
    dsimp [L]
    have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hkpos
    have : 0 < (k : ℝ) + α + β + 1 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
      linarith
    positivity
  let E : ℝ → ℝ := fun y => f y ^ 2 + y * (1 - y) * (deriv f y) ^ 2 / L
  let p : Polynomial ℝ := ∑ m ∈ Finset.range (k + 1),
    C ((-1 : ℝ) ^ m * (k.choose m : ℝ) *
      (rising ((k : ℝ) + α + β + 1) m / rising (α + 1) m)) * X ^ m
  have hp : f = fun y => p.eval y := by
    funext y
    simp [f, p, jacobiShifted, eval_finsetSum, eval_mul, eval_pow]
  have hf (y : ℝ) : DifferentiableAt ℝ f y := by
    rw [hp]
    exact p.differentiableAt
  have hdp : deriv f = fun y => p.derivative.eval y := by
    funext y
    rw [hp]
    exact Polynomial.deriv p
  have hdf (y : ℝ) : DifferentiableAt ℝ (deriv f) y := by
    rw [hdp]
    exact p.derivative.differentiableAt
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun y => (hf y).continuousAt
  have hdfc : Continuous (deriv f) :=
    continuous_iff_continuousAt.mpr fun y => (hdf y).continuousAt
  have hE : ContinuousOn E (Set.Icc (0 : ℝ) 1) := by
    apply Continuous.continuousOn
    dsimp [E]
    exact (hfc.pow 2).add
      (((continuous_id.mul (continuous_const.sub continuous_id)).mul
        (hdfc.pow 2)).div_const L)
  have hd (y : ℝ) (hy : y ∈ Set.Ioo (0 : ℝ) 1) : DifferentiableAt ℝ E y := by
    dsimp [E]
    fun_prop
  have hder (y : ℝ) (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
      deriv E y = (-(2 * α + 1) + 2 * (α + β + 1) * y) * ((deriv f y) ^ 2 / L) := by
    have ho := jacobiShifted_ode k α β y hα'
    change y * (1 - y) * deriv (deriv f) y +
      (α + 1 - (α + β + 2) * y) * deriv f y + L * f y = 0 at ho
    have hcalc : deriv E y = 2 * f y * deriv f y +
        ((1 - 2 * y) * (deriv f y) ^ 2 +
          2 * y * (1 - y) * deriv f y * deriv (deriv f) y) / L := by
      have hpow : deriv (fun z => f z ^ 2) y = 2 * f y * deriv f y := by
        rw [show (fun z => f z ^ 2) = f ^ 2 from rfl, deriv_pow (hf y) 2]
        ring
      have hdpow : deriv (fun z => (deriv f z) ^ 2) y =
          2 * deriv f y * deriv (deriv f) y := by
        rw [show (fun z => (deriv f z) ^ 2) = (deriv f) ^ 2 from rfl,
          deriv_pow (hdf y) 2]
        ring
      have hlin : deriv (fun z : ℝ => z * (1 - z)) y = 1 - 2 * y := by
        rw [show (fun z : ℝ => z * (1 - z)) =
          (fun z : ℝ => z) * (fun z : ℝ => 1 - z) from rfl,
          deriv_mul (by fun_prop) (by fun_prop)]
        convert_to (1 : ℝ) * (1 - y) + y * (0 - 1) = 1 - 2 * y
        · rw [deriv_id'', deriv_const_sub, deriv_id'']
          norm_num
        · ring
      have hprod : deriv (fun z => z * (1 - z) * (deriv f z) ^ 2) y =
          (1 - 2 * y) * (deriv f y) ^ 2 +
            y * (1 - y) * (2 * deriv f y * deriv (deriv f) y) := by
        rw [show (fun z => z * (1 - z) * (deriv f z) ^ 2) =
          (fun z : ℝ => z * (1 - z)) * (fun z => (deriv f z) ^ 2) from rfl,
          deriv_mul (by fun_prop) (by fun_prop)]
        rw [hlin, hdpow]
      change deriv ((fun z => f z ^ 2) +
        (fun z => z * (1 - z) * (deriv f z) ^ 2 / L)) y = _
      rw [deriv_add (by fun_prop) (by fun_prop)]
      rw [hpow, deriv_div_const, hprod]
      ring
    rw [hcalc]
    apply (div_left_inj' hL.ne').mp
    field_simp
    linear_combination 2 * deriv f y * ho
  have hbound := affine_deriv_energy_le_max E (2 * α + 1) (2 * (α + β + 1)) x
    (by linarith) hE hd (by
      intro y hy
      refine ⟨(deriv f y) ^ 2 / L, div_nonneg (sq_nonneg _) hL.le, ?_⟩
      exact hder y hy) hx
  have hEx : (f x) ^ 2 ≤ E x := by
    dsimp [E]
    have : 0 ≤ x * (1 - x) := mul_nonneg hx.1 (by linarith [hx.2])
    have : 0 ≤ x * (1 - x) * (deriv f x) ^ 2 / L :=
      div_nonneg (mul_nonneg this (sq_nonneg _)) hL.le
    linarith
  have hE0 : E 0 = 1 := by simp [E, f, jacobiShifted_zero]
  have hE1 : E 1 ≤ 1 := by
    simp only [E, sub_self, mul_zero, zero_mul, zero_div, add_zero]
    have := (sq_le_sq₀ (abs_nonneg (f 1)) (by norm_num : (0 : ℝ) ≤ 1)).mpr hright
    simpa [f] using this
  rw [hE0] at hbound
  have hfx : f x ^ 2 ≤ 1 := le_trans hEx (le_trans hbound (max_le (le_refl 1) hE1))
  have : |f x| ≤ 1 := by nlinarith [sq_nonneg (f x), sq_abs (f x)]
  exact this

/-- A [degree](hyp:k), [positive shape parameter](hyp:α), and [point in the unit interval](hyp:x,hx), with [parameter positivity](hyp:hα) and [positive degree](hyp:_hk), give [an absolute-value bound of one for the shifted Jacobi perturbation](goal).

For positive `α`, the shifted Jacobi perturbation is bounded in absolute
value by one throughout `[0,1]`. -/
theorem abs_h_le_one (k : ℕ) (α x : ℝ) (hα : 0 < α) (_hk : 1 ≤ k)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : |h k α x| ≤ 1 := by
  exact jacobiShifted_abs_le_one k α 0 x hα.le (by norm_num) (by linarith) hx

end Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi

module
public import Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi.Basic
public import Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi.Calculus

/-!
# Shifted Jacobi Rodrigues formula and power-bump endpoints

The kernel `x^(α+k) (1-x)^k` has enough zeros at both endpoints to
support `k` integrations by parts.  The interior Rodrigues identity is the
shift of DLMF 18.5.5 and Table 18.5.1, with normalization from 18.5.7.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi

open Filter
open scoped Topology

/-- A [degree](hyp:k), [shape parameter](hyp:α), and [evaluation point](hyp:x) determine [the weighted Rodrigues kernel](goal), [given by the product of a left power and a right power bump](step:1).

The weighted power bump whose `k`th derivative represents a shifted
Jacobi polynomial on the positive half-line. -/
noncomputable def rodKernel (k : ℕ) (α x : ℝ) : ℝ :=
  x ^ (α + (k : ℝ)) * (1 - x) ^ k

/-- A [degree](hyp:k), [derivative order](hyp:i), [shape parameter](hyp:α), and [positive evaluation point](hyp:x), with [point positivity](hyp:hx), give [the finite derivative expansion of the Rodrigues kernel](goal).

On positive arguments, the `i`th derivative of the Rodrigues kernel is
the finite binomial expansion with descending factorial coefficients.  This
reduces endpoint limits and Rodrigues normalization to finite algebra. -/
theorem rodKernel_deriv_expansion (k i : ℕ) (α x : ℝ) (hx : 0 < x) :
    (deriv^[i] (rodKernel k α)) x =
      ∑ m ∈ Finset.range (k + 1),
        (-1 : ℝ) ^ m * (k.choose m : ℝ) *
          (descPochhammer ℝ i).eval (α + (k : ℝ) + (m : ℝ)) *
            x ^ (α + (k : ℝ) + (m : ℝ) - (i : ℝ)) := by
  let c (m : ℕ) : ℝ := (-1 : ℝ) ^ m * (k.choose m : ℝ)
  let p (m : ℕ) : ℝ := α + (k : ℝ) + (m : ℝ)
  have hbin (y : ℝ) : (1 - y) ^ k =
      ∑ m ∈ Finset.range (k + 1), c m * y ^ m := by
    have hh := add_pow (-y) (1 : ℝ) k
    simp only [one_pow, mul_one] at hh
    convert hh using 1
    · ring
    · apply Finset.sum_congr rfl
      intro m hm
      dsimp [c]
      rw [neg_pow y]
      ring
  have hfun : Set.EqOn (rodKernel k α)
      (fun y : ℝ => ∑ m ∈ Finset.range (k + 1), c m * y ^ p m)
      (Set.Ioi 0) := by
    intro y hy
    have hy' : 0 < y := hy
    rw [rodKernel, hbin, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [p]
    have hr : y ^ (α + (k : ℝ) + (m : ℝ)) =
        y ^ (α + (k : ℝ)) * y ^ m := by
      rw [show α + (k : ℝ) + (m : ℝ) = (α + (k : ℝ)) + (m : ℝ) by ring,
        Real.rpow_add hy', Real.rpow_natCast]
    rw [hr]
    ring
  have hder := (hfun.iteratedDeriv_of_isOpen isOpen_Ioi i) hx
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate] at hder
  rw [hder, ← iteratedDeriv_eq_iterate]
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [iteratedDeriv_eq_iterate]
    simp only [p, c]
    rw [← iteratedDeriv_eq_iterate, iteratedDeriv_const_mul_field,
      iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]
    ring
  · intro m hm
    exact contDiffAt_const.mul (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hx))

/-- A [degree](hyp:k), [positive shape parameter](hyp:α), and [positive evaluation point](hyp:x), with [parameter positivity](hyp:hα) and [point positivity](hyp:hx), give [the normalized shifted Jacobi expansion after extracting the power weight](goal).

The order-`k` binomial derivative expansion equals the normalized
shifted Jacobi sum after factoring out `x^α`. -/
theorem rodKernel_expansion_eq_h (k : ℕ) (α x : ℝ) (hα : 0 < α)
    (hx : 0 < x) :
    (∑ m ∈ Finset.range (k + 1),
        (-1 : ℝ) ^ m * (k.choose m : ℝ) *
          (descPochhammer ℝ k).eval (α + (k : ℝ) + (m : ℝ)) *
            x ^ (α + (k : ℝ) + (m : ℝ) - (k : ℝ))) =
      rising (α + 1) k * (x ^ α * h k α x) := by
  have hmul (n m : ℕ) :
      rising (α + 1) n * rising (α + 1 + (n : ℝ)) m =
        rising (α + 1) (n + m) := by
    have hh := congrArg (Polynomial.eval (α + 1)) (ascPochhammer_mul ℝ n m)
    simpa only [rising, Polynomial.eval_mul, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_natCast] using hh
  have hcoef (m : ℕ) :
      (descPochhammer ℝ k).eval (α + (k : ℝ) + (m : ℝ)) =
        rising (α + 1) k *
          (rising ((k : ℝ) + α + 1) m / rising (α + 1) m) := by
    have hmpos : rising (α + 1) m ≠ 0 :=
      ne_of_gt (rising_pos (α + 1) m (by linarith))
    have hleft := hmul m k
    have hright := hmul k m
    have heq : rising (α + 1 + (m : ℝ)) k * rising (α + 1) m =
        rising (α + 1) k * rising ((k : ℝ) + α + 1) m := by
      calc
        _ = rising (α + 1) (m + k) := by rw [← hleft]; ring
        _ = rising (α + 1) (k + m) := by rw [Nat.add_comm]
        _ = _ := by rw [← hright]; congr 1; ring
    rw [descPochhammer_eval_eq_ascPochhammer]
    change rising (α + (k : ℝ) + (m : ℝ) - (k : ℝ) + 1) k = _
    have hb : α + (k : ℝ) + (m : ℝ) - (k : ℝ) + 1 = α + 1 + (m : ℝ) := by ring
    rw [hb]
    rw [← mul_div_assoc]
    apply (eq_div_iff hmpos).2
    exact heq
  unfold h jacobiShifted
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [hcoef m]
  have hpow : x ^ (α + (k : ℝ) + (m : ℝ) - (k : ℝ)) = x ^ α * x ^ m := by
    convert Real.rpow_add hx α (m : ℝ) using 1
    · ring
    · simp
  rw [hpow]
  ring

/-- A [degree](hyp:k), [derivative order](hyp:i), and [shape parameter](hyp:α), when [the derivative order is below the degree](hyp:hik) and [the parameter is positive](hyp:hα), give [a zero Rodrigues-kernel derivative at the right endpoint](goal).

Every derivative of order less than `k` of the Jacobi Rodrigues kernel
vanishes at the right endpoint. -/
theorem rodKernel_deriv_one (k i : ℕ) (α : ℝ) (hik : i < k)
    (hα : 0 < α) : (deriv^[i] (rodKernel k α)) 1 = 0 := by
  change (deriv^[i] (fun x : ℝ => x ^ (α + (k : ℝ)) * (1 - x) ^ k)) 1 = 0
  apply iter_deriv_mul_one_sub_pow_at_one
  · exact Real.contDiffAt_rpow_const_of_ne (by norm_num)
  · exact hik

/-- A [degree](hyp:k), [derivative order](hyp:i), and [shape parameter](hyp:α), when [the derivative order is below the degree](hyp:hik) and [the parameter is positive](hyp:hα), give [convergence of the Rodrigues-kernel derivative to zero from the right](goal).

Every derivative of order less than `k` of the Jacobi Rodrigues kernel
tends to zero from the right at the singular left endpoint. -/
theorem rodKernel_deriv_tendsto_zero (k i : ℕ) (α : ℝ)
    (hik : i < k) (hα : 0 < α) :
    Filter.Tendsto (fun x : ℝ => (deriv^[i] (rodKernel k α)) x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hterm (m : ℕ) :
      Tendsto (fun x : ℝ =>
        (-1 : ℝ) ^ m * (k.choose m : ℝ) *
          (descPochhammer ℝ i).eval (α + (k : ℝ) + (m : ℝ)) *
            x ^ (α + (k : ℝ) + (m : ℝ) - (i : ℝ)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hi : (i : ℝ) < (k : ℝ) := by exact_mod_cast hik
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have hp : 0 < α + (k : ℝ) + (m : ℝ) - (i : ℝ) := by linarith
    have hid : Tendsto (fun x : ℝ => x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      (tendsto_id : Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0)).mono_left inf_le_left
    have hpow := hid.rpow_const (Or.inr hp.le)
    simpa [Real.zero_rpow (ne_of_gt hp)] using
      hpow.const_mul ((-1 : ℝ) ^ m * (k.choose m : ℝ) *
        (descPochhammer ℝ i).eval (α + (k : ℝ) + (m : ℝ)))
  have hsum : Tendsto (fun x : ℝ =>
      ∑ m ∈ Finset.range (k + 1),
        (-1 : ℝ) ^ m * (k.choose m : ℝ) *
          (descPochhammer ℝ i).eval (α + (k : ℝ) + (m : ℝ)) *
            x ^ (α + (k : ℝ) + (m : ℝ) - (i : ℝ)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using (tendsto_finsetSum (Finset.range (k + 1))
      (fun m _ => hterm m))
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (rodKernel_deriv_expansion k i α x hx).symm

/-- A [degree](hyp:k), [positive shape parameter](hyp:α), and [positive evaluation point](hyp:x), with [parameter positivity](hyp:hα) and [point positivity](hyp:hx), give [the normalized shifted Rodrigues formula](goal).

The shifted Rodrigues formula on positive arguments, with the exact
rising-factorial normalization of `h`. -/
theorem h_rodrigues (k : ℕ) (α x : ℝ) (hα : 0 < α) (hx : 0 < x) :
    x ^ α * h k α x =
      (deriv^[k] (rodKernel k α)) x / rising (α + 1) k := by
  rw [rodKernel_deriv_expansion k k α x hx,
    rodKernel_expansion_eq_h k α x hα hx]
  exact (eq_div_iff (ne_of_gt (rising_pos (α + 1) k (by linarith)))).2
    (by ring)

end Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi

module
public import Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi.Rodrigues

/-!
# Reciprocal-weight boundary terms for the shifted Rodrigues kernel

The reciprocal weight in the zeroth moment is singular at zero.  Every
individual boundary product still tends to zero because the kernel carries
the additional positive power `x^α`.
-/

public section

namespace Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi

open Filter

/-- A [degree](hyp:k), [derivative index](hyp:i), and [positive shape parameter](hyp:α), with [parameter positivity](hyp:hα) and [the index below the degree](hyp:hik), give [vanishing at zero of the reciprocal-weight boundary product: the i-th derivative of 1/x times the (k−1−i)-th derivative of the weighted Rodrigues kernel tends to zero as x decreases to zero](goal).

For `i < k`, the product of the `i`th derivative of `x⁻¹` and the
`(k-1-i)`th derivative of the Rodrigues kernel tends to zero as `x ↓ 0`. -/
theorem inv_mul_rodKernel_deriv_tendsto_zero (k i : ℕ) (α : ℝ)
    (hα : 0 < α) (hik : i < k) :
    Tendsto
      (fun x : ℝ => (deriv^[i] (fun y : ℝ => y⁻¹)) x *
        (deriv^[k - 1 - i] (rodKernel k α)) x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hn : k - 1 - i + i + 1 = k := by omega
  have hid : Tendsto (fun x : ℝ => x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    (tendsto_id : Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0)).mono_left inf_le_left
  have hterm (m : ℕ) :
      Tendsto (fun x : ℝ =>
        ((-1 : ℝ) ^ i * (i.factorial : ℝ) *
          ((-1 : ℝ) ^ m * (k.choose m : ℝ) *
            (descPochhammer ℝ (k - 1 - i)).eval (α + (k : ℝ) + (m : ℝ)))) *
          x ^ (α + (m : ℝ)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hp : 0 < α + (m : ℝ) := by positivity
    simpa [Real.zero_rpow (ne_of_gt hp)] using
      (hid.rpow_const (Or.inr hp.le)).const_mul
        ((-1 : ℝ) ^ i * (i.factorial : ℝ) *
          ((-1 : ℝ) ^ m * (k.choose m : ℝ) *
            (descPochhammer ℝ (k - 1 - i)).eval (α + (k : ℝ) + (m : ℝ))))
  have hsum :
      Tendsto (fun x : ℝ =>
        ∑ m ∈ Finset.range (k + 1),
          ((-1 : ℝ) ^ i * (i.factorial : ℝ) *
            ((-1 : ℝ) ^ m * (k.choose m : ℝ) *
              (descPochhammer ℝ (k - 1 - i)).eval (α + (k : ℝ) + (m : ℝ)))) *
            x ^ (α + (m : ℝ)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using (tendsto_finsetSum (Finset.range (k + 1))
      (fun m _ => hterm m))
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxpos : 0 < x := hx
  rw [iter_deriv_inv, rodKernel_deriv_expansion k (k - 1 - i) α x hxpos,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have he : ((-1 - (i : ℤ) : ℤ) : ℝ) +
      (α + (k : ℝ) + (m : ℝ) - (↑(k - 1 - i) : ℝ)) =
      α + (m : ℝ) := by
    have hn' : (↑(k - 1 - i) : ℝ) + (i : ℝ) + 1 = (k : ℝ) := by
      exact_mod_cast hn
    push_cast
    linarith
  have hpow : x ^ ((-1 - (i : ℤ) : ℤ) : ℝ) *
      x ^ (α + (k : ℝ) + (m : ℝ) - (↑(k - 1 - i) : ℝ)) =
      x ^ (α + (m : ℝ)) := by
    rw [← Real.rpow_add hxpos, he]
  rw [Real.rpow_intCast] at hpow
  rw [← hpow]
  ring

end Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi

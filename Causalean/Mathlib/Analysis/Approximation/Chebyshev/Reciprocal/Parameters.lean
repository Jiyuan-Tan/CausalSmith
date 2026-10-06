module
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

/-!
# Parameters for reciprocal approximation on a positive interval

This module records the interval shape and geometric decay parameters in the
exact best uniform approximation error for the reciprocal function.  It also
reduces the parameters on `[1,K²]` to elementary rational expressions.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.Reciprocal

/-- The [lower endpoint](hyp:a) and [upper endpoint](hyp:b) determine [the interval shape
parameter](goal), given by [their sum divided by their difference](step:1). -/
noncomputable def intervalShape (a b : ℝ) : ℝ := (a + b) / (b - a)

/-- The [lower endpoint](hyp:a) and [upper endpoint](hyp:b) determine [the geometric decay
parameter](goal), given by [the interval shape parameter v minus the square root of v² −
1](step:1). -/
noncomputable def intervalDecay (a b : ℝ) : ℝ :=
  intervalShape a b - Real.sqrt ((intervalShape a b) ^ 2 - 1)

/-- The [interval endpoints](hyp:a,b) and [degree bound m](hyp:m) determine [the reciprocal
approximation error](goal), given by [twice the m-th power of the decay parameter, divided by the
interval length times (v² − 1), where v is the interval shape parameter](step:1). -/
noncomputable def reciprocalError (a b : ℝ) (m : ℕ) : ℝ :=
  2 * intervalDecay a b ^ m /
    ((b - a) * ((intervalShape a b) ^ 2 - 1))

/-- A [positive lower endpoint](hyp:a,ha) and [strictly larger upper
endpoint](hyp:b,hab) imply [that the interval shape exceeds one](goal). -/
theorem intervalShape_gt_one {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    1 < intervalShape a b := by
  unfold intervalShape
  have hba : 0 < b - a := sub_pos.mpr hab
  apply (lt_div_iff₀ hba).2
  nlinarith

/-- A [positive lower endpoint](hyp:a,ha) and [strictly larger upper
endpoint](hyp:b,hab) imply [that the decay parameter lies strictly between
zero and one](goal). -/
theorem intervalDecay_mem_Ioo {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    intervalDecay a b ∈ Set.Ioo (0 : ℝ) 1 := by
  let v := intervalShape a b
  let s := Real.sqrt (v ^ 2 - 1)
  have hv : 1 < v := intervalShape_gt_one ha hab
  have hsarg : 0 ≤ v ^ 2 - 1 := by nlinarith
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = v ^ 2 - 1 := Real.sq_sqrt hsarg
  have hsv : s < v := by
    by_contra h
    have hvs : v ≤ s := le_of_not_gt h
    nlinarith [sq_nonneg (s - v)]
  have hρ : 0 < v - s := sub_pos.mpr hsv
  have hsum : 1 < v + s := by linarith
  have hprod : (v - s) * (v + s) = 1 := by nlinarith
  have hρlt : v - s < 1 := by
    nlinarith [mul_pos hρ (sub_pos.mpr hsum)]
  exact ⟨by simpa [intervalDecay, v, s] using hρ,
    by simpa [intervalDecay, v, s] using hρlt⟩

/-- A [positive lower endpoint](hyp:a,ha) and [strictly larger upper
endpoint](hyp:b,hab) imply [that the decay parameter plus its reciprocal
equals twice the interval shape](goal). -/
theorem intervalDecay_add_inv {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    intervalDecay a b + (intervalDecay a b)⁻¹ = 2 * intervalShape a b := by
  let v := intervalShape a b
  let s := Real.sqrt (v ^ 2 - 1)
  have hv : 1 < v := intervalShape_gt_one ha hab
  have hsarg : 0 ≤ v ^ 2 - 1 := by nlinarith
  have hs2 : s ^ 2 = v ^ 2 - 1 := Real.sq_sqrt hsarg
  have hρ : 0 < intervalDecay a b := (intervalDecay_mem_Ioo ha hab).1
  have hprod : (v - s) * (v + s) = 1 := by nlinarith
  have hinv : (intervalDecay a b)⁻¹ = v + s := by
    have hne : v - s ≠ 0 := by
      change 0 < v - s at hρ
      exact ne_of_gt hρ
    change (v - s)⁻¹ = v + s
    field_simp
    nlinarith [hs2]
  rw [hinv]
  change (v - s) + (v + s) = 2 * v
  ring

/-- A [positive lower endpoint](hyp:a,ha), [strictly larger upper
endpoint](hyp:b,hab), and [finite degree](hyp:m) imply [that the claimed
reciprocal error is positive](goal). -/
theorem reciprocalError_pos {a b : ℝ} (ha : 0 < a) (hab : a < b) (m : ℕ) :
    0 < reciprocalError a b m := by
  unfold reciprocalError
  have hv : 1 < intervalShape a b := intervalShape_gt_one ha hab
  have hρ : 0 < intervalDecay a b := (intervalDecay_mem_Ioo ha hab).1
  have hsq : 0 < (intervalShape a b) ^ 2 - 1 := by nlinarith
  exact div_pos (by positivity) (mul_pos (sub_pos.mpr hab) hsq)

/-- A [natural number K at least two](hyp:K,hK) implies [that the decay parameter of the interval
from one to K² equals (K − 1) / (K + 1)](goal). -/
theorem intervalDecay_one_sq (K : ℕ) (hK : 2 ≤ K) :
    intervalDecay 1 ((K : ℝ) ^ 2) = ((K : ℝ) - 1) / ((K : ℝ) + 1) := by
  let x : ℝ := K
  have hx : 2 ≤ x := by
    change (2 : ℝ) ≤ (K : ℝ)
    exact_mod_cast hK
  have hdpos : 0 < x ^ 2 - 1 := by nlinarith
  have hd : x ^ 2 - 1 ≠ 0 := ne_of_gt hdpos
  have hxplus : x + 1 ≠ 0 := by positivity
  have hv : intervalShape 1 (x ^ 2) = (1 + x ^ 2) / (x ^ 2 - 1) := rfl
  have harg : 0 ≤ (intervalShape 1 (x ^ 2)) ^ 2 - 1 := by
    have hshape : 1 < intervalShape 1 (x ^ 2) :=
      intervalShape_gt_one (by norm_num) (by nlinarith)
    nlinarith
  have hroot : Real.sqrt ((intervalShape 1 (x ^ 2)) ^ 2 - 1) =
      2 * x / (x ^ 2 - 1) := by
    apply (Real.sqrt_eq_iff_eq_sq harg (by positivity)).2
    rw [hv]
    field_simp
    ring
  change intervalShape 1 (x ^ 2) -
    Real.sqrt ((intervalShape 1 (x ^ 2)) ^ 2 - 1) = (x - 1) / (x + 1)
  rw [hroot, hv]
  field_simp
  ring

/-- A [natural number K at least two](hyp:K,hK) implies [that the degree-K reciprocal approximation
error on the interval from one to K² equals (K² − 1) / (2 K²) times the K-th power of (K − 1) / (K
+ 1)](goal). -/
theorem reciprocalError_one_sq (K : ℕ) (hK : 2 ≤ K) :
    reciprocalError 1 ((K : ℝ) ^ 2) K =
      (((K : ℝ) ^ 2 - 1) / (2 * (K : ℝ) ^ 2)) *
        (((K : ℝ) - 1) / ((K : ℝ) + 1)) ^ K := by
  let x : ℝ := K
  have hx : 2 ≤ x := by
    change (2 : ℝ) ≤ (K : ℝ)
    exact_mod_cast hK
  have hdpos : 0 < x ^ 2 - 1 := by nlinarith
  have hd : x ^ 2 - 1 ≠ 0 := ne_of_gt hdpos
  have hxne : x ≠ 0 := by positivity
  have hv : intervalShape 1 (x ^ 2) = (1 + x ^ 2) / (x ^ 2 - 1) := rfl
  rw [reciprocalError, intervalDecay_one_sq K hK]
  change 2 * ((x - 1) / (x + 1)) ^ K /
      ((x ^ 2 - 1) * ((intervalShape 1 (x ^ 2)) ^ 2 - 1)) =
    ((x ^ 2 - 1) / (2 * x ^ 2)) * ((x - 1) / (x + 1)) ^ K
  rw [hv]
  field_simp
  have hden : (1 + x ^ 2) ^ 2 - (x ^ 2 - 1) ^ 2 = 4 * x ^ 2 := by ring
  rw [hden]
  field_simp [hxne]
  ring

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.Reciprocal

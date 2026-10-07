module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Basic
public import Causalean.Tactic.Attr
public import Causalean.Tactic.CondexpLinearity
public import Causalean.Tactic.IndicatorSimps
public import Causalean.Tactic.IntegralLinearity
public import Causalean.Tactic.SumAlgebraSimps
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Exterior Lagrange mass on Chebyshev–Lobatto grids

For the Chebyshev–Lobatto nodes cos(iπ/N), i = 0, …, N, the sum of the absolute values of the
Lagrange cardinal polynomials at a point x < −1 outside the grid equals |T_N(x)|, the absolute
value of the degree-N Chebyshev polynomial. By affine invariance of the cardinal polynomials, the
grid moved to [a, 1] with 0 < a < 1 has cardinal mass |T_N(−(1 + a)/(1 − a))| at zero, and for
a = K⁻² and N = K − 1 with K ≥ 2 this value is at most cosh 2. These identities bound how far
polynomial extrapolation from [a, 1] to 0 can amplify sampled values.

## Main results

* `standard_exterior_basis_sign` — for x < −1 the i-th cardinal value has sign (−1)^(N + i).
* `standard_exterior_lagrange_abs_sum` — Σ_i |ℓ_i(x)| = |T_N(x)| for x < −1.
* `lagrange_basis_eval_affine_local` — cardinal polynomials are unchanged when nodes and the
  evaluation point undergo the same affine map with nonzero slope.
* `shifted_chebyshev_lagrange_abs_sum` — the cardinal mass at zero of the grid moved to [a, 1].
* `calibrated_chebyshev_exterior_le_cosh_two` — |T_(K−1)(−(1 + K⁻²)/(1 − K⁻²))| ≤ cosh 2.
-/

public section

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev

open Polynomial

/-- For a [standard Lobatto grid of degree](hyp:N), an [evaluation point left of
`-1`](hyp:x,hx), and a [grid index](hyp:i), the absolute cardinal-basis value is
the value with its common alternating sign exposed. The result is [the alternating-sign identity for an exterior Lobatto cardinal value](goal). -/
lemma standard_exterior_basis_sign (N : ℕ) (x : ℝ) (hx : x < -1)
    (i : Fin (N + 1)) :
    |(Lagrange.basis Finset.univ
        (fun j : Fin (N + 1) => Polynomial.Chebyshev.node N j) i).eval x| =
      (-1 : ℝ) ^ N * ((-1 : ℝ) ^ (i : ℕ) *
        (Lagrange.basis Finset.univ
          (fun j : Fin (N + 1) => Polynomial.Chebyshev.node N j) i).eval x) := by
  let s := (Finset.univ : Finset (Fin (N + 1))).erase i
  let v : Fin (N + 1) → ℝ := fun j => Polynomial.Chebyshev.node N j
  let D : ℝ := ∏ j ∈ s, (v i - v j)
  let A : ℝ := ∏ j ∈ s, (x - v j)
  have hi : (i : ℕ) ≤ N := Nat.lt_succ_iff.mp i.isLt
  have hD : 0 < (-1 : ℝ) ^ (i : ℕ) * D := by
    have hleft : 0 < ∏ j ∈ Finset.Iio i, ((-1 : ℝ) * (v i - v j)) := by
      apply Finset.prod_pos
      intro j hj
      have hji : j < i := Finset.mem_Iio.mp hj
      exact mul_pos_of_neg_of_neg (by norm_num)
        (sub_neg.mpr (Polynomial.Chebyshev.node_lt hi hji))
    rw [Finset.prod_mul_distrib, Finset.prod_const, Fin.card_Iio] at hleft
    have hright : 0 < ∏ j ∈ Finset.Ioi i, (v i - v j) := by
      apply Finset.prod_pos
      intro j hj
      have hij : i < j := Finset.mem_Ioi.mp hj
      exact sub_pos.mpr
        (Polynomial.Chebyshev.node_lt (Nat.lt_succ_iff.mp j.isLt) hij)
    have hunion : s = Finset.Iio i ∪ Finset.Ioi i := by
      ext j
      simp only [s, Finset.mem_erase, Finset.mem_univ, and_true,
        Finset.mem_union, Finset.mem_Iio, Finset.mem_Ioi]
      constructor
      · exact lt_or_gt_of_ne
      · exact fun h => h.elim (fun hji => ne_of_lt hji) (fun hij => ne_of_gt hij)
    have hdisjoint : Disjoint (Finset.Iio i) (Finset.Ioi i) := by
      exact Finset.disjoint_left.mpr (fun j hji hij =>
        (Finset.mem_Iio.mp hji).asymm (Finset.mem_Ioi.mp hij))
    dsimp [D]
    rw [hunion, Finset.prod_union hdisjoint, ← mul_assoc]
    exact mul_pos hleft hright
  have hA : 0 < (-1 : ℝ) ^ N * A := by
    have hpos : 0 < ∏ j ∈ s, -(x - v j) := by
      apply Finset.prod_pos
      intro j hj
      have hvj : -1 ≤ v j := (Polynomial.Chebyshev.node_mem_Icc).1
      linarith
    have hcard : s.card = N := by simp [s]
    rw [Finset.prod_neg, hcard] at hpos
    exact hpos
  have heval :
      (Lagrange.basis Finset.univ v i).eval x = D⁻¹ * A := by
    rw [Lagrange.basis, Polynomial.eval_prod]
    simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_sub, Polynomial.eval_X]
    rw [Finset.prod_mul_distrib, ← Finset.prod_inv_distrib]
  have hsign : 0 < ((-1 : ℝ) ^ N * (-1 : ℝ) ^ (i : ℕ)) *
      (Lagrange.basis Finset.univ v i).eval x := by
    rw [heval]
    have hDi : 0 < ((-1 : ℝ) ^ (i : ℕ) * D)⁻¹ := inv_pos.mpr hD
    have hrewrite : ((-1 : ℝ) ^ (i : ℕ) * D)⁻¹ =
        (-1 : ℝ) ^ (i : ℕ) * D⁻¹ := by
      rw [mul_inv_rev]
      have hpow : ((-1 : ℝ) ^ (i : ℕ))⁻¹ = (-1 : ℝ) ^ (i : ℕ) := by
        rw [← inv_pow]
        norm_num
      rw [hpow]
      ring
    rw [hrewrite] at hDi
    nlinarith
  have habs := abs_of_pos hsign
  rw [abs_mul, abs_mul, abs_neg_one_pow, abs_neg_one_pow, one_mul, one_mul] at habs
  rw [habs, mul_assoc]


/-- For a [standard Lobatto grid of degree](hyp:N) and an [evaluation point left
of `-1`](hyp:x,hx), the sum of absolute cardinal-basis values equals the
absolute value of the corresponding Chebyshev polynomial. The result is [the exterior Lobatto cardinal-mass identity](goal). -/
lemma standard_exterior_lagrange_abs_sum (N : ℕ) (x : ℝ) (hx : x < -1) :
    (∑ i : Fin (N + 1),
      |(Lagrange.basis Finset.univ
          (fun j : Fin (N + 1) => Polynomial.Chebyshev.node N j) i).eval x|) =
      |(Polynomial.Chebyshev.T ℝ (N : ℤ)).eval x| := by
  let v : Fin (N + 1) → ℝ := fun j => Polynomial.Chebyshev.node N j
  have hv : Function.Injective v := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij' | hji'
    · exact ne_of_gt (Polynomial.Chebyshev.node_lt
        (Nat.lt_succ_iff.mp j.isLt) hij') hij
    · exact ne_of_lt (Polynomial.Chebyshev.node_lt
        (Nat.lt_succ_iff.mp i.isLt) hji') hij
  have hdegree : (Polynomial.Chebyshev.T ℝ (N : ℤ)).degree <
      ((Finset.univ : Finset (Fin (N + 1))).card : WithBot ℕ) := by
    rw [Polynomial.Chebyshev.degree_T, Int.natAbs_natCast]
    simp
    exact_mod_cast Nat.lt_succ_self N
  have hinterp := Lagrange.eq_interpolate
    (f := Polynomial.Chebyshev.T ℝ (N : ℤ)) hv.injOn hdegree
  have heval := congrArg (fun p : ℝ[X] => p.eval x) hinterp
  have hsigned :
      (∑ i : Fin (N + 1), (-1 : ℝ) ^ (i : ℕ) *
        (Lagrange.basis Finset.univ v i).eval x) =
          (Polynomial.Chebyshev.T ℝ (N : ℤ)).eval x := by
    rw [heval]
    simp only [Lagrange.interpolate_apply, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C]
    apply Finset.sum_congr rfl
    intro i _
    rw [Polynomial.Chebyshev.eval_T_real_node
      (Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp i.isLt))]
  calc
    (∑ i : Fin (N + 1),
        |(Lagrange.basis Finset.univ v i).eval x|) =
        ∑ i : Fin (N + 1), (-1 : ℝ) ^ N *
          ((-1 : ℝ) ^ (i : ℕ) *
            (Lagrange.basis Finset.univ v i).eval x) := by
      apply Finset.sum_congr rfl
      intro i _
      exact standard_exterior_basis_sign N x hx i
    _ = (-1 : ℝ) ^ N *
        (∑ i : Fin (N + 1), (-1 : ℝ) ^ (i : ℕ) *
          (Lagrange.basis Finset.univ v i).eval x) := by
      rw [Finset.mul_sum]
    _ = (-1 : ℝ) ^ N *
        (Polynomial.Chebyshev.T ℝ (N : ℤ)).eval x := by rw [hsigned]
    _ = |(Polynomial.Chebyshev.T ℝ (N : ℤ)).eval x| := by
      have hnonneg : 0 ≤ (-1 : ℝ) ^ N *
          (Polynomial.Chebyshev.T ℝ (N : ℤ)).eval x := by
        have h := Polynomial.Chebyshev.one_le_negOnePow_mul_eval_T_real
          (N : ℤ) (show x ≤ -1 by linarith)
        simpa using (show (0 : ℝ) ≤ (N : ℤ).negOnePow *
          (Polynomial.Chebyshev.T ℝ (N : ℤ)).eval x by linarith)
      calc
        (-1 : ℝ) ^ N * (Polynomial.Chebyshev.T ℝ (N : ℤ)).eval x =
            |(-1 : ℝ) ^ N *
              (Polynomial.Chebyshev.T ℝ (N : ℤ)).eval x| :=
          (abs_of_nonneg hnonneg).symm
        _ = _ := by rw [abs_mul, abs_neg_one_pow, one_mul]


/-- For [nodes](hyp:v) that are [injective on the interpolation set](hyp:s,hv),
a [selected node in that set](hyp:i,hi), and a [nondegenerate affine change of
scale](hyp:c,r,z,hr), the transformed cardinal-basis evaluation equals the
original evaluation. The result is [invariance of the cardinal-basis evaluation under the affine change](goal). -/
lemma lagrange_basis_eval_affine_local {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {v : ι → ℝ} (hv : Set.InjOn v s) {i : ι} (hi : i ∈ s)
    (c r z : ℝ) (hr : r ≠ 0) :
    (Lagrange.basis s (fun j => c + r * v j) i).eval (c + r * z) =
      (Lagrange.basis s v i).eval z := by
  rw [Lagrange.basis, Lagrange.basis, Polynomial.eval_prod, Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro j hj
  have hjmem : j ∈ s := (Finset.mem_erase.mp hj).2
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  have hvne : v i ≠ v j := by
    intro h
    exact hji (hv hi hjmem h).symm
  simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_X]
  rw [show c + r * z - (c + r * v j) = r * (z - v j) by ring,
    show c + r * v i - (c + r * v j) = r * (v i - v j) by ring]
  field_simp [hr, hvne]


/-- For a [Lobatto degree](hyp:N) and a [left endpoint strictly between zero and
one](hyp:a,ha0,ha1), the cardinal mass of the grid shifted to `[a,1]` and
evaluated at zero equals the stated exterior Chebyshev value. The result is [the shifted-grid cardinal-mass identity at zero](goal). -/
lemma shifted_chebyshev_lagrange_abs_sum (N : ℕ) (a : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) :
    (∑ i : Fin (N + 1),
      |(Lagrange.basis Finset.univ
        (fun j : Fin (N + 1) =>
          (1 + a) / 2 + (1 - a) / 2 * Polynomial.Chebyshev.node N j) i).eval 0|) =
      |(Polynomial.Chebyshev.T ℝ (N : ℤ)).eval (-(1 + a) / (1 - a))| := by
  let v : Fin (N + 1) → ℝ := fun j => Polynomial.Chebyshev.node N j
  let c : ℝ := (1 + a) / 2
  let r : ℝ := (1 - a) / 2
  let z : ℝ := -(1 + a) / (1 - a)
  have hr : r ≠ 0 := by dsimp [r]; positivity
  have hv : Function.Injective v := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij' | hji'
    · exact ne_of_gt (Polynomial.Chebyshev.node_lt
        (Nat.lt_succ_iff.mp j.isLt) hij') hij
    · exact ne_of_lt (Polynomial.Chebyshev.node_lt
        (Nat.lt_succ_iff.mp i.isLt) hji') hij
  have hz : c + r * z = 0 := by
    dsimp [c, r, z]
    field_simp [ne_of_gt (sub_pos.mpr ha1)]
    ring
  have hzlt : z < -1 := by
    dsimp [z]
    rw [div_lt_iff₀ (sub_pos.mpr ha1)]
    linarith
  rw [← standard_exterior_lagrange_abs_sum N z hzlt]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hz]
  exact congrArg abs
    (lagrange_basis_eval_affine_local hv.injOn (Finset.mem_univ i) c r z hr)


/-- For an [integer scale K at least two](hyp:K,hK), [the Chebyshev polynomial of the first kind
of degree K − 1, evaluated at the exterior point −(1 + K⁻²) / (1 − K⁻²), which lies to the left of
−1, has absolute value at most cosh 2](goal). -/
lemma calibrated_chebyshev_exterior_le_cosh_two (K : ℕ) (hK : 2 ≤ K) :
    |(Polynomial.Chebyshev.T ℝ ((K - 1 : ℕ) : ℤ)).eval
      (-(1 + (K : ℝ)⁻¹ ^ 2) / (1 - (K : ℝ)⁻¹ ^ 2))| ≤ Real.cosh 2 := by
  let k : ℝ := K
  let r : ℝ := (k + 1) / (k - 1)
  let t : ℝ := Real.log r
  have hk2 : (2 : ℝ) ≤ k := by
    dsimp [k]
    exact_mod_cast hK
  have hk1 : 1 < k := lt_of_lt_of_le (by norm_num) hk2
  have hrpos : 0 < r := div_pos (by linarith) (by linarith)
  have hrone : 1 ≤ r := by
    dsimp [r]
    rw [le_div_iff₀ (by linarith : 0 < k - 1)]
    linarith
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact Real.log_nonneg hrone
  have ht_upper : (((K - 1 : ℕ) : ℝ)) * t ≤ 2 := by
    have hlog := Real.log_le_sub_one_of_pos hrpos
    have hkreal : ((K - 1 : ℕ) : ℝ) = k - 1 := by
      dsimp [k]
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hkreal]
    calc
      (k - 1) * t ≤ (k - 1) * (r - 1) :=
        mul_le_mul_of_nonneg_left hlog (by linarith)
      _ = 2 := by
        dsimp [r]
        field_simp [ne_of_gt (sub_pos.mpr hk1)]
        ring
  have hz : -(1 + (K : ℝ)⁻¹ ^ 2) / (1 - (K : ℝ)⁻¹ ^ 2) =
      -Real.cosh t := by
    have hk0 : k ≠ 0 := ne_of_gt (lt_trans (by norm_num) hk1)
    have hkm1 : k - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hk1)
    have hkp1 : k + 1 ≠ 0 := by linarith
    have hksq : k ^ 2 - 1 ≠ 0 := by nlinarith
    change -(1 + k⁻¹ ^ 2) / (1 - k⁻¹ ^ 2) = -Real.cosh t
    rw [Real.cosh_log hrpos]
    dsimp [t, r]
    field_simp [hk0, hkm1, hkp1, hksq]
    ring
  rw [hz, Polynomial.Chebyshev.T_eval_neg, Polynomial.Chebyshev.T_real_cosh]
  simp only [abs_mul, abs_unit_intCast, one_mul, Int.cast_natCast]
  rw [abs_of_nonneg (Real.cosh_pos _).le]
  apply (Real.cosh_le_cosh).2
  rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) ht0), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact ht_upper

end Causalean.Mathlib.Analysis.Approximation.Chebyshev

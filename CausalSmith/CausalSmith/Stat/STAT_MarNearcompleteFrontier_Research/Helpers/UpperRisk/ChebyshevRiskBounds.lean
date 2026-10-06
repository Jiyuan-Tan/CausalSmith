module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.ChebyshevBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Chebyshev quotient bounds for the light-cell correction

These leaves isolate the direct interval consequences of the quotient formula
in equation (6) of the upper-risk proof.
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

private lemma qPoly_comp_coeff_one_local (n : ℕ) :
    (((Polynomial.Chebyshev.T ℝ (polyDegree n : ℤ)).comp
      (1 - Polynomial.C (2 / polyThreshold n) * Polynomial.X)).coeff 1) =
      -(2 / polyThreshold n) * (polyDegree n : ℝ) ^ 2 := by
  rw [show (((Polynomial.Chebyshev.T ℝ (polyDegree n : ℤ)).comp
      (1 - Polynomial.C (2 / polyThreshold n) * Polynomial.X)).coeff 1) =
    (((Polynomial.Chebyshev.T ℝ (polyDegree n : ℤ)).comp
      (1 - Polynomial.C (2 / polyThreshold n) * Polynomial.X)).derivative.eval 0) by
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
      norm_num]
  rw [Polynomial.derivative_comp]
  simp [Polynomial.Chebyshev.derivative_T_eval_one]

private lemma qPoly_coeff_zero_local (n : ℕ) : (qPoly n).coeff 0 = 1 := by
  unfold qPoly
  rw [Polynomial.coeff_mul_C, Polynomial.coeff_divX]
  simp only [Polynomial.coeff_sub, Polynomial.coeff_one,
    if_neg (by norm_num : (1 : ℕ) ≠ 0), zero_sub]
  rw [qPoly_comp_coeff_one_local]
  have hB : polyThreshold n ≠ 0 := by
    have he : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
    have he' : 1 < Real.exp (1 : ℝ) + (n : ℝ) := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hl : 0 < ell n := Real.log_pos (by simpa [ell] using he')
    unfold polyThreshold
    positivity
  have hk : (polyDegree n : ℝ) ≠ 0 := by
    exact_mod_cast (show polyDegree n ≠ 0 by unfold polyDegree; omega)
  simp
  field_simp

-- @node: upper_qPoly_eval_zero
/-- The removable value of the Chebyshev quotient at zero is one. Given [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). -/
lemma upper_qPoly_eval_zero (n : ℕ) :
    (qPoly n).eval 0 = 1 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  exact qPoly_coeff_zero_local n

private lemma qPoly_bounds_on_positive {n : ℕ} (hn : 1 ≤ n) {z : ℝ}
    (hz : 0 < z) (hzB : z ≤ polyThreshold n) :
    0 ≤ (qPoly n).eval z ∧
      z * (qPoly n).eval z ≤
        polyThreshold n / (polyDegree n : ℝ) ^ 2 := by
  have hB : 0 < polyThreshold n := lt_of_lt_of_le hz hzB
  have hkNat : 1 ≤ polyDegree n := by
    unfold polyDegree
    exact le_max_left _ _
  have hk : 0 < (polyDegree n : ℝ) := by exact_mod_cast hkNat
  have hzdiv : 0 ≤ z / polyThreshold n := div_nonneg hz.le hB.le
  have hzdiv_le : z / polyThreshold n ≤ 1 := (div_le_one hB).2 hzB
  have hx : |1 - 2 * z / polyThreshold n| ≤ 1 := by
    have hquot : 2 * z / polyThreshold n = 2 * (z / polyThreshold n) := by ring
    rw [hquot, abs_le]
    constructor <;> nlinarith
  have ht := Polynomial.Chebyshev.abs_eval_T_real_le_one
    (polyDegree n : ℤ) hx
  have htlo : -1 ≤ (Polynomial.Chebyshev.T ℝ (polyDegree n : ℤ)).eval
      (1 - 2 * z / polyThreshold n) := (abs_le.mp ht).1
  have htup : (Polynomial.Chebyshev.T ℝ (polyDegree n : ℤ)).eval
      (1 - 2 * z / polyThreshold n) ≤ 1 := (abs_le.mp ht).2
  have hden : 0 <
      2 * (polyDegree n : ℝ) ^ 2 * z / polyThreshold n := by positivity
  rw [qPoly_eval_formula n hn z (ne_of_gt hz)]
  constructor
  · exact div_nonneg (by linarith) hden.le
  · have heq :
        z * ((1 - (Polynomial.Chebyshev.T ℝ (polyDegree n : ℤ)).eval
              (1 - 2 * z / polyThreshold n)) /
            (2 * (polyDegree n : ℝ) ^ 2 * z / polyThreshold n)) =
          (polyThreshold n *
              ((1 - (Polynomial.Chebyshev.T ℝ (polyDegree n : ℤ)).eval
                (1 - 2 * z / polyThreshold n)) / 2)) /
            (polyDegree n : ℝ) ^ 2 := by
        field_simp [ne_of_gt hz, ne_of_gt hB, ne_of_gt hk]
    rw [heq]
    apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hk)).2
    calc
      polyThreshold n *
          ((1 - (Polynomial.Chebyshev.T ℝ (polyDegree n : ℤ)).eval
            (1 - 2 * z / polyThreshold n)) / 2) ≤
          polyThreshold n * 1 := by
        apply mul_le_mul_of_nonneg_left _ hB.le
        linarith
      _ = polyThreshold n := mul_one _

-- @node: upper_qPoly_nonneg_on_positive
/-- The Chebyshev quotient is nonnegative at a positive rate below the
polynomial threshold. Given [the specified input `n`](hyp:n), [the specified input `hn`](hyp:hn), [the specified input `z`](hyp:z), [the specified input `hz`](hyp:hz), [the specified input `hzB`](hyp:hzB), [the stated mathematical conclusion holds](goal). -/
lemma upper_qPoly_nonneg_on_positive {n : ℕ} (hn : 1 ≤ n) {z : ℝ}
    (hz : 0 < z) (hzB : z ≤ polyThreshold n) :
    0 ≤ (qPoly n).eval z :=
  (qPoly_bounds_on_positive hn hz hzB).1

-- @node: upper_z_mul_qPoly_le
/-- On the light-cell range, rate times the Chebyshev quotient is bounded by
the threshold divided by the square of its polynomial degree. Given [the specified input `n`](hyp:n), [the specified input `hn`](hyp:hn), [the specified input `z`](hyp:z), [the specified input `hz`](hyp:hz), [the specified input `hzB`](hyp:hzB), [the stated mathematical conclusion holds](goal). -/
lemma upper_z_mul_qPoly_le {n : ℕ} (hn : 1 ≤ n) {z : ℝ}
    (hz : 0 < z) (hzB : z ≤ polyThreshold n) :
    z * (qPoly n).eval z ≤
      polyThreshold n / (polyDegree n : ℝ) ^ 2 :=
  (qPoly_bounds_on_positive hn hz hzB).2

-- @node: upper_qPoly_le_one_on_positive
/-- The Chebyshev quotient is at most one at a positive rate below the
polynomial threshold. Given [the specified input `n`](hyp:n), [the specified input `hn`](hyp:hn), [the specified input `z`](hyp:z), [the specified input `hz`](hyp:hz), [the specified input `hzB`](hyp:hzB), [the stated mathematical conclusion holds](goal). -/
lemma upper_qPoly_le_one_on_positive {n : ℕ} (hn : 1 ≤ n) {z : ℝ}
    (hz : 0 < z) (hzB : z ≤ polyThreshold n) :
    (qPoly n).eval z ≤ 1 := by
  let k := polyDegree n
  let B := polyThreshold n
  let x₀ : ℝ := 1 - 2 * z / B
  let T : Polynomial ℝ := Polynomial.Chebyshev.T ℝ (k : ℤ)
  have hB : 0 < B := lt_of_lt_of_le hz hzB
  have hkNat : 1 ≤ k := by
    unfold k polyDegree
    exact le_max_left _ _
  have hk : 0 < (k : ℝ) := by exact_mod_cast hkNat
  have hzdiv : 0 ≤ z / B := div_nonneg hz.le hB.le
  have hzdiv_le : z / B ≤ 1 := (div_le_one hB).2 hzB
  have hxabs : |x₀| ≤ 1 := by
    have hquot : 2 * z / B = 2 * (z / B) := by ring
    simp only [x₀, hquot, abs_le]
    constructor <;> nlinarith
  have hxmem : x₀ ∈ Set.Icc (-1 : ℝ) 1 := Set.mem_Icc.mpr (abs_le.mp hxabs)
  have hone : (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
  have hderiv : ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      ‖deriv (fun u : ℝ => T.eval u) y‖ ≤ (k : ℝ) ^ 2 := by
    intro y hy
    rw [Polynomial.deriv, Real.norm_eq_abs]
    have hyabs : |y| ≤ 1 := abs_le.mpr hy
    have hcheb := Polynomial.Chebyshev.abs_iterate_derivative_T_real_le
      (k : ℤ) 1 hyabs
    simpa only [T, Function.iterate_one,
      Polynomial.Chebyshev.derivative_T_eval_one, Int.cast_natCast] using hcheb
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.Icc (-1 : ℝ) 1) (x := x₀) (y := (1 : ℝ))
    (C := (k : ℝ) ^ 2)
    (fun y hy => T.differentiableAt) hderiv (convex_Icc _ _) hxmem hone
  have hTx : 1 - T.eval x₀ ≤ (k : ℝ) ^ 2 * (1 - x₀) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmv
    have hxle : x₀ ≤ 1 := hxmem.2
    calc
      1 - T.eval x₀ ≤ |1 - T.eval x₀| := le_abs_self _
      _ ≤ (k : ℝ) ^ 2 * (1 - x₀) := by
        simpa only [T, Polynomial.Chebyshev.T_eval_one,
          abs_of_nonneg (sub_nonneg.mpr hxle)] using hmv
  have hden : 0 < 2 * (k : ℝ) ^ 2 * z / B := by positivity
  rw [qPoly_eval_formula n hn z (ne_of_gt hz)]
  change (1 - T.eval x₀) / (2 * (k : ℝ) ^ 2 * z / B) ≤ 1
  apply (div_le_one hden).2
  calc
    1 - T.eval x₀ ≤ (k : ℝ) ^ 2 * (1 - x₀) := hTx
    _ = 2 * (k : ℝ) ^ 2 * z / B := by
      dsimp [x₀]
      ring

end CausalSmith.Stat.MarNearcompleteFrontier


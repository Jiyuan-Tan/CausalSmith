/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.Stat.Nonparametric.LocalPoly.DesignMatrixPosDef
public import Causalean.Stat.Nonparametric.LocalPoly.EstimatorRisk.DensityLeverage
public import Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate.PopulationMoment

/-!
# The moment event implies a well-conditioned local-polynomial design

On the event that every normalized empirical kernel moment is within the explicit tolerance of
its expectation, the weighted design matrix `M` of the local-polynomial fit is invertible, its
intercept inverse entry is of order `1/(N h)`, and the leverage product `M₀₀ (M⁻¹)₀₀` is bounded
by a constant (`localPoly_leverage_on_momentEvent`). The proof rewrites `M` in the rescaled basis
as `D_h B D_h`, with `B = N h ·` (empirical moment matrix) and `D_h` the diagonal matrix of
bandwidth powers, and applies the deterministic inverse-perturbation and leverage bounds for
density-weighted designs.

`rawIntercept_eq_wls_intercept` adds that on this event the estimator is the intercept of the
weighted least-squares polynomial fit.
-/

public section

namespace Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate

open MeasureTheory Causalean.Stat.Nonparametric
open scoped BigOperators

/-- For [a kernel `K` and evaluation point `x₀`, as carried by a design](hyp:D), [a positive
sample size `N`](hyp:hN), [a positive bandwidth `h`](hyp:hh) and design points `x_1, …,
x_N`, [the weighted Gram matrix `∑_i K(u_i) u_i^(j+k)` in the rescaled basis, `u_i = (x_i −
x₀)/h`, equals `N h` times the empirical moment matrix](goal). -/
theorem rescaled_designMatrix_eq (D : KernelDesign) (p : ℕ) {N : ℕ} {h : ℝ}
    (hN : 0 < N) (hh : 0 < h) (x : Fin N → ℝ) :
    designMatrix p (fun i => (x i - D.center) / h)
      (fun i => D.kernel ((x i - D.center) / h))
      = ((N : ℝ) * h) • empiricalMoment D p h x := by
  have hNh : (N : ℝ) * h ≠ 0 := mul_ne_zero (by exact_mod_cast hN.ne') hh.ne'
  ext j k
  simp only [designMatrix, empiricalMoment, momentSummand,
    Matrix.smul_apply, smul_eq_mul]
  field_simp

/-- For [a kernel `K` and evaluation point `x₀`, as carried by a design](hyp:D), [a positive
bandwidth `h`](hyp:hh) and design points `x_1, …, x_N`, [the weighted design matrix `∑_i
K(u_i) (x_i − x₀)^(j+k)` equals `D_h B D_h`, where `B` has entries `∑_i K(u_i) u_i^(j+k)`,
`u_i = (x_i − x₀)/h`, and `D_h` is the diagonal matrix of powers `1, h, …, h^p`](goal). -/
theorem unscaled_designMatrix_factor (D : KernelDesign) (p : ℕ) {N : ℕ} {h : ℝ}
    (hh : 0 < h) (x : Fin N → ℝ) :
    designMatrix p (fun i => x i - D.center)
      (fun i => D.kernel ((x i - D.center) / h)) =
    Matrix.diagonal (fun j : Fin (p + 1) => h ^ (j : ℕ)) *
      designMatrix p (fun i => (x i - D.center) / h)
        (fun i => D.kernel ((x i - D.center) / h)) *
      Matrix.diagonal (fun j : Fin (p + 1) => h ^ (j : ℕ)) := by
  ext j k
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, designMatrix]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [div_pow, div_pow]
  field_simp [hh.ne']

/-- **The moment event supplies the deterministic perturbation conditions.** Let [the design
density `f` lie between `f_min > 0` and `f_max` on `[x₀ − r, x₀ + r]`, and the kernel `K` be
measurable, nonnegative, bounded, zero outside `[−1, 1]` and at least `K_min > 0` on `[−Δ,
Δ]`](hyp:D). Take [a positive sample size `N`](hyp:hN), [a positive bandwidth `h`](hyp:hh)
[not exceeding `r`](hyp:hwindow), and [design points `x_1, …, x_N`](hyp:x) for which [every
empirical moment `(N h)⁻¹ ∑_i K(u_i) u_i^(j+k)`, `u_i = (x_i − x₀)/h`, `0 ≤ j, k ≤ p`, is
within the design tolerance `t₀` of its expectation](hyp:hx). Write `B` for the Gram matrix
`∑_i K(u_i) u_i^(j+k)`, `T` for the population matrix `∫ K(u) f(x₀ + h u) u^(j+k) du`, `η =
N h t₀` and `c = c_row/(N h)`. Then [every row of `(N h T)⁻¹` has absolute sum at most `c`,
every entry of `B − N h T` is at most `η` in absolute value, `c (p+1) η ≤ 1/2`, and `2 c²
(p+1) η ≤ c_inv/(N h)`](goal).

These are the hypotheses of the deterministic inverse-perturbation and leverage bounds for
the local-polynomial design matrix. -/
theorem localPoly_goodDesign_of_momentEvent (D : InteriorDesign) (p : ℕ)
    {N : ℕ} {h : ℝ} (hN : 0 < N) (hh : 0 < h) (hwindow : h ≤ D.radius)
    (x : Fin N → ℝ) (hx : x ∈ momentEvent D p h N (designTolerance D p)) :
    let B := designMatrix p (fun i => (x i - D.center) / h)
      (fun i => D.kernel ((x i - D.center) / h))
    let T := weightMomentMatrix p (fun u => D.kernel u * D.density (D.center + h * u))
    let η := (N : ℝ) * h * designTolerance D p
    let c := inverseRowConstant D p / ((N : ℝ) * h)
    (∀ i, (∑ j, |(((N : ℝ) * h) • T)⁻¹ i j|) ≤ c) ∧
      (∀ j k, |B j k - (N : ℝ) * h * T j k| ≤ η) ∧
      c * ((p + 1 : ℝ) * η) ≤ 1 / 2 ∧
      2 * c ^ 2 * ((p + 1 : ℝ) * η) ≤ inverseConstant D p / ((N : ℝ) * h) := by
  classical
  dsimp only
  have hNh : 0 < (N : ℝ) * h := mul_pos (by exact_mod_cast hN) hh
  let := invertibleOfNonzero hNh.ne'
  obtain ⟨_, _, hsmall, hpert⟩ := designTolerance_spec D p
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    rw [Matrix.inv_smul _ _
      ((Matrix.isUnit_iff_isUnit_det _).mp (shapeMoment_posDef D p hh hwindow).isUnit)]
    simp only [Matrix.smul_apply, smul_eq_mul, invOf_eq_inv, abs_mul,
      abs_of_pos (inv_pos.mpr hNh), ← Finset.mul_sum]
    simpa only [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left (shape_inverse_rows D p hh hwindow i)
        (inv_nonneg.mpr hNh.le)
  · intro j k
    have hclose := hx j k
    rw [populationMoment_eq_shape D p hh] at hclose
    rw [rescaled_designMatrix_eq D p hN hh x]
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_sub, abs_mul, abs_of_pos hNh]
    exact mul_le_mul_of_nonneg_left hclose hNh.le
  · convert hsmall using 1
    field_simp
  · apply (le_div_iff₀ hNh).mpr
    convert hpert using 1 <;> first | rfl | field_simp

/-- **On the moment event the design is good.** Let [the design density lie between `f_min > 0`
and `f_max` on `[x₀ − r, x₀ + r]`, and the kernel `K` be measurable, nonnegative, bounded,
zero outside `[−1, 1]` and at least `K_min > 0` on `[−Δ, Δ]`](hyp:D). Take [a positive
sample size `N`](hyp:hN), [a positive bandwidth `h`](hyp:hh) [not exceeding
`r`](hyp:hwindow), and [design points `x_1, …, x_N`](hyp:x) for which [every empirical
moment `(N h)⁻¹ ∑_i K(u_i) u_i^(j+k)`, `u_i = (x_i − x₀)/h`, `0 ≤ j, k ≤ p`, is within the
design tolerance `t₀` of its expectation](hyp:hx). Then [the weighted design matrix `M` with
entries `∑_i K(u_i) (x_i − x₀)^(j+k)` is invertible, `(M⁻¹)₀₀ ≤ 2 c_inv/(N h)`, and `√(M₀₀
(M⁻¹)₀₀) ≤ √(2 c_inv (c_top + 1))`](goal).

Here `c_inv = (G⁻¹)₀₀/f_min` and `c_top = f_max ∫ K(u) du`, with `G` the kernel moment
matrix. The first bound controls the variance of the local-polynomial intercept, the second
its bias. -/
theorem localPoly_leverage_on_momentEvent (D : InteriorDesign) (p : ℕ)
    {N : ℕ} {h : ℝ} (hN : 0 < N) (hh : 0 < h) (hwindow : h ≤ D.radius)
    (x : Fin N → ℝ) (hx : x ∈ momentEvent D p h N (designTolerance D p)) :
    let M := designMatrix p (fun i => x i - D.center)
      (fun i => D.kernel ((x i - D.center) / h))
    IsUnit M.det ∧ M⁻¹ 0 0 ≤ 2 * inverseConstant D p / ((N : ℝ) * h) ∧
      Real.sqrt (M 0 0 * M⁻¹ 0 0)
        ≤ Real.sqrt (2 * inverseConstant D p * (topConstant D + 1)) := by
  dsimp only
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hNh : 0 < (N : ℝ) * h := mul_pos hNreal hh
  obtain ⟨hrow, _, _⟩ := designConstants_positive D p
  obtain ⟨htol, htol_one, _, _⟩ := designTolerance_spec D p
  obtain ⟨hrows, hclose, hsmall, hpert⟩ :=
    localPoly_goodDesign_of_momentEvent D p hN hh hwindow x hx
  have hc : 0 ≤ inverseRowConstant D p / ((N : ℝ) * h) :=
    (div_pos hrow hNh).le
  have hη : 0 ≤ (N : ℝ) * h * designTolerance D p := (mul_pos hNh htol).le
  have hlo : ∀ a, |a - D.center| ≤ h → D.lower ≤ D.density a :=
    fun a ha => D.density_lower a (ha.trans hwindow)
  have hhi : ∀ a, |a - D.center| ≤ h → D.density a ≤ D.upper :=
    fun a ha => D.density_upper a (ha.trans hwindow)
  have hfactor := unscaled_designMatrix_factor D p hh x
  have hsmall' : (inverseRowConstant D p / ((N : ℝ) * h)) *
      ((p + 1 : ℕ) * ((N : ℝ) * h * designTolerance D p)) ≤ 1 / 2 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hsmall
  have hpert' : 2 * (inverseRowConstant D p / ((N : ℝ) * h)) ^ 2 *
      ((p + 1 : ℕ) * ((N : ℝ) * h * designTolerance D p)) ≤
      ((weightMomentMatrix p D.kernel)⁻¹ 0 0 / D.lower) / ((N : ℝ) * h) := by
    simpa only [Nat.cast_add, Nat.cast_one, inverseConstant] using hpert
  obtain ⟨hdet, hinv⟩ := localPoly_density_inv00_rate hh hNreal D.lower_pos
    D.kernel_nonneg D.kernel_support (shape_moments_integrable D p hh hwindow)
    (kernel_moments_integrable D p) (kernelMoment_posDef D p)
    (shapeMoment_posDef D p hh hwindow) hlo hfactor hc hη hrows hclose hsmall' hpert'
  have hηle : (N : ℝ) * h * designTolerance D p ≤ (N : ℝ) * h := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left htol_one hNh.le
  have hBpsd := designMatrix_posSemidef (p := p)
    (x := fun i => (x i - D.center) / h)
    (fun i => D.kernel_nonneg ((x i - D.center) / h))
  have hlev := localPoly_density_leverage_bound hh hNreal D.lower_pos
    D.lower_le_upper D.kernel_nonneg D.kernel_support
    (shape_moments_integrable D p hh hwindow) (kernel_moments_integrable D p)
    (kernelMoment_posDef D p) (shapeMoment_posDef D p hh hwindow)
    hlo hhi hfactor hc hη hrows hclose hsmall' hpert' hηle
    hBpsd.diag_nonneg hBpsd.inv.diag_nonneg
  refine ⟨hdet, ?_, ?_⟩
  · simpa only [inverseConstant, mul_div_assoc] using hinv
  · simpa [inverseConstant, topConstant, weightMomentMatrix] using hlev

/-- **On the moment event the estimator is the weighted least-squares intercept.** Let [the
design density lie between `f_min > 0` and `f_max` on `[x₀ − r, x₀ + r]`, and the kernel `K`
be measurable, nonnegative, bounded, zero outside `[−1, 1]` and at least `K_min > 0` on
`[−Δ, Δ]`](hyp:D). Take [a positive sample size `N`](hyp:hN), [a positive bandwidth
`h`](hyp:hh) [not exceeding `r`](hyp:hwindow), [design points `x_1, …, x_N`](hyp:x) for
which [every empirical moment `(N h)⁻¹ ∑_i K(u_i) u_i^(j+k)`, `u_i = (x_i − x₀)/h`, `0 ≤ j,
k ≤ p`, is within the design tolerance of its expectation](hyp:hx), and [responses `y_1, …,
y_N`](hyp:y). If [coefficients `c_0, …, c_p` minimize the weighted sum of squares `∑_i
K(u_i) (y_i − ∑_j c_j (x_i − x₀)^j)²`](hyp:hmin), then [the weighted design matrix is
invertible and the local-polynomial intercept `∑_i S_i y_i` equals `c_0`](goal).

So on the moment event the zero-by-convention value for singular designs never occurs, and
the estimator is the classical local-polynomial fit at `x₀`. -/
theorem rawIntercept_eq_wls_intercept (D : InteriorDesign) (p : ℕ)
    {N : ℕ} {h : ℝ} (hN : 0 < N) (hh : 0 < h) (hwindow : h ≤ D.radius)
    (x : Fin N → ℝ) (hx : x ∈ momentEvent D p h N (designTolerance D p))
    (y : Fin N → ℝ) {c : Fin (p + 1) → ℝ}
    (hmin : ∀ c' : Fin (p + 1) → ℝ,
      (∑ i, D.kernel ((x i - D.center) / h) *
          (y i - ∑ j, c j * (x i - D.center) ^ (j : ℕ)) ^ 2) ≤
        ∑ i, D.kernel ((x i - D.center) / h) *
          (y i - ∑ j, c' j * (x i - D.center) ^ (j : ℕ)) ^ 2) :
    IsUnit (designMatrix p (fun i => x i - D.center)
        (fun i => D.kernel ((x i - D.center) / h))).det ∧
      rawIntercept D p h x y = c 0 := by
  have hdet := (localPoly_leverage_on_momentEvent D p hN hh hwindow x hx).1
  exact ⟨hdet, (wls_intercept_eq_equivKernelSmoother
    (fun i => D.kernel_nonneg _) hdet hmin).symm⟩

end Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate

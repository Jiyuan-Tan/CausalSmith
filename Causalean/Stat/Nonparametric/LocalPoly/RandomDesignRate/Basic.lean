/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.Mathlib.Analysis.Calculus.HolderTaylor
public import Causalean.Mathlib.Analysis.ClipInterval
public import Causalean.Stat.Nonparametric.LocalPoly.EstimatorRisk.DensityConstants
public import Causalean.Stat.Nonparametric.LocalPoly.Weights
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Random-design local-polynomial regression in dimension one: model, constants, estimator

The setting is one-dimensional local-polynomial regression at an interior point `x₀`. The design
points are independent draws from a law with a Lebesgue density that is bounded above and below
by positive constants on a window `[x₀ − r, x₀ + r]`; the kernel is measurable, nonnegative,
bounded, supported on `[−1, 1]`, and bounded below on a subinterval `[−Δ, Δ]`.

This file defines the two bundles of assumptions (`KernelDesign` with the upper bounds only, and
`InteriorDesign` adding the lower bounds), the kernel-weighted empirical and population moment
matrices and the event on which they are entrywise close, the explicit constants that enter the
risk bound, the local Hölder class of regression functions, and the estimator: the weighted
least-squares intercept (zero by convention when the weighted design matrix is singular) and its
clipped version.

References: Tsybakov (2009), *Introduction to Nonparametric Estimation*, §1.6
(https://doi.org/10.1007/b13794); Fan and Gijbels (1996), *Local Polynomial Modelling and Its
Applications*, Theorem 3.1; Stone (1982), *Optimal global rates of convergence for nonparametric
regression*. Tsybakov's Theorem 1.7 is stated for a fixed design; the concentration step of this
directory supplies the random-design argument.
-/

@[expose] public section

noncomputable section
namespace Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate

open MeasureTheory ProbabilityTheory Causalean.Stat.Nonparametric
open Causalean.Mathlib.Analysis.HolderTaylor
open scoped BigOperators

/-- **Design law and kernel for kernel-weighted moments in dimension one.** The design points
are drawn from [a probability law](hyp:law,probability) on the real line with [a
measurable](hyp:density_measurable) [nonnegative](hyp:density_nonneg) [Lebesgue density
`f`](hyp:density,law_density). Around [the evaluation point `x₀`](hyp:center) there is [a window
`[x₀ − r, x₀ + r]` of positive radius](hyp:radius,radius_pos) on which
[`f ≤ f_max`](hyp:upper,density_upper). [The kernel `K`](hyp:kernel) is
[measurable](hyp:kernel_measurable), [nonnegative](hyp:kernel_nonneg), [zero outside
`[−1, 1]`](hyp:kernel_support) and [at most `K_max`](hyp:kernelMax,kernel_upper).

Every field is an assumption on the design law or on the kernel; none refers to a sample. These
assumptions suffice for the concentration of kernel-weighted design moments; no lower bound on
the density or the kernel is included. -/
structure KernelDesign where
  /-- The law of one design point. -/
  law : Measure ℝ
  /-- The design law is a probability measure. -/
  probability : IsProbabilityMeasure law
  /-- The design density `f`. -/
  density : ℝ → ℝ
  /-- The design density is measurable. -/
  density_measurable : Measurable density
  /-- The design density is nonnegative. -/
  density_nonneg : ∀ x, 0 ≤ density x
  /-- The design law has density `f` with respect to Lebesgue measure. -/
  law_density : law = volume.withDensity (fun x => ENNReal.ofReal (density x))
  /-- The evaluation point `x₀`. -/
  center : ℝ
  /-- The radius `r` of the window `[x₀ − r, x₀ + r]` on which the density bounds hold. -/
  radius : ℝ
  /-- The window has positive radius. -/
  radius_pos : 0 < radius
  /-- The upper density bound `f_max`. -/
  upper : ℝ
  /-- The density is at most `f_max` on the window. -/
  density_upper : ∀ x, |x - center| ≤ radius → density x ≤ upper
  /-- The kernel `K`. -/
  kernel : ℝ → ℝ
  /-- The kernel is measurable. -/
  kernel_measurable : Measurable kernel
  /-- The kernel is nonnegative. -/
  kernel_nonneg : ∀ u, 0 ≤ kernel u
  /-- The kernel vanishes outside `[−1, 1]`. -/
  kernel_support : ∀ u, 1 < |u| → kernel u = 0
  /-- The upper kernel bound `K_max`. -/
  kernelMax : ℝ
  /-- The kernel is at most `K_max`. -/
  kernel_upper : ∀ u, kernel u ≤ kernelMax

/-- **Design, kernel and evaluation point for one-dimensional local-polynomial regression at an
interior point.** In addition to a design law whose density `f` is at most `f_max` on a window
`[x₀ − r, x₀ + r]` around the evaluation point, and a measurable nonnegative kernel `K ≤ K_max`
vanishing outside `[−1, 1]`, the density satisfies [`f ≥ f_min`](hyp:lower,density_lower) on the
window with [`f_min > 0`](hyp:lower_pos), and the kernel is [at least
`K_min`](hyp:kernelMin,kernel_lower) with [`K_min > 0`](hyp:kernelMin_pos) on [an interval
`[−Δ, Δ]` with `Δ > 0`](hyp:subradius,subradius_pos).

Every field is an assumption on the design law or on the kernel; none refers to a sample. The
density bounds are required at every point of the window. It follows that `f_min ≤ f_max`,
`K_max > 0` and `Δ ≤ 1`. -/
structure InteriorDesign extends KernelDesign where
  /-- The lower density bound `f_min`. -/
  lower : ℝ
  /-- The lower density bound is positive. -/
  lower_pos : 0 < lower
  /-- The density is at least `f_min` on the window. -/
  density_lower : ∀ x, |x - center| ≤ radius → lower ≤ density x
  /-- The half-width `Δ` of the interval on which the kernel is bounded below. -/
  subradius : ℝ
  /-- The interval `[−Δ, Δ]` has positive length. -/
  subradius_pos : 0 < subradius
  /-- The lower kernel bound `K_min`. -/
  kernelMin : ℝ
  /-- The lower kernel bound is positive. -/
  kernelMin_pos : 0 < kernelMin
  /-- The kernel is at least `K_min` on `[−Δ, Δ]`. -/
  kernel_lower : ∀ u, |u| ≤ subradius → kernelMin ≤ kernel u

/-- An interior design is read as its underlying design law and kernel wherever only the upper
bounds on the density and the kernel are needed. -/
instance : Coe InteriorDesign KernelDesign := ⟨InteriorDesign.toKernelDesign⟩

/-- For [a design whose nonnegative density is at most `f_max` on a window around the evaluation
point](hyp:D), [`f_max ≥ 0`](goal). -/
theorem KernelDesign.upper_nonneg (D : KernelDesign) : 0 ≤ D.upper :=
  (D.density_nonneg D.center).trans
    (D.density_upper D.center (by simpa using D.radius_pos.le))

/-- For [a nonnegative kernel that is at most `K_max`](hyp:D), [`K_max ≥ 0`](goal). -/
theorem KernelDesign.kernelMax_nonneg (D : KernelDesign) : 0 ≤ D.kernelMax :=
  (D.kernel_nonneg 0).trans (D.kernel_upper 0)

/-- For [a design whose density lies between `f_min` and `f_max` on a window around the
evaluation point](hyp:D), [`f_min ≤ f_max`](goal). -/
theorem InteriorDesign.lower_le_upper (D : InteriorDesign) : D.lower ≤ D.upper :=
  (D.density_lower D.center (by simpa using D.radius_pos.le)).trans
    (D.density_upper D.center (by simpa using D.radius_pos.le))

/-- For [a kernel that is at most `K_max` and at least `K_min > 0` on an interval around
zero](hyp:D), [`K_max > 0`](goal). -/
theorem InteriorDesign.kernelMax_pos (D : InteriorDesign) : 0 < D.kernelMax :=
  D.kernelMin_pos.trans_le
    ((D.kernel_lower 0 (by simpa using D.subradius_pos.le)).trans (D.kernel_upper 0))

/-- For [a kernel that vanishes outside `[−1, 1]` and is at least `K_min > 0` on
`[−Δ, Δ]`](hyp:D), [`Δ ≤ 1`](goal). -/
theorem InteriorDesign.subradius_le_one (D : InteriorDesign) : D.subradius ≤ 1 := by
  by_contra hlt
  have hpos := D.subradius_pos
  have hlow := D.kernel_lower D.subradius (by rw [abs_of_pos hpos])
  rw [D.kernel_support D.subradius (by rw [abs_of_pos hpos]; exact lt_of_not_ge hlt)] at hlow
  exact absurd D.kernelMin_pos (not_lt.mpr hlow)

/-- For [a kernel `K` and an evaluation point `x₀`, as carried by a design](hyp:D), [a bandwidth
`h`](hyp:h), [two exponents `j` and `k`](hyp:j,k) and [a design point `x`](hyp:x), the
[kernel-weighted monomial](goal) is `K(u) · u^j · u^k` with `u = (x − x₀)/h`. -/
def momentSummand (D : KernelDesign) (h : ℝ) (j k : ℕ) (x : ℝ) : ℝ :=
  D.kernel ((x - D.center) / h) *
    (((x - D.center) / h) ^ j * ((x - D.center) / h) ^ k)

/-- For [a design law with kernel `K` and evaluation point `x₀`](hyp:D), [a polynomial degree
`p`](hyp:p) and [a bandwidth `h`](hyp:h), the [population moment matrix](goal) is the `(p+1)
× (p+1)` matrix whose `(j,k)` entry is `E[K(u) u^(j+k)] / h`, where `u = (X − x₀)/h` and `X`
is one draw from the design law. -/
def populationMoment (D : KernelDesign) (p : ℕ) (h : ℝ) :
    Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ :=
  fun j k => (∫ x, momentSummand D h j k x ∂D.law) / h

/-- For [a kernel `K` and evaluation point `x₀`, as carried by a design](hyp:D), [a polynomial
degree `p`](hyp:p), [a bandwidth `h`](hyp:h) and [design points `x_1, …, x_N`](hyp:x), the
[empirical moment matrix](goal) is the `(p+1) × (p+1)` matrix whose `(j,k)` entry is `(N
h)⁻¹ ∑_i K(u_i) u_i^(j+k)`, where `u_i = (x_i − x₀)/h`. -/
def empiricalMoment (D : KernelDesign) (p : ℕ) (h : ℝ) {N : ℕ}
    (x : Fin N → ℝ) : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ :=
  fun j k => (∑ i, momentSummand D h j k (x i)) / ((N : ℝ) * h)

/-- For [a design law with kernel `K` and evaluation point `x₀`](hyp:D), [a polynomial degree
`p`](hyp:p), [a bandwidth `h`](hyp:h), [a sample size `N`](hyp:N) and [a tolerance
`t`](hyp:t), the [moment event](goal) is the set of design vectors `(x_1, …, x_N)` for which
every entry `(N h)⁻¹ ∑_i K(u_i) u_i^(j+k)`, `u_i = (x_i − x₀)/h`, `0 ≤ j, k ≤ p`, of the
empirical moment matrix is within `t` of its expectation `E[K(u) u^(j+k)] / h`. -/
def momentEvent (D : KernelDesign) (p : ℕ) (h : ℝ) (N : ℕ) (t : ℝ) :
    Set (Fin N → ℝ) :=
  {x | ∀ j k, |empiricalMoment D p h x j k - populationMoment D p h j k| ≤ t}

/-- For [a kernel that is at least `K_min > 0` on an interval `[−Δ, Δ]`, as carried by a
design](hyp:D), and [a polynomial degree `p`](hyp:p), the [reference moment matrix](goal) is
the `(p+1) × (p+1)` matrix with `(j,k)` entry `∫_{−Δ}^{Δ} u^(j+k) du`. -/
def referenceMoment (D : InteriorDesign) (p : ℕ) :
    Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ :=
  weightMomentMatrix p (Set.Icc (-D.subradius) D.subradius |>.indicator (fun _ => 1))

/-- For [a design whose density is at least `f_min > 0` near the evaluation point and whose
kernel is at least `K_min > 0` on `[−Δ, Δ]`](hyp:D), and [a polynomial degree `p`](hyp:p),
the [inverse-row constant](goal) is `c_row = (p+1) · tr(R⁻¹) / (f_min K_min)`, where `R` is
the matrix of monomial moments `∫_{−Δ}^{Δ} u^(j+k) du`.

It bounds every absolute row sum of the inverse population moment matrix, uniformly in the
bandwidth. -/
def inverseRowConstant (D : InteriorDesign) (p : ℕ) : ℝ :=
  (p + 1 : ℝ) * (∑ j, (referenceMoment D p)⁻¹ j j) / (D.lower * D.kernelMin)

/-- For [a design whose density is at least `f_min > 0` near the evaluation point, with kernel
`K`](hyp:D), and [a polynomial degree `p`](hyp:p), the [intercept inverse constant](goal) is
`c_inv = (G⁻¹)₀₀ / f_min`, where `G` is the `(p+1) × (p+1)` kernel moment matrix with
`(j,k)` entry `∫ K(u) u^(j+k) du`. -/
def inverseConstant (D : InteriorDesign) (p : ℕ) : ℝ :=
  (weightMomentMatrix p D.kernel)⁻¹ 0 0 / D.lower

/-- For [a design whose density is at most `f_max` near the evaluation point, with kernel
`K`](hyp:D), the [total-weight constant](goal) is `c_top = f_max · ∫ K(u) du`.

Only the upper design data are used; this constant does not depend on the polynomial degree. -/
def topConstant (D : KernelDesign) : ℝ :=
  D.upper * ∫ u, D.kernel u

/-- For [a design with density bounds `f_min ≤ f_max` near the evaluation point and a kernel
bounded below on `[−Δ, Δ]`](hyp:D), and [a polynomial degree `p`](hyp:p), the [design
tolerance](goal) is `t₀ = min(1, 1/(2 (p+1) c_row), c_inv/(2 (p+1) c_row²))`, where `c_row =
(p+1) tr(R⁻¹)/(f_min K_min)` and `c_inv = (G⁻¹)₀₀/f_min` are built from the monomial moment
matrix `R` on `[−Δ, Δ]` and the kernel moment matrix `G`.

When every empirical moment is within `t₀` of its expectation, the empirical moment matrix
is invertible and its top-left inverse entry is at most `2 c_inv/(N h)`, twice the
corresponding population-entry bound. -/
def designTolerance (D : InteriorDesign) (p : ℕ) : ℝ :=
  min 1 (min (1 / (2 * (p + 1 : ℝ) * inverseRowConstant D p))
    (inverseConstant D p / (2 * (p + 1 : ℝ) * inverseRowConstant D p ^ 2)))

/-- For [a design whose density is at most `f_max` near the evaluation point and whose kernel is
at most `K_max`](hyp:D), and [a tolerance `t`](hyp:t), the [Bernstein exponent](goal) is `t²
/ (4 (2 f_max K_max² + K_max t))`. -/
def tailExponent (D : KernelDesign) (t : ℝ) : ℝ :=
  t ^ 2 / (4 * (2 * D.upper * D.kernelMax ^ 2 + D.kernelMax * t))

/-- For [a design whose density is at most `f_max` near the evaluation point and whose kernel is
at most `K_max`](hyp:D), [a polynomial degree `p`](hyp:p), [a sample size `N`](hyp:N), [a
bandwidth `h`](hyp:h) and [a tolerance `t`](hyp:t), the [failure bound](goal) is `2 (p+1)²
exp(−N h t² / (4 (2 f_max K_max² + K_max t)))`. -/
def failureBound (D : KernelDesign) (p N : ℕ) (h t : ℝ) : ℝ :=
  2 * (p + 1 : ℝ) ^ 2 * Real.exp (-(N : ℝ) * h * tailExponent D t)

/-- [A regression function `m`](hyp:m) belongs to the [local Hölder class](goal) with
[smoothness `β`](hyp:β) and [constant `H`](hyp:H) on [the window `[x₀ − r, x₀ + r]`](hyp:x₀,r)
when [`β > 0`](step:1), [`H ≥ 0`](step:2), [`m` is
`p` times continuously differentiable on the window, where `p = ⌈β⌉ − 1` is the largest
integer strictly below `β`](step:3), and [its `p`-th derivative within the window satisfies
`|m⁽ᵖ⁾(x) − m⁽ᵖ⁾(y)| ≤ H |x − y|^(β − p)` for all `x, y` in the window](step:4).

Nothing is required of `m` outside the window; at the two endpoints the derivatives are
one-sided. For integer `β` this is the class of functions whose `(β − 1)`-th derivative is
Lipschitz on the window, as in Tsybakov (2009), Definition 1.2, restricted to the window. A
function that is `p` times continuously differentiable on the whole line with the same
Hölder bound on the window belongs to the class. -/
def HolderRegression (x₀ r β H : ℝ) (m : ℝ → ℝ) : Prop :=
  0 < β ∧ 0 ≤ H ∧
    ContDiffOn ℝ (holderDerivOrder β) m (Set.Icc (x₀ - r) (x₀ + r)) ∧
    ∀ x ∈ Set.Icc (x₀ - r) (x₀ + r),
    ∀ y ∈ Set.Icc (x₀ - r) (x₀ + r),
      |iteratedDerivWithin (holderDerivOrder β) m
          (Set.Icc (x₀ - r) (x₀ + r)) x -
        iteratedDerivWithin (holderDerivOrder β) m
          (Set.Icc (x₀ - r) (x₀ + r)) y|
        ≤ H * |x - y| ^ (β - (holderDerivOrder β : ℝ))

/-- **Global smoothness implies membership in the local Hölder class.** For [a window `[x₀ − r,
x₀ + r]` of positive radius](hyp:x₀,r,hr), if [`β > 0`](hyp:hβ), [`H ≥
0`](hyp:hH), [`m` is `p = ⌈β⌉ − 1` times continuously differentiable on the whole real
line](hyp:hm), and [its `p`-th derivative satisfies `|m⁽ᵖ⁾(x) − m⁽ᵖ⁾(y)| ≤ H |x − y|^(β −
p)` for all `x, y` in the window](hyp:hb), then [`m` belongs to the local Hölder class of
smoothness `β` and constant `H` on the window](goal). -/
theorem HolderRegression.of_contDiff (x₀ r : ℝ) (hr : 0 < r) {β H : ℝ} {m : ℝ → ℝ}
    (hβ : 0 < β) (hH : 0 ≤ H) (hm : ContDiff ℝ (holderDerivOrder β) m)
    (hb : ∀ x ∈ Set.Icc (x₀ - r) (x₀ + r),
      ∀ y ∈ Set.Icc (x₀ - r) (x₀ + r),
        |iteratedDeriv (holderDerivOrder β) m x - iteratedDeriv (holderDerivOrder β) m y|
          ≤ H * |x - y| ^ (β - (holderDerivOrder β : ℝ))) :
    HolderRegression x₀ r β H m := by
  have hu : UniqueDiffOn ℝ (Set.Icc (x₀ - r) (x₀ + r)) :=
    uniqueDiffOn_Icc (by linarith)
  refine ⟨hβ, hH, hm.contDiffOn, fun x hx y hy => ?_⟩
  rw [iteratedDerivWithin_eq_iteratedDeriv hu hm.contDiffAt hx,
    iteratedDerivWithin_eq_iteratedDeriv hu hm.contDiffAt hy]
  exact hb x hx y hy

/-- For [a design with density bounds `f_min ≤ f_max` near the evaluation point and kernel
`K`](hyp:D), [a smoothness `β`](hyp:β) and [a Hölder constant `H`](hyp:H), the [bias
constant](goal) is `C_bias = (H / p!) · √(2 c_inv (c_top + 1))`, where `p = ⌈β⌉ − 1`, `c_inv
= (G⁻¹)₀₀ / f_min`, `c_top = f_max ∫ K(u) du`, and `G` is the `(p+1) × (p+1)` kernel moment
matrix. -/
def biasConstant (D : InteriorDesign) (β H : ℝ) : ℝ :=
  (H / (holderDerivOrder β).factorial) *
    Real.sqrt (2 * inverseConstant D (holderDerivOrder β) *
      (topConstant D + 1))

/-- For [a design with density lower bound `f_min` near the evaluation point and a kernel at
most `K_max`](hyp:D), [a polynomial degree `p`](hyp:p) and [a noise scale `σ`](hyp:σ), the
[variance constant](goal) is `C_var = 2 σ² K_max c_inv`, where `c_inv = (G⁻¹)₀₀ / f_min` and
`G` is the `(p+1) × (p+1)` kernel moment matrix. -/
def varianceConstant (D : InteriorDesign) (p : ℕ) (σ : ℝ) : ℝ :=
  2 * σ ^ 2 * D.kernelMax * inverseConstant D p

/-- For [a kernel `K` and evaluation point `x₀`, as carried by a design](hyp:D), [a polynomial
degree `p`](hyp:p), [a bandwidth `h`](hyp:h), [design points `x_1, …, x_N`](hyp:x) and
[responses `y_1, …, y_N`](hyp:y), the [local-polynomial intercept](goal) is `∑_i S_i y_i`
with weights `S_i = ∑_k (M⁻¹)_{0k} K(u_i) (x_i − x₀)^k`, where `u_i = (x_i − x₀)/h` and `M`
is the weighted design matrix with `(j,k)` entry `∑_i K(u_i) (x_i − x₀)^(j+k)`.

When `M` is invertible this is the intercept of the degree-`p` polynomial in `x − x₀` fitted
to the responses by least squares with weights `K(u_i)`, that is, the local-polynomial
estimate of the regression function at `x₀`. When `M` is singular its inverse is read as the
zero matrix, so the value is zero by convention. -/
def rawIntercept (D : KernelDesign) (p : ℕ) (h : ℝ) {N : ℕ}
    (x y : Fin N → ℝ) : ℝ :=
  ∑ i, equivKernelWeight p (fun i => x i - D.center)
    (fun i => D.kernel ((x i - D.center) / h)) i * y i

/-- For [a kernel `K` and evaluation point `x₀`, as carried by a design](hyp:D), [a polynomial
degree `p`](hyp:p), [a bandwidth `h`](hyp:h), [a clipping level `M`](hyp:M), [design points
`x_1, …, x_N`](hyp:x) and [responses `y_1, …, y_N`](hyp:y), the [clipped local-polynomial
intercept](goal) is the weighted least-squares intercept of the degree-`p` fit at `x₀` (zero
by convention when the weighted design matrix is singular), moved to the nearest point of
`[−M, M]`. -/
def clippedIntercept (D : KernelDesign) (p : ℕ) (h M : ℝ) {N : ℕ}
    (x y : Fin N → ℝ) : ℝ :=
  Causalean.Mathlib.Analysis.clipIcc (-M) M (rawIntercept D p h x y)

end Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate

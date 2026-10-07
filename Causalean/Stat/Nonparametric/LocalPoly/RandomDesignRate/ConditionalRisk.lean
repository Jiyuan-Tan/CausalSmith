/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.Mathlib.MeasureTheory.Matrix
public import Causalean.Stat.Nonparametric.LocalPoly.EstimatorRisk.EstimatorRisk
public import Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate.Basic
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Conditional risk of the clipped local-polynomial intercept on a fixed design, dimension one

For fixed design points and independent responses with conditional means `m(x_i)` and
conditional variances at most `σ²`, the mean-squared error of the local-polynomial intercept is
at most its squared noise-free bias plus `σ²` times the sum of squared equivalent-kernel weights
(`rawIntercept_fibre_mse_le`). The bias is at most `(H / p!) L h^β` for a Hölder regression
function when the leverage product of the design is at most `L²` (`windowed_localPoly_bias`);
design points outside the kernel window carry zero weight and are unrestricted.

`localPoly_fibre_mse_of_designBounds` combines the two: on a design whose inverse intercept
entry is of order `1/(N h)` and whose leverage product is bounded, the intercept clipped to
`[−M, M]` has conditional mean-squared error at most `C_bias² h^(2β) + C_var/(N h)`, because
clipping cannot increase the squared distance to a target inside `[−M, M]`. The responses need
only finite conditional second moments.
-/

public section

namespace Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate

open MeasureTheory ProbabilityTheory Causalean.Stat Causalean.Stat.Nonparametric
open Causalean.Mathlib.Analysis.HolderTaylor
open scoped BigOperators ProbabilityTheory

/-- For [a kernel `K` that vanishes outside `[−1, 1]`, with evaluation point `x₀`](hyp:D), [a
positive bandwidth `h`](hyp:hh) and design points `x_1, …, x_N`, if [`|x_i − x₀| >
h`](hyp:hi) then [the equivalent-kernel weight `S_i = ∑_k (M⁻¹)_{0k} K((x_i − x₀)/h) (x_i −
x₀)^k` of the `i`-th observation is zero](goal). -/
theorem equivKernelWeight_eq_zero_of_outside (D : KernelDesign) (p : ℕ) {N : ℕ} {h : ℝ}
    (hh : 0 < h) (x : Fin N → ℝ) {i : Fin N} (hi : ¬ |x i - D.center| ≤ h) :
    equivKernelWeight p (fun i => x i - D.center)
      (fun i => D.kernel ((x i - D.center) / h)) i = 0 := by
  have hw : D.kernel ((x i - D.center) / h) = 0 := by
    apply D.kernel_support
    rw [abs_div, abs_of_pos hh]
    exact (lt_div_iff₀ hh).2 (by simpa only [one_mul] using lt_of_not_ge hi)
  simp [equivKernelWeight, hw]

/-- **Bias of the local-polynomial intercept on a fixed design.** Let [the kernel `K` be
nonnegative and zero outside `[−1, 1]`, with evaluation point `x₀` and window radius
`r`](hyp:D), and let [the regression function `m` be, on the window `[x₀ − r, x₀ + r]`, `p =
⌈β⌉ − 1` times continuously differentiable with `p`-th derivative Hölder of order `β − p`
and constant `H`](hyp:hm). For [a positive bandwidth `h`](hyp:hh) [not exceeding
`r`](hyp:hwindow) and [design points `x_1, …, x_N`](hyp:x) whose [weighted design matrix `M`
is invertible](hyp:hdet) with [`√(M₀₀ (M⁻¹)₀₀) ≤ L`](hyp:hlev), [the intercept computed from
the noise-free responses `m(x_i)` satisfies `|∑_i S_i m(x_i) − m(x₀)| ≤ (H / p!) · L ·
h^β`](goal).

Design points outside the kernel window `[x₀ − h, x₀ + h]` are allowed; they receive weight
zero. -/
theorem windowed_localPoly_bias (D : KernelDesign) {β H h L : ℝ}
    {N : ℕ} {m : ℝ → ℝ} (hm : HolderRegression D.center D.radius β H m)
    (hh : 0 < h) (hwindow : h ≤ D.radius) (x : Fin N → ℝ)
    (hdet : IsUnit (designMatrix (holderDerivOrder β) (fun i => x i - D.center)
      (fun i => D.kernel ((x i - D.center) / h))).det)
    (hlev : Real.sqrt
      ((designMatrix (holderDerivOrder β) (fun i => x i - D.center)
        (fun i => D.kernel ((x i - D.center) / h))) 0 0 *
      (designMatrix (holderDerivOrder β) (fun i => x i - D.center)
        (fun i => D.kernel ((x i - D.center) / h)))⁻¹ 0 0) ≤ L) :
    |rawIntercept D (holderDerivOrder β) h x (fun i => m (x i)) - m D.center|
      ≤ (H / (holderDerivOrder β).factorial) * L * h ^ β := by
  classical
  let p := holderDerivOrder β
  let w : Fin N → ℝ := fun i => D.kernel ((x i - D.center) / h)
  let S : Fin N → ℝ := equivKernelWeight p (fun i => x i - D.center) w
  let a : Fin N → ℝ := fun i => if |x i - D.center| ≤ h then x i else D.center
  have hzero (i : Fin N) (hi : ¬ |x i - D.center| ≤ h) : S i = 0 :=
    equivKernelWeight_eq_zero_of_outside D p hh x hi
  have hwin (i : Fin N) : |a i - D.center| ≤ h := by
    by_cases hi : |x i - D.center| ≤ h
    · simp only [a, if_pos hi]
      exact hi
    · simp [a, hi, hh.le]
  have ha (i : Fin N) :
      a i ∈ Set.Icc (D.center - D.radius) (D.center + D.radius) := by
    have hi := (abs_le.mp ((hwin i).trans hwindow))
    constructor <;> linarith [hi.1, hi.2]
  have ht : D.center ∈ Set.Icc (D.center - D.radius) (D.center + D.radius) := by
    constructor <;> linarith [D.radius_pos]
  have hrep : ∀ k : ℕ, k ≤ p →
      (∑ i, S i * (a i - D.center) ^ k) = if k = 0 then 1 else 0 := by
    intro k hk
    calc
      (∑ i, S i * (a i - D.center) ^ k)
          = ∑ i, S i * (x i - D.center) ^ k := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : |x i - D.center| ≤ h
            · simp [a, hi]
            · simp [hzero i hi]
      _ = if k = 0 then 1 else 0 := equivKernelWeight_reproduces hdet k hk
  have hsmooth : (∑ i, S i * m (a i)) = rawIntercept D p h x (fun i => m (x i)) := by
    unfold rawIntercept
    apply Finset.sum_congr rfl
    intro i _
    change S i * m (a i) = S i * m (x i)
    by_cases hi : |x i - D.center| ≤ h
    · simp [a, hi]
    · simp [hzero i hi]
  have hbias := linearSmoother_bias_window_within hm.1 hm.2.1 ht ha hwin
    hm.2.2.1 hm.2.2.2 hrep
  rw [hsmooth] at hbias
  have hsq : (∑ i, |S i|) ^ 2 ≤
      (designMatrix p (fun i => x i - D.center) w) 0 0 *
      (designMatrix p (fun i => x i - D.center) w)⁻¹ 0 0 :=
    equivKernelWeight_abs_sum_sq_le hdet (fun i => D.kernel_nonneg _)
  have hsL : (∑ i, |S i|) ≤ L :=
    (Real.le_sqrt_of_sq_le hsq).trans hlev
  exact hbias.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsL (div_nonneg hm.2.1 (by positivity)))
    (Real.rpow_nonneg hh.le β))

/-- For [a measurable kernel and an evaluation point, as carried by a design](hyp:D), [the
local-polynomial intercept is a jointly measurable function of the design points and the
responses, for every degree, sample size and bandwidth](goal). -/
@[fun_prop] theorem rawIntercept_measurable (D : KernelDesign) (p N : ℕ) (h : ℝ) :
    Measurable (fun z : (Fin N → ℝ) × (Fin N → ℝ) => rawIntercept D p h z.1 z.2) := by
  have hw : ∀ i, Measurable (fun z : (Fin N → ℝ) × (Fin N → ℝ) =>
      D.kernel ((z.1 i - D.center) / h)) := fun i =>
    D.kernel_measurable.comp (by fun_prop)
  have hA : ∀ j k : Fin (p + 1), Measurable
      (fun z : (Fin N → ℝ) × (Fin N → ℝ) =>
        designMatrix p (fun i => z.1 i - D.center)
          (fun i => D.kernel ((z.1 i - D.center) / h)) j k) := by
    intro j k
    unfold designMatrix
    fun_prop
  have hInv := Causalean.Mathlib.MeasureTheory.measurable_matrix_inv_apply _ hA
  unfold rawIntercept equivKernelWeight
  fun_prop

/-- For [a measurable kernel and an evaluation point, as carried by a design](hyp:D), [the
clipped local-polynomial intercept is a jointly measurable function of the design points and
the responses, for every degree, sample size, bandwidth and clipping level](goal). -/
@[fun_prop] theorem clippedIntercept_measurable (D : KernelDesign) (p N : ℕ) (h M : ℝ) :
    Measurable (fun z : (Fin N → ℝ) × (Fin N → ℝ) =>
      clippedIntercept D p h M z.1 z.2) :=
  (Causalean.Mathlib.Analysis.measurable_clipIcc (-M) M).comp (rawIntercept_measurable D p N h)

/-- Fix design points `x_1, …, x_N` and a set `A` of indices, and let the responses `Y_1, …,
Y_N` be independent with `Y_i` drawn from [a conditional outcome distribution](hyp:κ) at
`x_i`. If [for each `i` in `A` this distribution has a finite second moment, mean `m(x_i)`
and variance at most `σ²`](hyp:hx), then [the masked responses `Z_i`, equal to `Y_i` for `i`
in `A` and to zero otherwise, are square integrable, have variance at most `σ²`, are
pairwise uncorrelated, and have mean `m(x_i)` for `i` in `A` and zero otherwise](goal).

Nothing is assumed about the responses with index outside `A`. -/
theorem fibre_response_moments {N : ℕ} (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    (m : ℝ → ℝ) (σ : ℝ) (x : Fin N → ℝ) (A : Set (Fin N))
    (hx : ∀ i ∈ A, MemLp (fun y : ℝ => y) 2 (κ (x i)) ∧
      (∫ y, y ∂κ (x i)) = m (x i) ∧ Var[fun y : ℝ => y; κ (x i)] ≤ σ ^ 2) :
    let μ := Measure.pi (fun i => κ (x i))
    (∀ i : Fin N, MemLp (fun y : Fin N → ℝ => A.indicator y i) 2 μ) ∧
      UncorrelatedVarianceFamily (fun i (y : Fin N → ℝ) => A.indicator y i) μ σ ∧
      (∀ i : Fin N, (∫ y : Fin N → ℝ, A.indicator y i ∂μ) =
        A.indicator (fun i => m (x i)) i) := by
  dsimp only
  have hin : ∀ i ∈ A, (fun y : Fin N → ℝ => A.indicator y i) = fun y => y i := fun i hi => by
    funext y
    exact Set.indicator_of_mem hi y
  have hout : ∀ i ∉ A, (fun y : Fin N → ℝ => A.indicator y i) = fun _ => 0 := fun i hi => by
    funext y
    exact Set.indicator_of_notMem hi y
  have hYin : ∀ i ∈ A, MemLp (fun y : Fin N → ℝ => y i) 2
      (Measure.pi (fun i => κ (x i))) := fun i hi =>
    (hx i hi).1.comp_measurePreserving (measurePreserving_eval _ i)
  have hY : ∀ i : Fin N, MemLp (fun y : Fin N → ℝ => A.indicator y i) 2
      (Measure.pi (fun i => κ (x i))) := by
    intro i
    by_cases hi : i ∈ A
    · rw [hin i hi]
      exact hYin i hi
    · rw [hout i hi]
      exact memLp_const 0
  refine ⟨hY, ⟨?_, ?_⟩, ?_⟩
  · intro i
    dsimp only
    by_cases hi : i ∈ A
    · rw [hin i hi]
      exact ((measurePreserving_eval (fun i => κ (x i)) i).variance_fun_comp
        (f := fun y : ℝ => y) measurable_id.aemeasurable).le.trans (hx i hi).2.2
    · rw [hout i hi]
      rw [show (fun _ : Fin N → ℝ => (0 : ℝ)) = 0 from rfl, variance_zero]
      exact sq_nonneg σ
  · intro i j hij
    dsimp only
    by_cases hi : i ∈ A
    · by_cases hj : j ∈ A
      · rw [hin i hi, hin j hj]
        exact ((iIndepFun_pi (fun i => measurable_id.aemeasurable)).indepFun
          hij).covariance_eq_zero (hYin i hi) (hYin j hj)
      · rw [hout j hj]
        exact covariance_const_right 0
    · rw [hout i hi]
      exact covariance_const_left 0
  · intro i
    by_cases hi : i ∈ A
    · rw [hin i hi, Set.indicator_of_mem hi, integral_eval]
      exact (hx i hi).2.1
    · rw [hout i hi, Set.indicator_of_notMem hi]
      simp

/-- For [a kernel `K` that vanishes outside `[−1, 1]`, with evaluation point `x₀`](hyp:D), and
[a positive bandwidth `h`](hyp:hh), [the local-polynomial intercept `∑_i S_i y_i` is
unchanged when every response `y_i` with `|x_i − x₀| > h` is replaced by zero](goal).

Observations outside the kernel window carry zero weight, so the estimator does not depend
on their responses. -/
theorem rawIntercept_eq_sum_indicator (D : KernelDesign) (p : ℕ) {N : ℕ} {h : ℝ}
    (hh : 0 < h) (x y : Fin N → ℝ) :
    rawIntercept D p h x y =
      ∑ i, equivKernelWeight p (fun i => x i - D.center)
        (fun i => D.kernel ((x i - D.center) / h)) i *
          {i | |x i - D.center| ≤ h}.indicator y i := by
  unfold rawIntercept
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hi : |x i - D.center| ≤ h
  · rw [Set.indicator_of_mem (by exact hi)]
  · rw [equivKernelWeight_eq_zero_of_outside D p hh x hi, zero_mul, zero_mul]

/-- Fix [a kernel `K` that vanishes outside `[−1, 1]`, with evaluation point `x₀`](hyp:D), [a
positive bandwidth `h`](hyp:hh) and design points `x_1, …, x_N`, and let the responses be
independent with `Y_i` drawn from [a conditional outcome distribution](hyp:κ) at `x_i`. If
[this distribution has a finite second moment at every `x_i` with `|x_i − x₀| ≤ h`](hyp:hx),
then [the local-polynomial intercept `∑_i S_i Y_i` is square integrable](goal). -/
theorem rawIntercept_fibre_memLp (D : KernelDesign) (p : ℕ) {N : ℕ} {h : ℝ} (hh : 0 < h)
    (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] (x : Fin N → ℝ)
    (hx : ∀ i, |x i - D.center| ≤ h → MemLp (fun y : ℝ => y) 2 (κ (x i))) :
    MemLp (fun y => rawIntercept D p h x y) 2 (Measure.pi (fun i => κ (x i))) := by
  have hfun : (fun y => rawIntercept D p h x y) = fun y =>
      ∑ i, equivKernelWeight p (fun i => x i - D.center)
        (fun i => D.kernel ((x i - D.center) / h)) i *
          {i | |x i - D.center| ≤ h}.indicator y i :=
    funext (rawIntercept_eq_sum_indicator D p hh x)
  rw [hfun]
  refine memLp_finsetSum _ (fun i _ => MemLp.const_mul ?_ _)
  by_cases hi : |x i - D.center| ≤ h
  · have he : (fun y : Fin N → ℝ => {i | |x i - D.center| ≤ h}.indicator y i) =
        fun y => y i := funext fun y => Set.indicator_of_mem (by exact hi) y
    rw [he]
    exact (hx i hi).comp_measurePreserving (measurePreserving_eval _ i)
  · have he : (fun y : Fin N → ℝ => {i | |x i - D.center| ≤ h}.indicator y i) =
        fun _ => 0 := funext fun y => Set.indicator_of_notMem (by exact hi) y
    rw [he]
    exact memLp_const 0

/-- **Bias–variance bound on a fixed design.** Fix [a kernel `K` that vanishes outside `[−1,
1]`, with evaluation point `x₀`](hyp:D), [a positive bandwidth `h`](hyp:hh) and design
points `x_1, …, x_N`, and let the responses be independent with `Y_i` drawn from [a
conditional outcome distribution](hyp:κ) at `x_i`. If [at every `x_i` with `|x_i − x₀| ≤ h`
this distribution has a finite second moment, mean `m(x_i)` and variance at most
`σ²`](hyp:hx), then [the local-polynomial intercept `m̂ = ∑_i S_i Y_i` satisfies `E[(m̂ −
m(x₀))²] ≤ (∑_i S_i m(x_i) − m(x₀))² + σ² ∑_i S_i²`](goal).

Nothing is assumed about the responses at design points outside the kernel window. -/
theorem rawIntercept_fibre_mse_le (D : KernelDesign) (p : ℕ) {N : ℕ} {h : ℝ} (hh : 0 < h)
    (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] (m : ℝ → ℝ) (σ : ℝ) (x : Fin N → ℝ)
    (hx : ∀ i, |x i - D.center| ≤ h → MemLp (fun y : ℝ => y) 2 (κ (x i)) ∧
      (∫ y, y ∂κ (x i)) = m (x i) ∧ Var[fun y : ℝ => y; κ (x i)] ≤ σ ^ 2) :
    (∫ y, (rawIntercept D p h x y - m D.center) ^ 2
      ∂Measure.pi (fun i => κ (x i))) ≤
      (rawIntercept D p h x (fun i => m (x i)) - m D.center) ^ 2 +
      σ ^ 2 * ∑ i, (equivKernelWeight p (fun i => x i - D.center)
        (fun i => D.kernel ((x i - D.center) / h)) i) ^ 2 := by
  classical
  let μ := Measure.pi (fun i => κ (x i))
  let A : Set (Fin N) := {i | |x i - D.center| ≤ h}
  let S : Fin N → ℝ := equivKernelWeight p (fun i => x i - D.center)
    (fun i => D.kernel ((x i - D.center) / h))
  let F : (Fin N → ℝ) → ℝ := fun y => ∑ i, S i * A.indicator y i
  obtain ⟨hY, hnoise, hmean⟩ := fibre_response_moments κ m σ x A hx
  have hraw : ∀ y, rawIntercept D p h x y = F y := rawIntercept_eq_sum_indicator D p hh x
  have hfit : MemLp F 2 μ := memLp_finsetSum _ (fun i _ => (hY i).const_mul (S i))
  have hμfit : (∫ y, F y ∂μ) = F (fun i => m (x i)) := by
    change (∫ y, ∑ i, S i * A.indicator y i ∂μ) =
      ∑ i, S i * A.indicator (fun i => m (x i)) i
    rw [integral_finsetSum _ (fun i _ => ((hY i).integrable (by simp)).const_mul _)]
    simp_rw [integral_const_mul, hmean]
  have hvar := linearSmoother_variance_le hY hnoise
    (S := S) (V := ∑ i, S i ^ 2) le_rfl
  have herr : MemLp (fun y => F y - m D.center) 2 μ := hfit.sub (memLp_const _)
  have hid := variance_eq_sub herr
  rw [variance_sub_const hfit.aestronglyMeasurable,
    integral_sub (hfit.integrable (by simp)) (integrable_const _),
    integral_const, probReal_univ, one_smul, hμfit] at hid
  simp_rw [hraw]
  change (∫ y, (F y - m D.center) ^ 2 ∂μ) ≤ _
  change Var[F; μ] ≤ _ at hvar
  change Var[F; μ] =
    (∫ y, (F y - m D.center) ^ 2 ∂μ) -
      (F (fun i => m (x i)) - m D.center) ^ 2 at hid
  dsimp only [S] at hvar
  linarith

/-- **Conditional mean-squared error on a design with bounded leverage, dimension one.** Let
[the kernel `K` be nonnegative, at most `K_max` and zero outside `[−1, 1]`, with evaluation
point `x₀` and window radius `r`](hyp:D), and let [the regression function `m` be, on the
window `[x₀ − r, x₀ + r]`, `p = ⌈β⌉ − 1` times continuously differentiable with `p`-th
derivative Hölder of order `β − p` and constant `H`](hyp:hm). Take [a positive bandwidth
`h`](hyp:hh) [not exceeding `r`](hyp:hwindow), [a clipping level `M` with `|m(x₀)| ≤
M`](hyp:hM), and [design points `x_1, …, x_N`](hyp:x), and let the responses be independent
with `Y_i` drawn from [a conditional outcome distribution](hyp:κ) that [at each `x_i` in the
window `[x₀ − r, x₀ + r]` has a finite second moment, mean `m(x_i)` and variance at most
`σ²`](hyp:hnoise). If [the weighted design matrix `M_x` is invertible](hyp:hdet),
[`(M_x⁻¹)₀₀ ≤ 2 c_inv/(N h)`](hyp:hinv) and [`√((M_x)₀₀ (M_x⁻¹)₀₀) ≤ √(2 c_inv (c_top +
1))`](hyp:hlev), then [the degree-`p` intercept clipped to `[−M, M]` satisfies `E[(m̂ −
m(x₀))²] ≤ C_bias² h^(2β) + C_var/(N h)`, the expectation being over the responses](goal). -/
theorem localPoly_fibre_mse_of_designBounds (D : InteriorDesign) {β H h M σ : ℝ}
    {N : ℕ} {m : ℝ → ℝ} (hm : HolderRegression D.center D.radius β H m)
    (hh : 0 < h) (hwindow : h ≤ D.radius) (hM : |m D.center| ≤ M)
    (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] (x : Fin N → ℝ)
    (hnoise : ∀ i, |x i - D.center| ≤ D.radius → MemLp (fun y : ℝ => y) 2 (κ (x i)) ∧
      (∫ y, y ∂κ (x i)) = m (x i) ∧ Var[fun y : ℝ => y; κ (x i)] ≤ σ ^ 2)
    (hdet : IsUnit (designMatrix (holderDerivOrder β) (fun i => x i - D.center)
      (fun i => D.kernel ((x i - D.center) / h))).det)
    (hinv : (designMatrix (holderDerivOrder β) (fun i => x i - D.center)
      (fun i => D.kernel ((x i - D.center) / h)))⁻¹ 0 0 ≤
        2 * inverseConstant D (holderDerivOrder β) / ((N : ℝ) * h))
    (hlev : Real.sqrt
      ((designMatrix (holderDerivOrder β) (fun i => x i - D.center)
        (fun i => D.kernel ((x i - D.center) / h))) 0 0 *
      (designMatrix (holderDerivOrder β) (fun i => x i - D.center)
        (fun i => D.kernel ((x i - D.center) / h)))⁻¹ 0 0) ≤
        Real.sqrt (2 * inverseConstant D (holderDerivOrder β) *
          (topConstant D + 1))) :
    (∫ y, (clippedIntercept D (holderDerivOrder β) h M x y - m D.center) ^ 2
      ∂Measure.pi (fun i => κ (x i))) ≤
      biasConstant D β H ^ 2 * h ^ (2 * β) +
        varianceConstant D (holderDerivOrder β) σ / ((N : ℝ) * h) := by
  classical
  let p := holderDerivOrder β
  let μ := Measure.pi (fun i => κ (x i))
  let S := equivKernelWeight p (fun i => x i - D.center)
    (fun i => D.kernel ((x i - D.center) / h))
  have hnoise' : ∀ i, |x i - D.center| ≤ h → MemLp (fun y : ℝ => y) 2 (κ (x i)) ∧
      (∫ y, y ∂κ (x i)) = m (x i) ∧ Var[fun y : ℝ => y; κ (x i)] ≤ σ ^ 2 :=
    fun i hi => hnoise i (hi.trans hwindow)
  have hfit : MemLp (fun y => rawIntercept D p h x y) 2 μ :=
    rawIntercept_fibre_memLp D p hh κ x (fun i hi => (hnoise' i hi).1)
  have hraw : Integrable (fun y => (rawIntercept D p h x y - m D.center) ^ 2) μ :=
    (hfit.sub (memLp_const _)).integrable_sq
  have hmeas : Measurable (fun y => (clippedIntercept D p h M x y - m D.center) ^ 2) :=
    (((clippedIntercept_measurable D p N h M).comp
      (measurable_const.prodMk measurable_id)).sub_const _).pow_const 2
  have hle : ∀ y, (clippedIntercept D p h M x y - m D.center) ^ 2 ≤
      (rawIntercept D p h x y - m D.center) ^ 2 := fun y =>
    Causalean.Mathlib.Analysis.clipIcc_sub_sq_le (Set.mem_Icc.mpr (abs_le.mp hM)) _
  have hclip : Integrable (fun y => (clippedIntercept D p h M x y - m D.center) ^ 2) μ :=
    hraw.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hle y)
  have hcompare := integral_mono hclip hraw hle
  have hbias : |rawIntercept D p h x (fun i => m (x i)) - m D.center| ≤
      biasConstant D β H * h ^ β :=
    windowed_localPoly_bias D hm hh hwindow x hdet hlev
  have hB : 0 ≤ biasConstant D β H * h ^ β := by
    unfold biasConstant
    exact mul_nonneg
      (mul_nonneg (div_nonneg hm.2.1 (by positivity)) (Real.sqrt_nonneg _))
      (Real.rpow_nonneg hh.le _)
  have hbias_sq : (rawIntercept D p h x (fun i => m (x i)) - m D.center) ^ 2 ≤
      biasConstant D β H ^ 2 * h ^ (2 * β) := by
    have hb := (sq_le_sq₀ (abs_nonneg _) hB).2 hbias
    rw [sq_abs, mul_pow] at hb
    have hp : (h ^ β) ^ (2 : ℕ) = h ^ (2 * β) := by
      rw [mul_comm (2 : ℝ) β, Real.rpow_mul hh.le, Real.rpow_two]
    rwa [hp] at hb
  have hweights : (∑ i, S i ^ 2) ≤ D.kernelMax *
      (2 * inverseConstant D p / ((N : ℝ) * h)) :=
    (equivKernelWeight_sq_sum_le hdet (fun i => D.kernel_nonneg _)
      (fun i => D.kernel_upper _)).trans
        (mul_le_mul_of_nonneg_left hinv D.kernelMax_pos.le)
  have hvariance : σ ^ 2 * ∑ i, S i ^ 2 ≤
      varianceConstant D p σ / ((N : ℝ) * h) := by
    calc
      σ ^ 2 * ∑ i, S i ^ 2 ≤
          σ ^ 2 * (D.kernelMax * (2 * inverseConstant D p / ((N : ℝ) * h))) :=
        mul_le_mul_of_nonneg_left hweights (sq_nonneg σ)
      _ = varianceConstant D p σ / ((N : ℝ) * h) := by
        unfold varianceConstant
        ring
  exact hcompare.trans ((rawIntercept_fibre_mse_le D p hh κ m σ x hnoise').trans
    (add_le_add hbias_sq hvariance))

end Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate

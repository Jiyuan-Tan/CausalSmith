/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.Stat.Nonparametric.HistogramRegression.Mesh
public import Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate.Risk

/-!
# Pointwise rate of the clipped local-polynomial estimator, dimension one

With the bandwidth `h = N^(−1/(2β+1))` the squared-bias term `h^(2β)` and the variance term
`1/(N h)` both equal `N^(−2β/(2β+1))`, and the exponentially small design-failure term is at
most a constant times the same power. `localPoly_clipped_pointwise_rate` concludes that, once
`N ≥ max(1, ⌈r^(−(2β+1))⌉)` so that the bandwidth fits inside the window on which the design
density is bounded, the clipped local-polynomial intercept has mean-squared error at most an
explicit constant times `N^(−2β/(2β+1))`.

This is an upper bound, for the clipped estimator, in dimension one, at exactly this bandwidth.
-/

@[expose] public section

noncomputable section
namespace Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Analysis.HolderTaylor
open scoped ProbabilityTheory

/-- For [a smoothness `β`](hyp:β) and [a sample size `N`](hyp:N), the [balancing
bandwidth](goal) in dimension one is `h = N^(−1/(2β+1))`, the bandwidth at which the
squared-bias term `h^(2β)` and the variance term `1/(N h)` are equal. -/
def balancingBandwidth (β : ℝ) (N : ℕ) : ℝ :=
  HistogramRegression.optimizedBandwidth 1 β N

/-- For [a design whose density bounds hold on `[x₀ − r, x₀ + r]`](hyp:D) and [a smoothness
`β`](hyp:β), the [sample-size threshold](goal) is `max(1, ⌈r^(−(2β+1))⌉)`, the smallest
sample size from which the bandwidth `N^(−1/(2β+1))` is at most `r`. -/
def rateThreshold (D : InteriorDesign) (β : ℝ) : ℕ :=
  max 1 ⌈D.radius ^ (-(2 * β + 1))⌉₊

/-- [The balancing bandwidth for smoothness `β` and sample size `N` equals
`N^(−1/(2β+1))`](goal). -/
theorem balancingBandwidth_eq (β : ℝ) (N : ℕ) :
    balancingBandwidth β N = (N : ℝ) ^ (-(1 / (2 * β + 1))) := by
  simp [balancingBandwidth, HistogramRegression.optimizedBandwidth]

/-- For [a positive smoothness `β`](hyp:hβ) and [a positive sample size `N`](hyp:hN), [the
bandwidth `h = N^(−1/(2β+1))` satisfies `h^(2β) = N^(−2β/(2β+1))` and `1/(N h) =
N^(−2β/(2β+1))`](goal). -/
theorem balancingBandwidth_power_identities {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N) :
    balancingBandwidth β N ^ (2 * β) = (N : ℝ) ^ (-(2 * β / (2 * β + 1))) ∧
      1 / ((N : ℝ) * balancingBandwidth β N) = (N : ℝ) ^ (-(2 * β / (2 * β + 1))) := by
  simpa [balancingBandwidth] using
    HistogramRegression.optimized_power_identities 1 β N hβ hN

/-- Let [the design window be `[x₀ − r, x₀ + r]` with `r > 0`](hyp:D). For [a positive
smoothness `β`](hyp:hβ) and [a sample size `N ≥ max(1, ⌈r^(−(2β+1))⌉)`](hyp:hN), [`N` is
positive and the bandwidth `h = N^(−1/(2β+1))` satisfies `0 < h ≤ r`](goal). -/
theorem balancingBandwidth_spec (D : InteriorDesign) {β : ℝ} (hβ : 0 < β)
    {N : ℕ} (hN : rateThreshold D β ≤ N) :
    0 < N ∧ 0 < balancingBandwidth β N ∧ balancingBandwidth β N ≤ D.radius := by
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one
    ((le_max_left _ _).trans hN)
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hden : 0 < 2 * β + 1 := by linarith
  have hceil : ⌈D.radius ^ (-(2 * β + 1))⌉₊ ≤ N :=
    (le_max_right _ _).trans hN
  have hrN : D.radius ^ (-(2 * β + 1)) ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  refine ⟨hNpos, ?_, ?_⟩ <;> rw [balancingBandwidth_eq]
  · exact Real.rpow_pos_of_pos hNreal _
  · calc
      (N : ℝ) ^ (-(1 / (2 * β + 1))) ≤
          (D.radius ^ (-(2 * β + 1))) ^ (-(1 / (2 * β + 1))) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos D.radius_pos _) hrN
          (neg_nonpos.mpr (le_of_lt (one_div_pos.mpr hden)))
      _ = D.radius := by
        rw [← Real.rpow_mul D.radius_pos.le]
        have hexp : -(2 * β + 1) * -(1 / (2 * β + 1)) = 1 := by
          field_simp
        rw [hexp, Real.rpow_one]

/-- Let [the design density lie between `f_min > 0` and `f_max` near the evaluation point, and
the kernel be measurable, nonnegative, bounded, zero outside `[−1, 1]` and bounded below on
`[−Δ, Δ]`](hyp:D). For [a positive smoothness `β`](hyp:hβ) with `p = ⌈β⌉ − 1`, and [a
positive sample size `N`](hyp:hN), [at the bandwidth `h = N^(−1/(2β+1))` the failure bound
satisfies `2 (p+1)² exp(−c₀ N h) ≤ (2 (p+1)² / c₀) · N^(−2β/(2β+1))`, where `c₀ > 0` is the
Bernstein exponent at the design tolerance](goal).

The proof uses `exp(−s) ≤ 1/s` for `s > 0`, so the constant is conservative. -/
theorem balancing_failureBound_le (D : InteriorDesign) {β : ℝ} (hβ : 0 < β)
    {N : ℕ} (hN : 0 < N) :
    failureBound D (holderDerivOrder β) N (balancingBandwidth β N)
      (designTolerance D (holderDerivOrder β)) ≤
    (2 * (holderDerivOrder β + 1 : ℝ) ^ 2 /
      tailExponent D (designTolerance D (holderDerivOrder β))) *
      (N : ℝ) ^ (-(2 * β / (2 * β + 1))) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  let a := tailExponent D (designTolerance D (holderDerivOrder β))
  have ha : 0 < a := tailExponent_pos D (designTolerance_spec D _).1
  have hs : 0 < (N : ℝ) * balancingBandwidth β N := by
    rw [balancingBandwidth_eq]
    exact mul_pos hNreal (Real.rpow_pos_of_pos hNreal _)
  have hrecip := (balancingBandwidth_power_identities hβ hN).2
  have hexp : Real.exp (-((N : ℝ) * balancingBandwidth β N * a)) ≤
      1 / ((N : ℝ) * balancingBandwidth β N * a) := by
    rw [Real.exp_neg, ← one_div]
    apply one_div_le_one_div_of_le (mul_pos hs ha)
    linarith [Real.add_one_le_exp ((N : ℝ) * balancingBandwidth β N * a)]
  unfold failureBound
  change 2 * (holderDerivOrder β + 1 : ℝ) ^ 2 *
      Real.exp (-(N : ℝ) * balancingBandwidth β N * a) ≤
    (2 * (holderDerivOrder β + 1 : ℝ) ^ 2 / a) *
      (N : ℝ) ^ (-(2 * β / (2 * β + 1)))
  rw [show -(N : ℝ) * balancingBandwidth β N * a =
    -((N : ℝ) * balancingBandwidth β N * a) by ring]
  calc
    _ ≤ 2 * (holderDerivOrder β + 1 : ℝ) ^ 2 *
        (1 / ((N : ℝ) * balancingBandwidth β N * a)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = (2 * (holderDerivOrder β + 1 : ℝ) ^ 2 / a) *
        (1 / ((N : ℝ) * balancingBandwidth β N)) := by ring
    _ = _ := by rw [hrecip]

/-- For [a design with density bounds `f_min ≤ f_max` near the evaluation point and a kernel
bounded above and, on `[−Δ, Δ]`, below](hyp:D), [a smoothness `β`](hyp:β), [a Hölder
constant `H`](hyp:H), [a clipping level `M`](hyp:M) and [a noise scale `σ`](hyp:σ), the
[pointwise rate constant](goal) is `C = C_bias² + C_var + 16 M² (p+1)² / c₀`, where `p = ⌈β⌉
− 1`, `C_bias` and `C_var` are the bias and variance constants, and `c₀` is the Bernstein
exponent at the design tolerance. -/
def pointwiseRateConstant (D : InteriorDesign) (β H M σ : ℝ) : ℝ :=
  biasConstant D β H ^ 2 + varianceConstant D (holderDerivOrder β) σ +
    16 * M ^ 2 * (holderDerivOrder β + 1 : ℝ) ^ 2 /
      tailExponent D (designTolerance D (holderDerivOrder β))

/-- **Pointwise rate `N^(−2β/(2β+1))` for the clipped local-polynomial estimator at an interior
point, dimension one.** Let [the design density lie between positive constants `f_min ≤
f_max` on an interval `[x₀ − r, x₀ + r]`, and let the kernel `K` be measurable, nonnegative,
at most `K_max`, zero outside `[−1, 1]` and at least `K_min > 0` on `[−Δ, Δ]`](hyp:D).
Suppose [for some `β > 0` and `p = ⌈β⌉ − 1` the regression function `m` is, on that
interval, `p` times continuously differentiable with `p`-th derivative Hölder of order `β −
p` and constant `H`](hyp:hm), [the sample size satisfies `N ≥ max(1,
⌈r^(−(2β+1))⌉)`](hyp:hN), and [the clipping level `M` satisfies `|m(x₀)| ≤ M`](hyp:hM). Let
`(X_i, Y_i)`, `i = 1, …, N`, be independent pairs with `X_i` drawn from the design density
and `Y_i` drawn, given `X_i`, from [a conditional outcome distribution](hyp:κ) that [at
almost every design point `x` in that interval has a finite second moment, mean `m(x)` and
variance at most `σ²`](hyp:hnoise). Then [the degree-`p` kernel-weighted least-squares
intercept at `x₀` with bandwidth `h = N^(−1/(2β+1))` (taken to be zero when the weighted
design matrix is singular), clipped to `[−M, M]`, satisfies `E[(m̂(x₀) − m(x₀))²] ≤ C ·
N^(−2β/(2β+1))` with `C = C_bias² + C_var + 16 M² (p+1)² / c₀`, an explicit function of
`f_min`, `f_max`, `K_min`, `K_max`, `Δ`, the kernel moments, `p`, `H`, `σ` and `M` that does
not depend on `N`](goal).

Nothing is assumed about the regression function or the conditional response distribution
outside `[x₀ − r, x₀ + r]`. This is an upper bound only, for the clipped estimator in
dimension one with the bandwidth fixed at exactly `N^(−1/(2β+1))`. The exponent is the one
in Stone (1982) and in Tsybakov (2009), Theorem 1.7 (fixed design) and Fan and Gijbels
(1996), Theorem 3.1. -/
theorem localPoly_clipped_pointwise_rate (D : InteriorDesign) {β H M σ : ℝ}
    {N : ℕ} {m : ℝ → ℝ} (hm : HolderRegression D.center D.radius β H m)
    (hN : rateThreshold D β ≤ N) (hM : |m D.center| ≤ M)
    (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    (hnoise : ∀ᵐ x ∂D.law, |x - D.center| ≤ D.radius → MemLp (fun y : ℝ => y) 2 (κ x) ∧
      (∫ y, y ∂κ x) = m x ∧ Var[fun y : ℝ => y; κ x] ≤ σ ^ 2) :
    (∫ z : Fin N → ℝ × ℝ,
      (clippedIntercept D (holderDerivOrder β) (balancingBandwidth β N) M
        (fun i => (z i).1) (fun i => (z i).2) - m D.center) ^ 2
      ∂Measure.pi (fun _ : Fin N => D.law ⊗ₘ κ)) ≤
      pointwiseRateConstant D β H M σ * (N : ℝ) ^ (-(2 * β / (2 * β + 1))) := by
  obtain ⟨hNpos, hbandpos, hwindow⟩ := balancingBandwidth_spec D hm.1 hN
  obtain ⟨hbiasPower, hinvEffective⟩ := balancingBandwidth_power_identities hm.1 hNpos
  have hrisk := localPoly_clipped_mse_unconditional D hm hNpos hbandpos hwindow
    hM κ hnoise
  rw [hbiasPower, show
    varianceConstant D (holderDerivOrder β) σ /
        ((N : ℝ) * balancingBandwidth β N) =
      varianceConstant D (holderDerivOrder β) σ *
        (1 / ((N : ℝ) * balancingBandwidth β N)) by ring,
    hinvEffective] at hrisk
  have htail := mul_le_mul_of_nonneg_left
    (balancing_failureBound_le D hm.1 hNpos)
    (by positivity : 0 ≤ 8 * M ^ 2)
  calc
    _ ≤ biasConstant D β H ^ 2 * (N : ℝ) ^ (-(2 * β / (2 * β + 1))) +
        varianceConstant D (holderDerivOrder β) σ *
          (N : ℝ) ^ (-(2 * β / (2 * β + 1))) +
        8 * M ^ 2 * failureBound D (holderDerivOrder β) N (balancingBandwidth β N)
          (designTolerance D (holderDerivOrder β)) := hrisk
    _ ≤ biasConstant D β H ^ 2 * (N : ℝ) ^ (-(2 * β / (2 * β + 1))) +
        varianceConstant D (holderDerivOrder β) σ *
          (N : ℝ) ^ (-(2 * β / (2 * β + 1))) +
        8 * M ^ 2 * ((2 * (holderDerivOrder β + 1 : ℝ) ^ 2 /
          tailExponent D (designTolerance D (holderDerivOrder β))) *
          (N : ℝ) ^ (-(2 * β / (2 * β + 1)))) := add_le_add le_rfl htail
    _ = _ := by unfold pointwiseRateConstant; ring

/-- **Pointwise rate `N^(−2β/(2β+1))` of the clipped local-polynomial estimator for a globally
smooth regression function, dimension one.** Let [the design density lie between positive
constants `f_min ≤ f_max` on an interval `[x₀ − r, x₀ + r]`, and let the kernel `K` be
measurable, nonnegative, at most `K_max`, zero outside `[−1, 1]` and at least `K_min > 0` on
`[−Δ, Δ]`](hyp:D). Suppose [`β > 0`](hyp:hβ), [`H ≥ 0`](hyp:hH), [the regression function
`m` is `p = ⌈β⌉ − 1` times continuously differentiable on the whole real line](hyp:hm), and
[its `p`-th derivative satisfies `|m⁽ᵖ⁾(x) − m⁽ᵖ⁾(y)| ≤ H |x − y|^(β − p)` for all `x, y` in
that interval](hyp:hb). Suppose also [the sample size satisfies `N ≥ max(1,
⌈r^(−(2β+1))⌉)`](hyp:hN) and [the clipping level `M` satisfies `|m(x₀)| ≤ M`](hyp:hM). Let
`(X_i, Y_i)`, `i = 1, …, N`, be independent pairs with `X_i` drawn from the design density
and `Y_i` drawn, given `X_i`, from [a conditional outcome distribution](hyp:κ) that [at
almost every design point `x` has a finite second moment, mean `m(x)` and variance at most
`σ²`](hyp:hnoise). Then [the degree-`p` kernel-weighted least-squares intercept at `x₀` with
bandwidth `h = N^(−1/(2β+1))` (taken to be zero when the weighted design matrix is
singular), clipped to `[−M, M]`, satisfies `E[(m̂(x₀) − m(x₀))²] ≤ C · N^(−2β/(2β+1))` with
the same constant `C = C_bias² + C_var + 16 M² (p+1)² / c₀` as in the version with
assumptions on the interval only](goal).

This is the special case of the pointwise rate whose smoothness and noise conditions are
imposed only on `[x₀ − r, x₀ + r]`. It is an upper bound for the clipped estimator. -/
theorem localPoly_clipped_pointwise_rate_of_contDiff (D : InteriorDesign) {β H M σ : ℝ}
    {N : ℕ} {m : ℝ → ℝ}
    (hβ : 0 < β) (hH : 0 ≤ H) (hm : ContDiff ℝ (holderDerivOrder β) m)
    (hb : ∀ x ∈ Set.Icc (D.center - D.radius) (D.center + D.radius),
      ∀ y ∈ Set.Icc (D.center - D.radius) (D.center + D.radius),
        |iteratedDeriv (holderDerivOrder β) m x - iteratedDeriv (holderDerivOrder β) m y|
          ≤ H * |x - y| ^ (β - (holderDerivOrder β : ℝ)))
    (hN : rateThreshold D β ≤ N) (hM : |m D.center| ≤ M)
    (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    (hnoise : ∀ᵐ x ∂D.law, MemLp (fun y : ℝ => y) 2 (κ x) ∧
      (∫ y, y ∂κ x) = m x ∧ Var[fun y : ℝ => y; κ x] ≤ σ ^ 2) :
    (∫ z : Fin N → ℝ × ℝ,
      (clippedIntercept D (holderDerivOrder β) (balancingBandwidth β N) M
        (fun i => (z i).1) (fun i => (z i).2) - m D.center) ^ 2
      ∂Measure.pi (fun _ : Fin N => D.law ⊗ₘ κ)) ≤
      pointwiseRateConstant D β H M σ * (N : ℝ) ^ (-(2 * β / (2 * β + 1))) :=
  localPoly_clipped_pointwise_rate D
    (HolderRegression.of_contDiff D.center D.radius D.radius_pos hβ hH hm hb)
    hN hM κ (hnoise.mono fun _ hx _ => hx)

end Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate

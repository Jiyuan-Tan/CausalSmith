/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.Stat.Concentration.ConditionalBernstein.Disintegration
public import Causalean.Stat.Nonparametric.LocalPoly.EstimatorRisk.Unconditional
public import Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate.ConditionalRisk
public import Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate.GoodDesign
public import Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate.MomentConcentration
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Unconditional mean-squared error of the clipped local-polynomial estimator, dimension one

`localPoly_clipped_mse_unconditional`: at an interior point `x₀`, for independent pairs
`(X_i, Y_i)` whose design density is bounded above and below near `x₀`, a regression function in
a local Hölder class of smoothness `β`, and responses with conditional variance at most `σ²`,
the degree-`p` local-polynomial intercept (`p = ⌈β⌉ − 1`) clipped to `[−M, M]`, where
`|m(x₀)| ≤ M`, has mean-squared error at most
`C_bias² h^(2β) + C_var/(N h) + 16 M² (p+1)² exp(−c₀ N h)`.

The event that the empirical kernel moments are close to their expectations is constructed, not
assumed: on it the conditional mean-squared error is at most the first two terms, and its
complement has probability at most `2 (p+1)² exp(−c₀ N h)`. A bounded estimator's squared loss
is lifted from the event to the whole sample at the cost of `8 M²` times the probability of the
complement (`bounded_fibre_mse_lift`). The result is an upper bound for the clipped estimator;
neither the responses nor the regression function need be bounded.
-/

public section

namespace Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate

open MeasureTheory ProbabilityTheory Causalean.Stat Causalean.Stat.Nonparametric
open Causalean.Mathlib.Analysis.HolderTaylor
open scoped BigOperators ProbabilityTheory

/-- **From a good-design event to the unconditional mean-squared error.** Let the design `X`
have [a probability law](hyp:P) and the response `Y` be drawn, given `X`, from [a
conditional distribution](hyp:κ). Let [a measurable](hyp:hmeas) [estimator `θ̂(X,
Y)`](hyp:est) be [bounded by `M` in absolute value](hyp:hbound), let [the target `θ` satisfy
`|θ| ≤ M`](hyp:hθ), and let [`R ≥ 0`](hyp:hR). If on [a measurable set `G` of
designs](hyp:hG) [the conditional mean-squared error `E[(θ̂ − θ)² | X]` is at most `R` for
almost every design in `G`](hyp:hgood), then [`E[(θ̂ − θ)²] ≤ R + 8 M² · P(X ∉ G)`](goal). -/
theorem bounded_fibre_mse_lift {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure A) [IsProbabilityMeasure P] (κ : Kernel A B) [IsMarkovKernel κ]
    (est : A × B → ℝ) (hmeas : Measurable est) {G : Set A}
    (hG : MeasurableSet G) {θ M R : ℝ} (hθ : |θ| ≤ M) (hR : 0 ≤ R)
    (hbound : ∀ z, |est z| ≤ M)
    (hgood : ∀ᵐ x ∂P, x ∈ G → (∫ y, (est (x, y) - θ) ^ 2 ∂κ x) ≤ R) :
    (∫ z, (est z - θ) ^ 2 ∂(P ⊗ₘ κ)) ≤ R + 8 * M ^ 2 * P.real Gᶜ := by
  let loss : A × B → ℝ := fun z => (est z - θ) ^ 2
  have hloss : Measurable loss := (hmeas.sub_const θ).pow_const 2
  have hloss_bound : ∀ z, |loss z| ≤ 4 * M ^ 2 := by
    intro z
    have he := abs_le.mp (hbound z)
    have ht := abs_le.mp hθ
    have hM : 0 ≤ M := (abs_nonneg θ).trans hθ
    dsimp only [loss]
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (est z - θ + 2 * M),
      sq_nonneg (2 * M - (est z - θ)),
      mul_nonneg (show 0 ≤ 2 * M - (est z - θ) by linarith)
        (show 0 ≤ 2 * M + (est z - θ) by linarith)]
  have hloss_int : Integrable loss (P ⊗ₘ κ) :=
    (integrable_const (4 * M ^ 2)).mono' hloss.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hloss_bound z)
  let F : A → ℝ := fun x => ∫ y, loss (x, y) ∂κ x
  have hFmeas : StronglyMeasurable F := hloss.stronglyMeasurable.integral_kernel_prod_right'
  have hFnonneg : ∀ x, 0 ≤ F x := fun x => integral_nonneg (fun y => sq_nonneg _)
  have hFbound : ∀ x, |F x| ≤ 4 * M ^ 2 := by
    intro x
    have hb := norm_integral_le_of_norm_le_const
      (μ := κ x) (f := fun y => loss (x, y)) (C := 4 * M ^ 2)
      (Filter.Eventually.of_forall fun y => by
        simpa only [Real.norm_eq_abs] using hloss_bound (x, y))
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hb
  have hFint : Integrable F P :=
    (integrable_const (4 * M ^ 2)).mono' hFmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hFbound x)
  have hcond : ∀ᵐ x ∂P, x ∈ G → |(P[F | ‹MeasurableSpace A›]) x - 0| ≤ R := by
    rw [condExp_of_stronglyMeasurable le_rfl hFmeas hFint]
    filter_upwards [hgood] with x hx hxG
    simpa only [sub_zero, abs_of_nonneg (hFnonneg x)] using hx hxG
  have hb := estimatorBias_unconditional (μ := P) (m := ‹MeasurableSpace A›)
    (est := F) (θ := 0) (B := R) (M := 4 * M ^ 2)
    le_rfl hFint hFbound (by simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg M))
    hR hG hcond
  rw [Measure.integral_compProd hloss_int]
  change (∫ x, F x ∂P) ≤ _
  exact (le_abs_self _).trans (by
    simpa only [sub_zero, Measure.real,
      show (2 : ℝ) * (4 * M ^ 2) = 8 * M ^ 2 by ring] using hb)

/-- Let [the design law, kernel and evaluation point be given](hyp:D) and let the response be
drawn, given the design point, from [a conditional outcome distribution](hyp:κ). Then for
every degree, sample size, bandwidth, clipping level and target, [the expected squared error
of the clipped local-polynomial intercept over `N` independent pairs `(X_i, Y_i)` equals its
expected squared error when the `N` design points are drawn first, independently, and the
responses are then drawn independently given the design points](goal). -/
theorem clippedIntercept_iid_risk_eq (D : KernelDesign) (p N : ℕ) (h M θ : ℝ)
    (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] :
    (∫ z : Fin N → ℝ × ℝ,
      (clippedIntercept D p h M (fun i => (z i).1) (fun i => (z i).2) - θ) ^ 2
      ∂Measure.pi (fun _ : Fin N => D.law ⊗ₘ κ)) =
    ∫ z : (Fin N → ℝ) × (Fin N → ℝ),
      (clippedIntercept D p h M z.1 z.2 - θ) ^ 2
      ∂(Measure.pi (fun _ : Fin N => D.law) ⊗ₘ finProductKernel N κ) := by
  let := D.probability
  let split : (Fin N → ℝ × ℝ) → (Fin N → ℝ) × (Fin N → ℝ) :=
    fun z => (fun i => (z i).1, fun i => (z i).2)
  have hs : Measurable split := by fun_prop
  have hf : Measurable (fun z : (Fin N → ℝ) × (Fin N → ℝ) =>
      (clippedIntercept D p h M z.1 z.2 - θ) ^ 2) :=
    ((clippedIntercept_measurable D p N h M).sub_const θ).pow_const 2
  rw [← Causalean.Stat.Concentration.ConditionalBernstein.iid_joint_map_split N D.law κ]
  exact (integral_map hs.aemeasurable hf.aestronglyMeasurable).symm

/-- **Conditional mean-squared error on the moment event, dimension one.** Let [the design
density lie between `f_min > 0` and `f_max` on `[x₀ − r, x₀ + r]`, and the kernel `K` be
measurable, nonnegative, at most `K_max`, zero outside `[−1, 1]` and at least `K_min > 0` on
`[−Δ, Δ]`](hyp:D), and let [the regression function `m` be, on the window `[x₀ − r, x₀ +
r]`, `p = ⌈β⌉ − 1` times continuously differentiable with `p`-th derivative Hölder of order
`β − p` and constant `H`](hyp:hm). Take [a positive sample size `N`](hyp:hN), [a positive
bandwidth `h`](hyp:hh) [not exceeding `r`](hyp:hwindow), [a clipping level `M` with `|m(x₀)|
≤ M`](hyp:hM), and [design points `x_1, …, x_N`](hyp:x) for which [every empirical kernel
moment is within the design tolerance of its expectation](hyp:hx). Let the responses be
independent with `Y_i` drawn from [a conditional outcome distribution](hyp:κ) that [at each
`x_i` in the window `[x₀ − r, x₀ + r]` has a finite second moment, mean `m(x_i)` and
variance at most `σ²`](hyp:hnoise). Then [the degree-`p` intercept clipped to `[−M, M]`
satisfies `E[(m̂ − m(x₀))²] ≤ C_bias² h^(2β) + C_var/(N h)`, the expectation being over the
responses](goal). -/
theorem localPoly_fibre_mse_on_momentEvent (D : InteriorDesign) {β H h M σ : ℝ}
    {N : ℕ} {m : ℝ → ℝ} (hm : HolderRegression D.center D.radius β H m)
    (hN : 0 < N) (hh : 0 < h) (hwindow : h ≤ D.radius) (hM : |m D.center| ≤ M)
    (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] (x : Fin N → ℝ)
    (hnoise : ∀ i, |x i - D.center| ≤ D.radius → MemLp (fun y : ℝ => y) 2 (κ (x i)) ∧
      (∫ y, y ∂κ (x i)) = m (x i) ∧ Var[fun y : ℝ => y; κ (x i)] ≤ σ ^ 2)
    (hx : x ∈ momentEvent D (holderDerivOrder β) h N
      (designTolerance D (holderDerivOrder β))) :
    (∫ y, (clippedIntercept D (holderDerivOrder β) h M x y - m D.center) ^ 2
      ∂Measure.pi (fun i => κ (x i))) ≤
      biasConstant D β H ^ 2 * h ^ (2 * β) +
        varianceConstant D (holderDerivOrder β) σ / ((N : ℝ) * h) := by
  obtain ⟨hdet, hinv, hlev⟩ := localPoly_leverage_on_momentEvent D
    (holderDerivOrder β) hN hh hwindow x hx
  exact localPoly_fibre_mse_of_designBounds D hm hh hwindow hM κ x hnoise
    hdet hinv hlev

/-- **Unconditional mean-squared error of the clipped local-polynomial estimator at an interior
point, dimension one.** Let [the design density lie between positive constants `f_min ≤
f_max` on an interval `[x₀ − r, x₀ + r]`, and let the kernel `K` be measurable, nonnegative,
at most `K_max`, zero outside `[−1, 1]` and at least `K_min > 0` on `[−Δ, Δ]`](hyp:D).
Suppose [for some `β > 0` and `p = ⌈β⌉ − 1` the regression function `m` is, on that
interval, `p` times continuously differentiable with `p`-th derivative Hölder of order `β −
p` and constant `H`](hyp:hm), [the sample size `N` is positive](hyp:hN), [the bandwidth `h`
is positive](hyp:hh) and [at most `r`](hyp:hwindow), and [the clipping level `M` satisfies
`|m(x₀)| ≤ M`](hyp:hM). Let `(X_i, Y_i)`, `i = 1, …, N`, be independent pairs with `X_i`
drawn from the design density and `Y_i` drawn, given `X_i`, from [a conditional outcome
distribution](hyp:κ) that [at almost every design point `x` in that interval has a finite
second moment, mean `m(x)` and variance at most `σ²`](hyp:hnoise). Then [the degree-`p`
kernel-weighted least-squares intercept at `x₀` (taken to be zero when the weighted design
matrix is singular), clipped to `[−M, M]`, satisfies `E[(m̂(x₀) − m(x₀))²] ≤ C_bias² h^(2β)
+ C_var/(N h) + 16 M² (p+1)² exp(−c₀ N h)`, where `C_bias`, `C_var` and `c₀ > 0` are
explicit functions of `f_min`, `f_max`, `K_min`, `K_max`, `Δ`, the kernel moments, `p`, `H`
and `σ` that do not depend on `N` or `h`](goal).

No condition on the realized design is assumed: the event that the empirical kernel moments
are close to their expectations is constructed in the proof, and the last term pays for the
designs on which it fails. Only the interval `[x₀ − r, x₀ + r]` matters: nothing is assumed
about the regression function, or about the conditional distribution of the response, at
design points outside it. In particular the statement covers a regression function that is
smooth on the whole line and responses whose conditional moment conditions hold at almost
every design point. The clipping level is a user-supplied bound on the target `m(x₀)`;
neither the responses nor the regression function need be bounded. This is an upper bound
for the clipped estimator in dimension one. The classical fixed-design counterpart is
Tsybakov (2009), Proposition 1.13. -/
theorem localPoly_clipped_mse_unconditional (D : InteriorDesign) {β H h M σ : ℝ}
    {N : ℕ} {m : ℝ → ℝ} (hm : HolderRegression D.center D.radius β H m)
    (hN : 0 < N) (hh : 0 < h) (hwindow : h ≤ D.radius) (hM : |m D.center| ≤ M)
    (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    (hnoise : ∀ᵐ x ∂D.law, |x - D.center| ≤ D.radius → MemLp (fun y : ℝ => y) 2 (κ x) ∧
      (∫ y, y ∂κ x) = m x ∧ Var[fun y : ℝ => y; κ x] ≤ σ ^ 2) :
    (∫ z : Fin N → ℝ × ℝ,
      (clippedIntercept D (holderDerivOrder β) h M
        (fun i => (z i).1) (fun i => (z i).2) - m D.center) ^ 2
      ∂Measure.pi (fun _ : Fin N => D.law ⊗ₘ κ)) ≤
      biasConstant D β H ^ 2 * h ^ (2 * β) +
        varianceConstant D (holderDerivOrder β) σ / ((N : ℝ) * h) +
        8 * M ^ 2 * failureBound D (holderDerivOrder β) N h
          (designTolerance D (holderDerivOrder β)) := by
  let := D.probability
  have hMnonneg : 0 ≤ M := (abs_nonneg _).trans hM
  have hinv : 0 < inverseConstant D (holderDerivOrder β) :=
    (designConstants_positive D (holderDerivOrder β)).2.1
  have hR : 0 ≤ biasConstant D β H ^ 2 * h ^ (2 * β) +
      varianceConstant D (holderDerivOrder β) σ / ((N : ℝ) * h) := by
    unfold varianceConstant
    have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
    have hkernel := D.kernelMax_pos
    positivity
  have hgood : ∀ᵐ x ∂Measure.pi (fun _ : Fin N => D.law),
      x ∈ momentEvent D (holderDerivOrder β) h N
        (designTolerance D (holderDerivOrder β)) →
      (∫ y, (clippedIntercept D (holderDerivOrder β) h M x y - m D.center) ^ 2
        ∂Causalean.Stat.finProductKernel N κ x) ≤
      biasConstant D β H ^ 2 * h ^ (2 * β) +
        varianceConstant D (holderDerivOrder β) σ / ((N : ℝ) * h) := by
    have hall : ∀ᵐ x ∂Measure.pi (fun _ : Fin N => D.law), ∀ i,
        |x i - D.center| ≤ D.radius → MemLp (fun y : ℝ => y) 2 (κ (x i)) ∧
        (∫ y, y ∂κ (x i)) = m (x i) ∧ Var[fun y : ℝ => y; κ (x i)] ≤ σ ^ 2 :=
      ae_all_iff.mpr (fun i =>
        (measurePreserving_eval (fun _ : Fin N => D.law) i).quasiMeasurePreserving.ae hnoise)
    filter_upwards [hall] with x hx hxG
    rw [Causalean.Stat.finProductKernel_apply]
    exact localPoly_fibre_mse_on_momentEvent D hm hN hh hwindow hM κ x hx hxG
  have hlift := bounded_fibre_mse_lift
    (Measure.pi (fun _ : Fin N => D.law)) (Causalean.Stat.finProductKernel N κ)
    (fun z => clippedIntercept D (holderDerivOrder β) h M z.1 z.2)
    (clippedIntercept_measurable D (holderDerivOrder β) N h M)
    (momentEvent_measurable D (holderDerivOrder β) N h
      (designTolerance D (holderDerivOrder β))) hM hR
    (fun z => Causalean.Mathlib.Analysis.abs_clipIcc_neg_le hMnonneg _)
    hgood
  rw [clippedIntercept_iid_risk_eq D (holderDerivOrder β) N h M (m D.center) κ]
  exact hlift.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left
      (localPoly_moment_simultaneous_probability D (holderDerivOrder β) N hN hh
        hwindow (designTolerance_spec D (holderDerivOrder β)).1)
      (by positivity : 0 ≤ 8 * M ^ 2)))

/-- **Unconditional mean-squared error of the clipped local-polynomial estimator for a globally
smooth regression function, dimension one.** Let [the design density lie between positive
constants `f_min ≤ f_max` on an interval `[x₀ − r, x₀ + r]`, and let the kernel `K` be
measurable, nonnegative, at most `K_max`, zero outside `[−1, 1]` and at least `K_min > 0` on
`[−Δ, Δ]`](hyp:D). Suppose [`β > 0`](hyp:hβ), [`H ≥ 0`](hyp:hH), [the regression function
`m` is `p = ⌈β⌉ − 1` times continuously differentiable on the whole real line](hyp:hm), and
[its `p`-th derivative satisfies `|m⁽ᵖ⁾(x) − m⁽ᵖ⁾(y)| ≤ H |x − y|^(β − p)` for all `x, y` in
that interval](hyp:hb). Suppose also [the sample size `N` is positive](hyp:hN), [the
bandwidth `h` is positive](hyp:hh) and [at most `r`](hyp:hwindow), and [the clipping level
`M` satisfies `|m(x₀)| ≤ M`](hyp:hM). Let `(X_i, Y_i)`, `i = 1, …, N`, be independent pairs
with `X_i` drawn from the design density and `Y_i` drawn, given `X_i`, from [a conditional
outcome distribution](hyp:κ) that [at almost every design point `x` has a finite second
moment, mean `m(x)` and variance at most `σ²`](hyp:hnoise). Then [the degree-`p`
kernel-weighted least-squares intercept at `x₀` (taken to be zero when the weighted design
matrix is singular), clipped to `[−M, M]`, satisfies `E[(m̂(x₀) − m(x₀))²] ≤ C_bias² h^(2β)
+ C_var/(N h) + 16 M² (p+1)² exp(−c₀ N h)`, with the same explicit constants as in the
version with assumptions on the interval only](goal).

This is the special case of the unconditional bound whose smoothness and noise conditions
are imposed only on `[x₀ − r, x₀ + r]`: a function smooth on the whole line is smooth on the
interval, and a condition holding at almost every design point holds at almost every design
point of the interval. It is an upper bound for the clipped estimator. -/
theorem localPoly_clipped_mse_unconditional_of_contDiff (D : InteriorDesign) {β H h M σ : ℝ}
    {N : ℕ} {m : ℝ → ℝ}
    (hβ : 0 < β) (hH : 0 ≤ H) (hm : ContDiff ℝ (holderDerivOrder β) m)
    (hb : ∀ x ∈ Set.Icc (D.center - D.radius) (D.center + D.radius),
      ∀ y ∈ Set.Icc (D.center - D.radius) (D.center + D.radius),
        |iteratedDeriv (holderDerivOrder β) m x - iteratedDeriv (holderDerivOrder β) m y|
          ≤ H * |x - y| ^ (β - (holderDerivOrder β : ℝ)))
    (hN : 0 < N) (hh : 0 < h) (hwindow : h ≤ D.radius) (hM : |m D.center| ≤ M)
    (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    (hnoise : ∀ᵐ x ∂D.law, MemLp (fun y : ℝ => y) 2 (κ x) ∧
      (∫ y, y ∂κ x) = m x ∧ Var[fun y : ℝ => y; κ x] ≤ σ ^ 2) :
    (∫ z : Fin N → ℝ × ℝ,
      (clippedIntercept D (holderDerivOrder β) h M
        (fun i => (z i).1) (fun i => (z i).2) - m D.center) ^ 2
      ∂Measure.pi (fun _ : Fin N => D.law ⊗ₘ κ)) ≤
      biasConstant D β H ^ 2 * h ^ (2 * β) +
        varianceConstant D (holderDerivOrder β) σ / ((N : ℝ) * h) +
        8 * M ^ 2 * failureBound D (holderDerivOrder β) N h
          (designTolerance D (holderDerivOrder β)) :=
  localPoly_clipped_mse_unconditional D
    (HolderRegression.of_contDiff D.center D.radius D.radius_pos hβ hH hm hb)
    hN hh hwindow hM κ (hnoise.mono fun _ hx _ => hx)

end Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate

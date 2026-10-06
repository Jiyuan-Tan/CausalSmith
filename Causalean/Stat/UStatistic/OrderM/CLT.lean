module
public import Causalean.Stat.UStatistic.OrderM.Hajek
public import Causalean.Stat.UStatistic.OrderM.RemainderNegligible

/-!
# Fixed-order U-statistic CLTs

This module states the asymptotic-normality interface for fixed-order
U-statistics. `uStatisticOrder_clt` converts a centered, square-integrable
summed first projection and an explicit higher-order remainder-negligibility
hypothesis into the Gaussian limit of the `√n`-rescaled statistic.

The wrapper `uStatisticOrder_clt_of_explicit_conditions` discharges the
negligibility hypothesis from the stated residual and fixed-section regularity
conditions via `orderDegenerateNegligible_of_residual`. Together these
declarations are the public CLT endpoint for the `OrderM` U-statistic
development.
-/

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X} [IsProbabilityMeasure μ]

/-- **Fixed-order U-statistic CLT.** For an i.i.d. sample `S` and an order-`m` kernel `h`,
write `ψ` for the summed coordinatewise first Hoeffding projection of `h`. If `ψ` is
[measurable](hyp:hψ_meas), [has population mean zero](hyp:hψ_mean), and
[is square-integrable](hyp:hψ_sq), if [the higher-order Hájek remainder of the order-`m`
U-statistic is negligible at the `√n` scale](hyp:hneg), and if [the `√n`-rescaled
U-statistic is almost-everywhere measurable at every sample size](hyp:hθn_meas), then
[the `√n`-rescaled U-statistic converges in distribution to the centered Gaussian law with
variance `∫ψ²dP`](goal). -/
theorem uStatisticOrder_clt (S : IIDSample Ω X μ P)
    {m : ℕ} [NeZero m] (h : (Fin m → X) → ℝ)
    (hψ_meas : Measurable (uInfluenceOrder h P))
    (hψ_mean : ∫ x, uInfluenceOrder h P x ∂P = 0)
    (hψ_sq : Integrable (fun x => (uInfluenceOrder h P x) ^ 2) P)
    (hneg : OrderDegenerateNegligible S h)
    (hθn_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinear.rescaledEstimator (uStatisticOrder S h) (uMeanOrder h P)
        (fun r => Finset.range r) n) μ) :
    Tendsto_dist
      (IsAsymLinear.rescaledEstimator (uStatisticOrder S h) (uMeanOrder h P)
        (fun r => Finset.range r))
      (gaussianMeasure 0 (∫ x, (uInfluenceOrder h P x) ^ 2 ∂P))
      μ
      hθn_meas := by
  have hAL : IsAsymLinear (uStatisticOrder S h) (uMeanOrder h P)
      (uInfluenceOrder h P) S (fun r => Finset.range r) :=
    uStatisticOrder_isAsymLinear S h hψ_mean hψ_sq hneg
  exact hAL.tendsto_normal hψ_meas hθn_meas

/-- **Fixed-order U-statistic CLT from explicit conditions.** For [an i.i.d.
sample](hyp:S) and [an order-`m` kernel](hyp:m,h), write `g` for the higher-order Hájek
residual and `ψ` for the summed coordinatewise first Hoeffding projection. If `g` is
[measurable](hyp:hmeas) and [square-integrable under the `m`-fold product law](hyp:hL2),
if for every coordinate [integrating `h` over the remaining `m − 1` coordinates yields an
integrable function of that coordinate](hyp:hslice_int) [with the same population mean
`uMeanOrder h P` in every coordinate](hyp:hmean) and [`h` remains integrable in the
remaining coordinates for every fixed value of that coordinate](hyp:hrow), and if `ψ` is
[measurable](hyp:hψ_meas) and [square-integrable](hyp:hψ_sq), and
[the `√n`-rescaled U-statistic is almost-everywhere measurable at every sample
size](hyp:hθn_meas), then [the `√n`-rescaled order-`m` U-statistic converges in
distribution to the centered Gaussian law with variance `∫ψ²dP`](goal).

This composes `uStatisticOrder_clt` with `orderDegenerateNegligible_of_residual`, so no
negligibility or separate influence-centering hypothesis is required from the caller. -/
theorem uStatisticOrder_clt_of_explicit_conditions
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {P : Measure X} [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P) {m : ℕ} [NeZero m] (h : (Fin m → X) → ℝ)
    (hmeas : Measurable (uDegenOrder h P))
    (hL2 : Integrable (fun z => (uDegenOrder h P z) ^ 2)
      (Measure.pi fun _ : Fin m => P))
    (hslice_int : ∀ j : Fin m, Integrable
      (fun x => ∫ tail : ({k : Fin m // k ≠ j}) → X,
        h (insertCoord j x tail) ∂(Measure.pi fun _ : {k : Fin m // k ≠ j} => P)) P)
    (hmean : ∀ j : Fin m,
      ∫ x, (∫ tail : ({k : Fin m // k ≠ j}) → X,
        h (insertCoord j x tail) ∂(Measure.pi fun _ : {k : Fin m // k ≠ j} => P)) ∂P
        = uMeanOrder h P)
    (hrow : ∀ (j : Fin m) (x : X),
      Integrable (fun tail : ({k : Fin m // k ≠ j}) → X =>
        h (insertCoord j x tail))
        (Measure.pi fun _ : {k : Fin m // k ≠ j} => P))
    (hψ_meas : Measurable (uInfluenceOrder h P))
    (hψ_sq : Integrable (fun x => (uInfluenceOrder h P x) ^ 2) P)
    (hθn_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinear.rescaledEstimator (uStatisticOrder S h) (uMeanOrder h P)
        (fun r => Finset.range r) n) μ) :
    Tendsto_dist
      (IsAsymLinear.rescaledEstimator (uStatisticOrder S h) (uMeanOrder h P)
        (fun r => Finset.range r))
      (gaussianMeasure 0 (∫ x, (uInfluenceOrder h P x) ^ 2 ∂P))
      μ
      hθn_meas := by
  letI : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  have hproj_int : ∀ j : Fin m, Integrable (uProjOrderAt j h P) P :=
    fun j => uProjOrderAt_integrable j (hslice_int j)
  have hproj_zero : ∀ j : Fin m, ∫ x, uProjOrderAt j h P x ∂P = 0 :=
    fun j => uProjOrderAt_integral_eq_zero j (hslice_int j) (hmean j)
  have hψ_mean : ∫ x, uInfluenceOrder h P x ∂P = 0 :=
    uInfluenceOrder_integral_eq_zero hproj_int hproj_zero
  have hneg : OrderDegenerateNegligible S h :=
    orderDegenerateNegligible_of_residual S h hmeas hL2 hslice_int hmean hrow
  exact uStatisticOrder_clt S h hψ_meas hψ_mean hψ_sq hneg hθn_meas

end Causalean.Stat

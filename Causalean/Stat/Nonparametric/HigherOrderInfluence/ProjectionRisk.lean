/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Nonparametric.HigherOrderInfluence.DegenerateUStatVariance
public import Causalean.Stat.Nonparametric.HigherOrderInfluence.ProductRemainder
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Projection-kernel risk-bound algebra

Algebraic risk bounds for higher-order influence function (HOIF) calculations, combining
assumed first-order variance and projection bias with proved degenerate U-statistic variance
and finite-product remainder bounds.

Given a risk decomposition with a `J`-dimensional projection space and bandwidth `h`, this module
combines its four component bounds:

* **localized first-order variance** `V₁ = O((nh)^{-1})` — an assumed stochastic term;
* **projection product bias²** `B² = O(J^{-4s/d})` — the squared series/sieve approximation error of
  the `J`-term projection (`Causalean.Stat.Nonparametric.SeriesSieve`);
* **degenerate U-statistic variance** `V₂ = Var[Uₙ] ≤ 4C·J/(nh)²` — the second-order projected
  stochastic term, controlled by `HigherOrderInfluence.DegenerateUStatVariance` from the supplied localized
  L²-energy hypothesis `ζ ≤ C·J/h²` (the sibling `HigherOrderInfluence.ProjectedKernelTrace` proves the inverse-Gram
  identity `ζ = J` in the unlocalized case);
* **order-`m` product remainder** `R² ≤ |T|²·δ^{2(m+1)}` — a finite sum of products of
  `m+1` bounded factors (`HigherOrderInfluence.ProductRemainder`). A separate theorem,
  `const_mul_natCast_rpow_sub_tendsto_zero` proves only a generic negative-power limit; relating
  its exponent comparison to `m` and nuisance rates requires an additional argument.

`projectionKernel_risk_bound` assembles these into a single explicit upper bound on the risk: it
takes the bias-variance decomposition as input and discharges the second-order variance term and
the product remainder from the Causalean theorems, leaving only `V₁` and `B²` (supplied by the
sibling local-polynomial / series-sieve substrates) as hypotheses.
-/

public section

namespace Causalean.Stat.Nonparametric.HigherOrderInfluence

open MeasureTheory ProbabilityTheory
open Causalean.Stat

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
  {g : X → X → ℝ}

/-- **Conditional projection-kernel risk algebra.** For [an i.i.d. sample and a symmetric,
square-integrable, doubly degenerate kernel](hyp:S,hg), [sample size at least two](hyp:hn),
[positive bandwidth](hyp:hh), and [nonnegative projection dimension and trace constant](hyp:hJ,hC),
this theorem assumes [the estimator's risk
decomposition into first-order variance, projection bias, degenerate U-statistic variance, and
squared remainder](hyp:hdecomp), as well as the stated bounds on the [first-order variance](hyp:hV1),
[projection bias](hyp:hB), [kernel energy](hyp:hzeta), and [remainder](hyp:hRbd,hnn,hle);
it only combines those inputs into [the displayed risk bound](goal). It is not a theorem deriving
a higher-order influence function (HOIF) risk decomposition or its first-order and
approximation terms.

The degenerate U-statistic variance term and the product-remainder term are discharged from the
Causalean theorems `degenerate_uStatistic_variance_le` and `productRemainder_sq_le`; the remaining two
terms are the first-order-variance / projection-bias inputs from the sibling substrates. -/
theorem projectionKernel_risk_bound (S : IIDSample Ω X μ P) (hg : DegenKernel P g)
    {ι : Type*} (T : Finset ι) (e : ι → ℕ → ℝ) (R : ℝ)
    {risk V1 Bsq Cv1 Cb C J h s d δ : ℝ} {n m : ℕ}
    (hn : 2 ≤ n) (hh : 0 < h) (hJ : 0 ≤ J) (hC : 0 ≤ C)
    (hzeta : IIDSample.zeta P g ≤ C * J / h ^ 2)
    (hV1 : V1 ≤ Cv1 / ((n : ℝ) * h))
    (hB : Bsq ≤ Cb * J ^ (-(4 * s / d)))
    (hnn : ∀ t ∈ T, ∀ k ∈ Finset.range (m + 1), 0 ≤ e t k)
    (hle : ∀ t ∈ T, ∀ k ∈ Finset.range (m + 1), e t k ≤ δ)
    (hRbd : |R| ≤ ∑ t ∈ T, ∏ k ∈ Finset.range (m + 1), e t k)
    (hdecomp : risk ≤ V1 + Bsq + variance (uStatistic S g n) μ + R ^ 2) :
    risk ≤ Cv1 / ((n : ℝ) * h) + Cb * J ^ (-(4 * s / d))
            + 4 * C * J / ((n : ℝ) * h) ^ 2 + (T.card : ℝ) ^ 2 * δ ^ (2 * (m + 1)) := by
  have hV2 : variance (uStatistic S g n) μ ≤ 4 * C * J / ((n : ℝ) * h) ^ 2 :=
    degenerate_uStatistic_variance_le S hg hn hh hJ hC hzeta
  have hRem : R ^ 2 ≤ (T.card : ℝ) ^ 2 * δ ^ (2 * (m + 1)) :=
    productRemainder_sq_le T e m δ R hnn hle hRbd
  calc risk ≤ V1 + Bsq + variance (uStatistic S g n) μ + R ^ 2 := hdecomp
    _ ≤ Cv1 / ((n : ℝ) * h) + Cb * J ^ (-(4 * s / d))
          + 4 * C * J / ((n : ℝ) * h) ^ 2 + (T.card : ℝ) ^ 2 * δ ^ (2 * (m + 1)) :=
        add_le_add (add_le_add (add_le_add hV1 hB) hV2) hRem

end Causalean.Stat.Nonparametric.HigherOrderInfluence

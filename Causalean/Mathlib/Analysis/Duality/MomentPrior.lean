/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.Mathlib.Analysis.Duality.MomentPrior.Basic
public import Causalean.Mathlib.Analysis.Duality.MomentPrior.Duality
public import Causalean.Mathlib.Analysis.Duality.MomentPrior.Fejer
public import Causalean.Mathlib.Analysis.Duality.MomentPrior.Rate

/-!
# Best polynomial approximation of |x| and moment-matched priors

The best uniform error E_K of approximating x ↦ |x| on [−1, 1] by polynomials of degree at most K
is of exact order 1/K: (1/100)/K ≤ E_K ≤ 1/K for every K ≥ 1. By duality there are two symmetric
probability measures on [−1, 1] whose moments agree up to order K while their means of |x| differ
by exactly 2·E_K. Such pairs are the least-favourable priors in minimax lower bounds for
non-smooth functionals such as the L¹ norm.

## Contents

* `MomentPrior.Basic` — the error `bestUniformApproxErrorAbs K`, its monotonicity in K and the
  existence of a best polynomial (`exists_bestPolynomialAbs`).
* `MomentPrior.Duality` — the pair of priors `AbsMomentMatchedPriors K` and its existence
  (`exists_symmetric_momentMatched_absGap`), from a Hahn–Banach and Riesz extremal signed measure.
* `MomentPrior.Fejer` — Fejér and de la Vallée-Poussin means and a bounded functional that
  vanishes on low Fourier modes, used for the lower bound.
* `MomentPrior.Rate` — `bestUniformApproxErrorAbs_upper`, `bestUniformApproxErrorAbs_lower` and
  `bestUniformApproxErrorAbs_order`; the constants are explicit but not sharp.

This file only gathers the modules above.
-/

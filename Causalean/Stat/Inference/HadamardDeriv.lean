/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.CLT.HadamardDeriv

/-!
# Hadamard directional derivatives

A map `φ` between normed spaces is Hadamard directionally differentiable at `θ` with derivative
`φ′` when `(φ(θ + tₙ hₙ) − φ(θ)) / tₙ → φ′(h)` for all `tₙ ↓ 0` and `hₙ → h`; `φ′` need not be
linear. Every Fréchet-differentiable map has this property, and so do `max` and `min` on pairs of
reals, whose derivative at a tie is `max(u, v)` or `min(u, v)`. The property, together with
continuity of the derivative, is stable under composition, pairing, sums, differences, products,
quotients with nonzero denominator, and finite maxima and minima.

## Main definitions and results (all in `Causalean.Stat.CLT.HadamardDeriv`)

* `HasHadamardDirDerivAt`, `HasContinuousHadamardDirDerivAt` — the property and its version with a
  continuous derivative.
* `HasFDerivAt.hasHadamardDirDerivAt` — Fréchet differentiability implies it.
* `hasHadamardDirDerivAt_max`, `hasHadamardDirDerivAt_min` — with derivatives `maxDirDeriv`,
  `minDirDeriv`.
* `HasHadamardDirDerivAt.comp` and the `HasContinuousHadamardDirDerivAt` closure rules (`prod`,
  `add`, `sub`, `mul`, `div`, `finset_sum`, `max`, `min`, `finset_sup'`, `finset_inf'`).

This file declares nothing itself; it makes that module available under the inference-layer path.
-/

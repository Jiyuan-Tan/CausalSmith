/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic lower and upper bounds for doubly-robust ATE estimation — entry point

Roll-up module for the `Estimation/MinimaxATE/` development (Jin–Syrgkanis 2024,
*Structure-agnostic Optimality of Doubly Robust Learning for Treatment Effect Estimation*,
arXiv:2402.14264).  **Import this file** to pull in the whole development; the index below
says where each headline result lives.

The finite observed-data model (`Obs`, `obsLaw`, `productLaw`, `ate`, `l2sq`, `nMiss`,
`minimaxMiss`) is in `MinimaxATE/Model.lean`. Its budgets `εg, εm` are
squared-`L²(P_X)` nuisance errors around a fixed center `(mhat, ghat)`. The ancillary-product
result also permits an arbitrary common probability law outside this finite core.

## Headline results

### Converse — perturbation-indexed finite-sample lower bounds

* `minimax_lower_bound` in `ConstCenterHalf/ChiSquaredCore.lean`: base case,
  constant center `(m̂,ĝ) ≡ ½`.
* `minimax_lower_bound_gen` in `ConstCenterGeneral/LowerBound.lean`: arbitrary
  constant center `(m₀,g₀,g₁) ∈ (0,1)³`.
* `minimax_lower_bound_var` in `VaryingCenterCase1/LowerBound.lean`: cell-varying
  center using the paper's Case-1-shaped perturbation family.
* `minimax_lower_bound_var2` in `VaryingCenterCase2/LowerBound.lean`:
  cell-varying center using the paper's Case-2-shaped perturbation family.
* `two_point_lower_bound_ancillary_product` in
  `ConstCenterHalf/AncillaryProduct.lean`: invariance under a common ancillary product.
* `parametric_lower_bound` in `ConstCenterHalf/Parametric.lean`: a two-point
  bound at a caller-supplied shift `δ`.
* `minimax_lower_bound_mse` and `minimax_lower_bound_mse_gen` in
  `ConstCenterHalf/MSE.lean` and `ConstCenterGeneral/MSE.lean`: weaker
  expected-risk (MSE) forms.

The minimax theorems construct two fixed laws, or a fixed null and a finite mixture,
inside the nuisance class and prove a testing lower bound. They then use class membership
and `nMiss_le_minimaxMiss` to conclude
`1/4 ≤ minimaxMiss mhat ghat εg εm n est s`.  Thus the displayed minimax claim is not asserted
directly from a two-fixed-law bound without the required embedding step.

### Achievability — a finite-sample DR/AIPW upper bound

* `aipw_minimaxMiss_le` in `Optimality.lean`: worst-case miss of the fixed-center
  AIPW estimator `estAIPW` is bounded by the Chebyshev expression
  `((1+2/ε)²/n)/(s − ε⁻¹·2√εg√εm)²` for any
  `s > ε⁻¹·2√εg√εm`.

### Combined finite-sample certificate

* `aipw_finiteSample_twoThreshold_bounds` in `Optimality.lean` bundles the `_var`
  converse and the AIPW achievability into `FiniteSampleTwoThresholdBounds`. The
  statement does not require the lower separation to be positive or compare it
  with the caller-supplied upper separation, so it is not by itself a minimax-rate theorem.

## Folder layout

* `Reduction/` — `Witness`, `WitnessMixture`, `Bump`: Le Cam two-point / Rademacher-mixture
  reduction and the `l2sq` bump algebra.
* `ConstCenterHalf/` — the base pipeline (constant nuisance center `½`): `Construction`,
  `Gap`, `Membership`, `ChiSqOverlap`, `ExplicitWitness`, `Ingster`, `ChiSquaredCore`
  (holds the base lower bound), plus the base-variant headlines `AncillaryProduct`, `MSE`,
  `Parametric`.
* `ConstCenterGeneral/` — arbitrary **constant** center `(m₀,g₀,g₁)`: `Construction`,
  `Gap`, `Membership`, `ChiSqOverlap`, `LowerBound`, `MSE`.
* `VaryingCenterCase1/` — **cell-varying** center, **Case-1-shaped** family:
  `Construction`, `Gap`, `Membership`, `ChiSqOverlap`, `Ingster` (the non-uniform
  per-pair χ²), `LowerBound`.
* `VaryingCenterCase2/` — **cell-varying** center, **Case-2-shaped** family: the symmetric
  second construction (`mλ = m₀(1+αg₁Δ)D`, `gλ(1) = g₁/D`, `D = 1+(β/g₁)Δ−αβ`), reusing
  `VaryingCenterCase1/Ingster`.  Files `Construction`, `Gap`, `Membership`, `ChiSqOverlap`,
  `LowerBound`.
* `Achievability/` — `AIPWEstimator`: the AIPW score/estimator + bias & variance bounds.
* `Optimality.lean`, `Model.lean` — the capstone and the finite observed-data model (top level).
-/

module
public import Causalean.Estimation.MinimaxATE.Achievability.AIPWEstimator
public import Causalean.Estimation.MinimaxATE.Causal.Bridge
public import Causalean.Estimation.MinimaxATE.Causal.Construction
public import Causalean.Estimation.MinimaxATE.Causal.Minimax
public import Causalean.Estimation.MinimaxATE.ConstCenterGeneral.ChiSqOverlap
public import Causalean.Estimation.MinimaxATE.ConstCenterGeneral.Construction
public import Causalean.Estimation.MinimaxATE.ConstCenterGeneral.Gap
public import Causalean.Estimation.MinimaxATE.ConstCenterGeneral.LowerBound
public import Causalean.Estimation.MinimaxATE.ConstCenterGeneral.MSE
public import Causalean.Estimation.MinimaxATE.ConstCenterGeneral.Membership
public import Causalean.Estimation.MinimaxATE.ConstCenterHalf.AncillaryProduct
public import Causalean.Estimation.MinimaxATE.ConstCenterHalf.ChiSqOverlap
public import Causalean.Estimation.MinimaxATE.ConstCenterHalf.ChiSquaredCore
public import Causalean.Estimation.MinimaxATE.ConstCenterHalf.Construction
public import Causalean.Estimation.MinimaxATE.ConstCenterHalf.ExplicitWitness
public import Causalean.Estimation.MinimaxATE.ConstCenterHalf.Gap
public import Causalean.Estimation.MinimaxATE.ConstCenterHalf.Ingster
public import Causalean.Estimation.MinimaxATE.ConstCenterHalf.MSE
public import Causalean.Estimation.MinimaxATE.ConstCenterHalf.Membership
public import Causalean.Estimation.MinimaxATE.ConstCenterHalf.Parametric
public import Causalean.Estimation.MinimaxATE.Model
public import Causalean.Estimation.MinimaxATE.Optimality
public import Causalean.Estimation.MinimaxATE.Reduction.Bump
public import Causalean.Estimation.MinimaxATE.Reduction.Witness
public import Causalean.Estimation.MinimaxATE.Reduction.WitnessMixture
public import Causalean.Estimation.MinimaxATE.VaryingCenterCase1.ChiSqOverlap
public import Causalean.Estimation.MinimaxATE.VaryingCenterCase1.Construction
public import Causalean.Estimation.MinimaxATE.VaryingCenterCase1.Gap
public import Causalean.Estimation.MinimaxATE.VaryingCenterCase1.Ingster
public import Causalean.Estimation.MinimaxATE.VaryingCenterCase1.LowerBound
public import Causalean.Estimation.MinimaxATE.VaryingCenterCase1.Membership
public import Causalean.Estimation.MinimaxATE.VaryingCenterCase2.ChiSqOverlap
public import Causalean.Estimation.MinimaxATE.VaryingCenterCase2.Construction
public import Causalean.Estimation.MinimaxATE.VaryingCenterCase2.Gap
public import Causalean.Estimation.MinimaxATE.VaryingCenterCase2.LowerBound
public import Causalean.Estimation.MinimaxATE.VaryingCenterCase2.Membership

/-!
This file is the entry point for the structure-agnostic lower- and upper-bound development
for doubly robust average-treatment-effect estimation.  Importing it brings in
the finite observed-data model, the constant-center and cell-varying minimax
lower bounds, the finite fixed-center AIPW achievability theorem, their two-threshold
finite-sample packaging, and the causal re-centering of the cell-varying lower bounds.

The main lower-bound declarations are `minimax_lower_bound`,
`minimax_lower_bound_gen`, `minimax_lower_bound_var`,
`minimax_lower_bound_var2`, `two_point_lower_bound_ancillary_product`,
`parametric_lower_bound`, `minimax_lower_bound_mse`, and
`minimax_lower_bound_mse_gen`.  The achievability side is centered on
`aipw_minimaxMiss_le`, and `aipw_finiteSample_twoThreshold_bounds` packages the converse and
AIPW upper bound without asserting that their two separation scales match.

## Causal grounding (`Causal/`)

The observed-data contrast `ate g = E_X[g(1,·) − g(0,·)]` on which the proof
machinery computes is identified with a genuine potential-outcome ATE.
`Causal/Construction.lean` builds, from a finite DGP `(m, g)`, a concrete
backdoor SCM (`Un → Xc → A → Y`, `Xc → Y`, latent noises `Ea, Ey`) and lifts it
through `POSystem.ofSCM` to a `POBackdoorSystem`; `Causal/Bridge.lean` defines
`causalATE m g := (dgpBackdoor m g).ATE = ∫ (Y(1) − Y(0)) dμ` and proves
`causalATE_eq_ate : causalATE m g = ate g` (under strict overlap), so the
minimax lower bound is a bound on the causal estimand `E[Y(1) − Y(0)]`,
identified by backdoor adjustment, not merely a regression contrast.
`Causal/Minimax.lean` contains the causal-centered miss probability
`minimaxMissCausal` and the first- and second-family causal lower bounds
`minimax_lower_bound_var_causal` and `minimax_lower_bound_var2_causal`.
-/

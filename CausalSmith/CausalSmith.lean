/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# CausalSmith umbrella

Auto-generated theorem package. Each subdir corresponds to a theorem-substrate
cluster used by the `causalsmith research` pipeline:

* `CausalSmith.Panel.*` — panel / linear-projection theorems
* `CausalSmith.ExactID.*` — exact identification (backdoor, frontdoor, IV, DID,
  DTR, LATE, mediation) — populated as proposals graduate.
* `CausalSmith.PartialID.*` — partial identification / bounds (Manski,
  Balke–Pearl, IV bounds, sensitivity, shape restrictions, missing-data) —
  populated as proposals graduate.
* `CausalSmith.Stat.*` — minimax-rate / efficiency / limit-law theorems for
  causal estimands — populated as proposals graduate.
* `CausalSmith.Experimentation.*` — design-based randomization-inference
  theorems (CLT / asymptotic normality + Wald coverage for design-based causal
  estimands), built on `Causalean/Experimentation/` — populated as proposals
  graduate.
* `CausalSmith.SCM.*` — graphical identification / SCM theorems.
* `CausalSmith.Substrate.*` — reusable substrate built by `causalsmith study`.
* `CausalSmith.Mathlib.*` — Mathlib-shaped helpers staged in CausalSmith
  before any promotion to `Causalean/Mathlib/`.

This umbrella is the DEFAULT build target and deliberately stays light: it
imports Causalean and the shared Mathlib-shaped helpers. `lake -d CausalSmith
build` therefore warms the foundation a new research run starts from and never
compiles the Lean code of existing papers.

Existing papers are opt-in. Each run is built through its own run barrel
(`lake -d CausalSmith build CausalSmith.<Area>.<RUN>_Research`), and a run that
imports an earlier paper or a `CausalSmith.Substrate.*` module compiles just that
import closure on demand. Prebuilt oleans for every module are fetched with
`scripts/fetch_build_cache.sh --causalsmith`, and
`CausalSmith/tools/scripts/full_tree_build.sh` type-checks every module.
Causalean never imports anything from this package.
-/

module
public import Causalean
public import CausalSmith.Mathlib.Concentration.FiniteClassRademacher
public import CausalSmith.Mathlib.InformationTheory.ProductChiSquared
public import CausalSmith.Mathlib.Probability.ParameterizedFinitePoissonSample
public import CausalSmith.Mathlib.Probability.PoissonUsableOccupancy

public section

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Discovery.InvariantPrediction.LinearGaussian
public import Causalean.Discovery.InvariantPrediction.Soundness

/-!
# Invariant Causal Prediction — umbrella

Entry point for the formalization of Peters, Bühlmann & Meinshausen, *Causal
inference using invariant prediction: identification and confidence intervals*
(JRSS-B 2016, `arXiv:1501.01332`).  Import this file to get the whole
development.  This is the third identification engine in `Causalean.Discovery`,
beside non-Gaussianity (`LiNGAM`) and interventions-plus-second-moments
(`LinearDisentanglement`): here causal structure is identified from the
**invariance of the causal mechanism across interventional environments**.

## Main results

* `EnvFamily` (`Model.lean`) — the model: a `Fintype`-indexed family of SCMs over
  common observed/latent variables that share the target's mechanism, parents and
  noise law (no environment intervenes on the target), each carrying its
  intervention's fixed values.
* `EnvFamily.Invariant` (`Invariance.lean`) — a predictor set `S` is invariant
  when the conditional law of the target given `X_S` is the same in every
  environment; `mechanism_invariant` shows the target's observed parents are
  always invariant.
* `EnvFamily.icp_sound` (`Soundness.lean`) — a population set-inclusion consequence
  of the mechanism validity represented by Proposition 1. The identified set
  `S(E) = ⋂{invariant S}` is contained in the target's observed parents `PA(Y)`:
  ICP never selects a non-parent. The paper's Theorem 1 is instead a finite-sample
  coverage guarantee and is not formalized here.

## Status

The Proposition 1 mechanism-validity/population-soundness analogue is formalized
in the nonparametric SCM setting. A separate random-variable/regression API under
`LinearGaussian/` proves
`icp_complete_linearGaussian_of_exogeneity`, a specialization of the paper's
Theorem 2(i) with observational and interventional target exogeneity supplied as
structure fields. Its `identifiedSet` is not definitionally the nonparametric
`idSet`; no equivalence theorem between the two APIs is claimed here.
-/

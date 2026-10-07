/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Experimentation.BettingMean
public import Causalean.Experimentation.ClusterRandomizedHT
public import Causalean.Experimentation.DesignBased
public import Causalean.Experimentation.ExposureMappingInterference
public import Causalean.Experimentation.FinitePopulationMoments
public import Causalean.Experimentation.MatchedPairDesign
public import Causalean.Experimentation.Sequential
public import Causalean.Experimentation.SuperPopulation
public import Causalean.Experimentation.TwoStageInterference
public import Causalean.Experimentation.UnknownInterference

/-!
# Experimentation — randomization, sequential, and network inference

Inference for randomized experiments, in three probability models. In the design-based model
the potential outcomes are fixed and the only randomness is the assignment drawn from a finite
design: here the library proves unbiasedness and exact or bounded randomization variances of
Horvitz–Thompson and difference-in-means estimators, including under interference between units
(exposure mappings, two-stage designs, unknown interference with Bernoulli assignment, cluster and
matched-pair designs), together with consistency results such as `htEst_consistent_eate`. In the
sequential model the data arrive over time: Ville's inequality `ville_inequality` for test
supermartingales gives tests valid under optional stopping and confidence sequences with
time-uniform coverage, applied to betting confidence sequences for a bounded mean. In the
super-population model units are random with dependence along a network: `networkSum_clt` is a
central limit theorem for sums of locally dependent variables and `netHAC_consistent` gives
consistency of the network-HAC variance estimator.

* `DesignBased` — paper-agnostic substrate (`FiniteDesign` `E`/`Var`/`Cov`, exposure mappings,
  Horvitz–Thompson estimators, Chebyshev, the edge-sum variance bound, normal-CDF facts, the
  finite-design→measure bridge).
* `Sequential` — measure-theoretic substrate for adaptive / sequential experiments with valid
  inference: test supermartingales and Ville's inequality, anytime-valid tests and confidence
  sequences, and the adaptive-design abstraction.
* `ExposureMappingInterference` — exposure-mapping average effects under general interference,
  formalizing Aronow & Samii (2017).
* `TwoStageInterference` — two-stage / partial-interference designs and their large-sample layer,
  formalizing Hudgens & Halloran (2008) and Liu & Hudgens (2014).
* `UnknownInterference` — Bernoulli-design EATE estimation under unknown interference, formalizing
  the core of Sävje, Aronow & Hudgens (2021).
* `MatchedPairDesign` — a fixed-pair randomized design, its difference-in-means estimator,
  unbiasedness, and an exact design-based variance formula, following the setup of Bai (2022).
* `BettingMean` — betting confidence sequences for bounded means, after Waudby-Smith & Ramdas
  (2024), as a worked application of the anytime-valid substrate.
* `ClusterRandomizedHT` — Horvitz–Thompson estimation for cluster-randomized experiments,
  formalizing Middleton & Aronow (2015).
* `FinitePopulationMoments` — exact simple-random-sample mean moments, after Li & Ding (2017).
* `SuperPopulation` — model-based (super-population) inference under network dependence: the
  locally-dependent network field (the m-dependent sibling of an i.i.d. sample), m-dependent CLTs
  for network sums and means via the Stein dependency-graph CLT, the network-HAC variance
  estimator, and HAC consistency theorems for the same asymptotic regime.

Further experimentation papers should be placed under method-facing module names, with the
bibliographic attribution in the module docstring.
-/

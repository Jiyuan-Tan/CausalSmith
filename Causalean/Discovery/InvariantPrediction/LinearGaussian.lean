/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Discovery.InvariantPrediction.LinearGaussian.Completeness

/-!
# Invariant Causal Prediction — linear-Gaussian completeness

Exact recovery of the direct causes of a target in a linear structural equation model with
centered Gaussian noise observed under do-interventions: a specialization of Theorem 2(i) of
Peters, Bühlmann & Meinshausen (JRSS-B 2016, `arXiv:1501.01332`). A predictor set S passes the
regression-invariance null when some coefficient vector supported on S leaves a residual that is
independent of each predictor in S and has the same law in the observational and in every
interventional environment; S(E) is the intersection of all such sets. If every predictor is, in
at least one environment, the only intervened variable and is set to a value different from its
observational mean, and the observational regressors are integrable, then S(E) is exactly the
parent set of the target. The models carry independence of the target noise from the target's
parents, in the observational and in each interventional environment, as an assumption; it is not
derived from the recursive structural equations.

Unlike the sibling nonparametric SWIG/kernel development (which proves
soundness, `S(E) ⊆ PA(Y)`, in full generality), this sub-development works in the
paper's **linear-Gaussian** framework — the only setting in which the paper
establishes the converse `S(E) ⊇ PA(Y)` — using a random-variable encoding.

## Files

* `Model.lean` — the observational linear-Gaussian SEM (`ObsSEM`), interventional
  environments with do-interventions (`Env`), and the environment family
  (`EnvFamily`), all in random-variable form with a `DAG` for the graph.
* `Regression.lean` — the regression residual, the regression-invariance null
  `H_{0,S}` (`InvarianceNull`), and the identified set `S(E)` (`identifiedSet`).
* `Helpers/Moments.lean` — Gaussian-noise moments: `εⱼ` is integrable with
  `E[εⱼ] = 0`.
* `Helpers/Residual.lean` — with the causal coefficient `γ* = β₀,·`, the residual
  equals the target noise `ε₀` a.e. in every environment.
* `Helpers/Invariance.lean` — non-descendant invariance: under `do(X_{k₀}=a)`,
  every non-descendant of `k₀` keeps its observational value a.e.
* `Completeness.lean` — the do-intervention hypotheses, soundness /
  youngest-node / mean-shift intermediate lemmas, and the main theorem
  `icp_complete_linearGaussian_of_exogeneity : S(E) = PA(Y)`. Soundness assumes
  the exogeneity certificates carried as `ObsSEM.hYexo` / `Env.hExo`.
-/

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Liu–Hudgens (2014): large-sample theory for the direct-effect contrast estimator

Umbrella for the large-sample (groups → ∞) layer over the Hudgens–Halloran two-stage design.

* `Setup` — the sequence-of-experiments bundle `LHExperiment`, carrying the two-stage design and
  its known design propensities, with the reusable unbiasedness (`E_estD`) and variance
  (`var_estD`) bridges.
* `Consistency` — the estimator converges in probability to the population average
  control-minus-treatment direct-effect contrast as the number of groups grows (Chebyshev, since
  the design variance vanishes), assuming fixed allocation counts on the within-group design
  support.
* `CLT` — a conditional-to-unconditional mixture-transfer theorem for the studentized
  direct-contrast CDF, assuming a uniform conditional Gaussian-CDF limit.
* `Identical` — discharges the analytic homogeneity hypothesis of the CLT bundle from literally
  identical groups: a coordinate-permutation relabeling proves the conditional studentized CDF is
  selection-symmetric (`hhom_of_identical`), yielding `directEffect_clt_identical`, the CLT resting
  on identical groups, bounded centered per-group contrast estimators, and the many-groups rates
  (no `hhom` assumption).
* `Wald` — asymptotic (oracle) Wald confidence-interval coverage: the interval `D̂E ± z·√directVar`
  has coverage at least `1 − γ`, from the CLT limits and standard-normal CDF symmetry.
* `WaldFeasible` — the feasible analogue: the interval `D̂E ± z·√V̂` using an *estimated* variance
  attains coverage at least `1 − γ` whenever the estimator is conservative-consistent.

Every direct contrast in this layer uses Hudgens–Halloran's control-minus-treatment orientation,
the negative of Liu–Hudgens' treatment-minus-control estimand. The homogeneous and identical-group
CLTs set the between-group effect variance to zero, so they are strict special cases of the
heterogeneous Liu–Hudgens Proposition 5.1.
-/

module
public import Causalean.Experimentation.TwoStageInterference.Asymptotic.Setup
public import Causalean.Experimentation.TwoStageInterference.Asymptotic.Consistency
public import Causalean.Experimentation.TwoStageInterference.Asymptotic.CLT
public import Causalean.Experimentation.TwoStageInterference.Asymptotic.CLTDischarge
public import Causalean.Experimentation.TwoStageInterference.Asymptotic.CLTDischargeMain
public import Causalean.Experimentation.TwoStageInterference.Asymptotic.Identical
public import Causalean.Experimentation.TwoStageInterference.Asymptotic.Wald
public import Causalean.Experimentation.TwoStageInterference.Asymptotic.WaldFeasible

/-! # Two-stage interference asymptotics

Two-stage interference asymptotics cover consistency, conditional-to-unconditional CDF transfer,
homogeneous special-case central limit theorems, and Wald intervals for the
control-minus-treatment direct-effect contrast. This is the negative of Liu–Hudgens'
treatment-minus-control estimand.

This roll-up imports:

* `Setup`, defining `LHExperiment`, the joint design `jointD`, the contrast estimator `estD`, the
  estimand `DEbar`, the closed-form variance `directVar`, and the bridges `E_estD` / `var_estD`.
* `Consistency`, proving `estDirect_consistent_of_bounded_outcomes` from bounded potential outcomes,
  fixed allocation counts on the within-group design support, and a growing number of selected
  groups.
* `CLT`, proving `directEffect_cdf_tendsto_of_uniform_conditional` from uniform conditional
  studentized-CDF convergence; the conditional limit is assumed.
* `CLTDischarge` and `CLTDischargeMain`, which package homogeneity in `Homogeneous` and prove the
  primitive homogeneous special case `directEffect_clt_homogeneous`.
* `Identical`, deriving the homogeneity hypothesis from literal identical-group symmetry and
  proving `directEffect_clt_identical`.
* `Wald` and `WaldFeasible`, proving oracle and conservative-feasible Wald coverage.
-/

public section

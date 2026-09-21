/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Liu–Hudgens (2014): asymptotic (feasible) Wald confidence-interval coverage

The **feasible** Wald interval `D̂E ± z·√(V̂)` for the Hudgens–Halloran-oriented
control-minus-treatment direct-effect contrast — using an *estimated* variance `V̂` instead of the
unknown true design variance `directVar` — attains asymptotic coverage at least `1 − γ`, provided
the variance estimator is *conservative-consistent*: it undershoots the true variance only with
vanishing probability (`hVhat`). The contrast is the negative of Liu–Hudgens'
treatment-minus-control estimand.

The theorem specializes the shared design-based transfer
`conservative_wald_liminf_of_feasible_studentized_cdf` to the `LHExperiment` bundle; only
the experiment-specific estimator, target, variance, and studentized-CDF identity are supplied
locally. It is the feasible analogue of the oracle interval `wald_coverage_oracle` in `Wald.lean`.

**Scope / faithfulness.** As in Aronow–Samii's headline `wald_coverage_feasible`, the estimator
`Vh` is taken abstractly and its conservative-consistency `hVhat` is a *hypothesis* — this is the
genuine input to the feasible interval.  Constructing a concrete Liu–Hudgens `V̂` (the between-group
sample variance of the ψ-selected group estimates plus the within-group Neyman estimators
`varHat`) and discharging `hVhat` from primitive conditions is the analogue of Aronow–Samii's
separate `wald_coverage_feasible_of_bounded_degree_factorization_covariance`. The in-expectation
conservativeness already proven (`E_varHat_conservative`, `Var ≤ E[V̂]`) is a necessary ingredient
toward `hVhat` but is *not* the same statement (it lacks the concentration half), so it is not
invoked here. The direct-contrast CDF limit is supplied per threshold as `hclt` (the conclusion of
`directEffect_cdf_tendsto_of_uniform_conditional`, quantified over `t`), decoupling this coverage
statement from the conditional-CLT plumbing — mirroring how `wald_coverage_oracle` takes its two
limits as hypotheses.
-/

module
public import Causalean.Experimentation.DesignBased.WaldCoverage
public import Causalean.Experimentation.TwoStageInterference.Asymptotic.Setup

/-! # Feasible Wald coverage

This file specializes the shared design-based feasible-Wald transfer to the control-minus-treatment
estimator, which is the negative of Liu–Hudgens' treatment-minus-control estimator. The theorem
`wald_coverage_feasible` combines a studentized CDF limit with conservative consistency of `Vh`,
proving asymptotic lower coverage for intervals of the form `estD ± zq * sqrt (Vh)`.
-/

public section

open scoped BigOperators Topology
open Filter

namespace Causalean
namespace Experimentation
namespace TwoStageInterference

open DesignBased

/-- **Asymptotic feasible Wald coverage (Liu–Hudgens 2014).** Along [a sequence of two-stage
Hudgens–Halloran experiments](hyp:Exp), let [`stud n` be the studentized statistic
`(D̂E − DE̅)/√directVar`](hyp:stud,hstud) for the control-minus-treatment direct-effect contrast,
and assume [its per-threshold CDF converges to the standard normal CDF at every
threshold](hyp:hclt) and [the design variance is everywhere positive](hyp:hVar). Let [`Vh n` be
an arbitrary variance estimator that is conservative-consistent — for every slack `ε > 0` the
probability it undershoots `(1−ε)` times the true variance tends to zero](hyp:Vh,hVhat), and let
[`zq ≥ 0` be the standard-normal upper quantile at level `γ`, `Φ(zq) = 1 − γ/2`](hyp:γ,zq,hzq0,hzq).
Then [the feasible Wald interval `D̂E ± zq·√(Vh)` attains asymptotic coverage of `DE̅` at least
`1 − γ`](goal). The contrast is the negative of Liu–Hudgens' treatment-minus-control estimand. -/
theorem wald_coverage_feasible (Exp : ℕ → LHExperiment)
    (stud : ∀ n, (StratAssign (Exp n).ι × ∀ i, Fin ((Exp n).gsize i) → Bool) → ℝ)
    (hstud : ∀ n sw, stud n sw = ((Exp n).estD sw - (Exp n).DEbar) / Real.sqrt ((Exp n).directVar))
    (Vh : ∀ n, (StratAssign (Exp n).ι × ∀ i, Fin ((Exp n).gsize i) → Bool) → ℝ)
    (hclt : ∀ t, Tendsto (fun n => (Exp n).jointD.Pr (fun sw => stud n sw ≤ t))
      atTop (𝓝 (stdNormalCdf t)))
    (hVar : ∀ n, 0 < (Exp n).directVar)
    (hVhat : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (Exp n).jointD.Pr (fun sw =>
        Vh n sw < (1 - ε) * (Exp n).directVar)) atTop (𝓝 0))
    {γ : ℝ} (zq : ℝ) (hzq0 : 0 ≤ zq) (hzq : stdNormalCdf zq = 1 - γ / 2) :
    1 - γ ≤ Filter.liminf
      (fun n => (Exp n).jointD.Pr (fun sw =>
        |(Exp n).estD sw - (Exp n).DEbar| ≤ zq * Real.sqrt (Vh n sw)))
      Filter.atTop := by
  simpa only [one_mul, div_one, abs_sub_comm] using
    conservative_wald_liminf_of_feasible_studentized_cdf
      (fun n => (Exp n).jointD)
      (fun n => (Exp n).estD)
      (fun n => (Exp n).DEbar)
      (fun n => (Exp n).directVar)
      (fun _ => 1)
      Vh
      (fun _ => one_pos) hVar hVhat γ zq
      (fun t => by simpa only [Real.sqrt_one, one_mul, hstud] using hclt t)
      hzq0 hzq

end TwoStageInterference
end Experimentation
end Causalean

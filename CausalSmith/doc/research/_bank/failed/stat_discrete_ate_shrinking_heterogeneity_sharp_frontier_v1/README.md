---
qid: stat_discrete_ate_shrinking_heterogeneity_sharp_frontier
spec: v1
topic: "Determine the sharp near-homogeneity frontier for ATE estimation with high-dimensional discrete confounders. For fixed known 0<epsilon<1/2, M>=1 and sigma in [0,2], observe n iid (X,A,Y) with X in [d], binary A, real Y, arbitrary unknown cell masses (null cells allowed), and unknown propensities in [epsilon,1-epsilon] on occupied cells. Consistency and conditional exchangeability identify tau=sum_k p_k(mu_1k-mu_0k). Each conditional mean lies in [-M/2,M/2] and each conditional central variance is at most M^2; no higher moments or bounded outcomes are assumed. Require max_k:p_k>0 |mu_1k-mu_0k-tau|<=sigma M, law by law. Uniformly over n>=3, 2<=d<=floor(n^2/log(en)), all sigma and M, determine a directly evaluable scalar rate r(n,d,sigma), a total computable estimator with worst-case MSE at most C_epsilon M^2 r, and a matching all-estimator same-class lower bound c_epsilon M^2 r. Comparison constants depend only on epsilon. Estimators may use the known class inputs but not unknown masses/propensities; define behavior on every sample, including empty cells.\n\nThe answer is open. With b=1/n+d/n^2 and u=d^2/[n^2 log^2(en)], the accepted same-class parent only proves lower b+sigma^2 min(1,u) versus upper 1/n+min(1,u,sigma^2+d/n^2). Resolve the entire shrinking-radius wedge and its transitions, not merely an endpoint, one sequence, or another bracket. At d=floor(n^(3/4)), sigma^2=u, current benchmarks range from order 1/n to order n^(-1/2)/log^2(en); this is a benchmark gap, not an asserted risk. Derive from the matched result exactly when approximately common effects retain collision-scale estimation and when rare-cell correction determines the rate. Do not stipulate that either existing bound is sharp.\n\nThe parent proves two anti-constraints: a hypothesis-independent outcome-channel transfer only gives product-scale lower separation, and the natural centered linear Chebyshev factorial lift has excessive singleton-pair variance even with oracle centering and sigma=0. Population bias reduction alone does not prove stochastic attainment. Any nonlinear stabilization/clipping must control its own uniform bias and risk under second moments. A new converse must respect the radius on every prior-support law, not merely on prior average. Proof architecture, estimator algebra and rate formula are delegated. Existing-selector optimality is eligible if a substantive new converse proves it. No unknown-radius adaptation or confidence-interval claim is requested.\n\nGrounding: Zeng-Balakrishnan-Han-Kennedy, https://arxiv.org/html/2405.00118, Theorems2-4 and Section4.2 explicitly leave radius dependence open. Their Section7 401(k) eligibility/net-assets analysis is the consumer: quantify which near-homogeneity assumptions justify estimation gains in sparse adjustment cells. This does not validate that dataset's overlap or reported intervals. The accepted parent stat_discrete_ate_heterogeneity_frontier_v1 supplies the bracket and architecture obstructions, not the new frontier. Legal sanity witness: n=10,d=4,M=1,epsilon=1/4,sigma=1/8, uniform masses, propensities alternating1/3,2/3, control means0 and treated means alternating1/16,-1/16, with independent Rademacher potential-outcome noises; tau=0 and all class constraints hold.\n\nPRESOLVE EVIDENCE REQUIRING VERIFICATION: A split-sample empirical-mass correction to the accepted occupancy-weighted pilot has an exact conditional error decomposition into outcome noise, centered effect deviations, and unmatched empirical mass. The draft derives a squared unmatched-mass bound of order (d/n)^2 and an inverse-binomial outcome-noise bound using only conditional second moments. Conditional on the imported pilot guarantee, it obtains M^2[1/n+sigma^2(d/n)^2] for d<=n, resolving the original polynomial-gap sequence at order M^2/n and narrowing the remaining bracket to a logarithmic gap. Checks included zero masses, empty blocks, exact homogeneity, saturation and the parent's failed channel and factorial constructions. The full frontier and proposed effective-log formula remain unproved.\nUNRESOLVED BOTTLENECK: Construct shared-design, exactly normalized marked-mixture priors with realization-wise radius control, concentrated ATE separation and small full-sample divergence at the proposed radius-dependent scale, or derive the corrected scale. The corresponding radius-dependent polynomial upper bound, stochastic covariance control and all uniform transitions also require proof; the draft lists every gap.\nEARLY KILL TEST: At d=n and sigma^2=log^2(en)/n, test the shared-design mixture likelihood, normalization and target concentration. A design-only divergence term should stop that proposed architecture before full proofs, preserving the original answer-open problem.\nSTRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_discrete_ate_shrinking_heterogeneity_sharp_frontier.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "No matched full-wedge rate, total attaining estimator, or same-class converse was delivered; the d=n, sigma^2=log^2(en)/n benchmark remains logarithmically nonmatching."
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "The stated project promises the sharp shrinking-radius frontier, but this theorem supplies only a strict upper-envelope tightening and explicitly leaves the residual wedge (including the benchmark) open; it must be positioned and routed as a partial frontier result rather than the promised resolution."
  - "At d=n and sigma^2=log^2(en)/n, neither closed-region condition holds. The outer separation bracket remains logarithmically nonmatching, and the conditionally centered marked-score program is not specified tightly enough to decide whether super-parametric separation is feasible."
reusable_artifacts:
  - "discovery/solve_oeq_repair_benchmark_prior.json — exact global-shift kill test and the surviving benchmark-prior obstruction"
  - "discovery/solve_thm_refined_bracket.json — proved empirical-mass upper branch and regional collision result"
  - "discovery/writeup.tex — consolidated partial-frontier derivation and explicit residual-domain boundary"
seeds_burned: []
proof_attempt_summary: |
  The run proved a total empirical-mass correction and a collision-scale result on a strict
  subregion, and it killed the simplest globally shifted marked-prior construction at the benchmark.
  It could not construct the supportwise shared-design converse or a matching stabilized upper
  estimator across the residual wedge, so the promised sharp full frontier remained open.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 22152561
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 22152561
  total_tokens_consumed: null
banked_on: "2026-09-10"
---

# stat_discrete_ate_shrinking_heterogeneity_sharp_frontier / v1 — Failed

**Topic.** Determine the sharp near-homogeneity frontier for ATE estimation with high-dimensional discrete confounders. For fixed known 0<epsilon<1/2, M>=1 and sigma in [0,2], observe n iid (X,A,Y) with X in [d], binary A, real Y, arbitrary unknown cell masses (null cells allowed), and unknown propensities in [epsilon,1-epsilon] on occupied cells. Consistency and conditional exchangeability identify tau=sum_k p_k(mu_1k-mu_0k). Each conditional mean lies in [-M/2,M/2] and each conditional central variance is at most M^2; no higher moments or bounded outcomes are assumed. Require max_k:p_k>0 |mu_1k-mu_0k-tau|<=sigma M, law by law. Uniformly over n>=3, 2<=d<=floor(n^2/log(en)), all sigma and M, determine a directly evaluable scalar rate r(n,d,sigma), a total computable estimator with worst-case MSE at most C_epsilon M^2 r, and a matching all-estimator same-class lower bound c_epsilon M^2 r. Comparison constants depend only on epsilon. Estimators may use the known class inputs but not unknown masses/propensities; define behavior on every sample, including empty cells.

The answer is open. With b=1/n+d/n^2 and u=d^2/[n^2 log^2(en)], the accepted same-class parent only proves lower b+sigma^2 min(1,u) versus upper 1/n+min(1,u,sigma^2+d/n^2). Resolve the entire shrinking-radius wedge and its transitions, not merely an endpoint, one sequence, or another bracket. At d=floor(n^(3/4)), sigma^2=u, current benchmarks range from order 1/n to order n^(-1/2)/log^2(en); this is a benchmark gap, not an asserted risk. Derive from the matched result exactly when approximately common effects retain collision-scale estimation and when rare-cell correction determines the rate. Do not stipulate that either existing bound is sharp.

The parent proves two anti-constraints: a hypothesis-independent outcome-channel transfer only gives product-scale lower separation, and the natural centered linear Chebyshev factorial lift has excessive singleton-pair variance even with oracle centering and sigma=0. Population bias reduction alone does not prove stochastic attainment. Any nonlinear stabilization/clipping must control its own uniform bias and risk under second moments. A new converse must respect the radius on every prior-support law, not merely on prior average. Proof architecture, estimator algebra and rate formula are delegated. Existing-selector optimality is eligible if a substantive new converse proves it. No unknown-radius adaptation or confidence-interval claim is requested.

Grounding: Zeng-Balakrishnan-Han-Kennedy, https://arxiv.org/html/2405.00118, Theorems2-4 and Section4.2 explicitly leave radius dependence open. Their Section7 401(k) eligibility/net-assets analysis is the consumer: quantify which near-homogeneity assumptions justify estimation gains in sparse adjustment cells. This does not validate that dataset's overlap or reported intervals. The accepted parent stat_discrete_ate_heterogeneity_frontier_v1 supplies the bracket and architecture obstructions, not the new frontier. Legal sanity witness: n=10,d=4,M=1,epsilon=1/4,sigma=1/8, uniform masses, propensities alternating1/3,2/3, control means0 and treated means alternating1/16,-1/16, with independent Rademacher potential-outcome noises; tau=0 and all class constraints hold.

PRESOLVE EVIDENCE REQUIRING VERIFICATION: A split-sample empirical-mass correction to the accepted occupancy-weighted pilot has an exact conditional error decomposition into outcome noise, centered effect deviations, and unmatched empirical mass. The draft derives a squared unmatched-mass bound of order (d/n)^2 and an inverse-binomial outcome-noise bound using only conditional second moments. Conditional on the imported pilot guarantee, it obtains M^2[1/n+sigma^2(d/n)^2] for d<=n, resolving the original polynomial-gap sequence at order M^2/n and narrowing the remaining bracket to a logarithmic gap. Checks included zero masses, empty blocks, exact homogeneity, saturation and the parent's failed channel and factorial constructions. The full frontier and proposed effective-log formula remain unproved.
UNRESOLVED BOTTLENECK: Construct shared-design, exactly normalized marked-mixture priors with realization-wise radius control, concentrated ATE separation and small full-sample divergence at the proposed radius-dependent scale, or derive the corrected scale. The corresponding radius-dependent polynomial upper bound, stochastic covariance control and all uniform transitions also require proof; the draft lists every gap.
EARLY KILL TEST: At d=n and sigma^2=log^2(en)/n, test the shared-design mixture likelihood, normalization and target concentration. A design-only divergence term should stop that proposed architecture before full proofs, preserving the original answer-open problem.
STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_discrete_ate_shrinking_heterogeneity_sharp_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The stated project promises the sharp shrinking-radius frontier, but this theorem supplies only a strict upper-envelope tightening and explicitly leaves the residual wedge (including the benchmark) open.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->

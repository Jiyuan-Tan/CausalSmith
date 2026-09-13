---
qid: panel_sblip_joint_limit_selection
spec: v1
topic: "Joint influence recursion and selection-valid path inference for LTV Synthetic-Blips panels. Fix one target unit, finite T and action set, q=1, fixed latent rank, and a finite budget-feasible path class. Conditional on deterministic LTV latent factors and assignments, let every required action-time donor cell grow proportionally to N; impose independent cross-unit sub-Gaussian innovations with bounded fourth moments, separated normalized factor/loading Grams, row-space inclusion and donor exogeneity, diffuse minimum-norm donor weights, p_N/N^(2+delta)->infinity noisy factor covariates, and a positive-definite limiting oracle covariance. Construct a covariate-row-cross-fitted orthogonal recursive SBE-PCR estimator with an explicit computable unit influence array and uniform joint root-N expansion for all target path values. Prove a multivariate Gaussian approximation and uniform consistency of covariance obtained by replaying the fitted recursion on leave-one-out residuals, including off-diagonal donor-reuse terms; then derive simultaneous path bands, an honest maximizing-path set, and the finite-Gaussian local-gap regret law. Consumer: Synthetic Blips' Korean export-insurance/loan schedule and targeting analysis. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The oracle source coefficients can be propagated exactly through the finite backward graph: each blip-node coefficient equals its donor-weighted observed-outcome coefficient minus propagated baseline and later-blip coefficients. This gives Phi_{r,N}^pi=N H_r^pi epsilon_r and Sigma_N=N sum_r H_r H_r' Var(epsilon_r). In the legal T=2 LTV witness with control, time-1 action, and time-2 action cells, the two path errors are (A,A+B-C), yielding Sigma=[[1,1],[1,3]] without cancellation. A separated rank-k spectral projector is differentiable. Row-space augmentation w'Z+xi'(X_i-X_S w), with xi estimated on opposite covariate-row folds and unit leave-out, makes the population derivative in w vanish, suggesting only nuisance-product remainders remain when p_N/N^(2+delta)->infinity. Checks found no collision with Synthetic Interventions scalar CLTs or dynamic softmax inference, and fixed spectral margins avoid projector boundary nonregularity. UNRESOLVED BOTTLENECK: Prove uniformly that the orthogonalized finite leave-one-out PCR recursion differs from its oracle version by o_P(N^(-1/2)), controlling spectral derivatives and every cross-fitted augmentation product. EARLY KILL TEST: At one rank-one equal-loading donor node with p_N=N^(2+delta), prove the augmented estimator's oracle expansion and influence-coefficient consistency uniformly; pivot if either root-N remainder fails under the stated gap and diffuseness."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: REVISE
tier_at_derivation: NA
proposal_promise_gap: "The novel feasible joint root-N expansion and replay covariance require unavailable superquadratic proxy measurements; the oracle recursion alone is settled algebra rather than the promised field contribution."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The load-bearing p_N>=ell_N N^(2+delta_0) condition is an instrumental proxy-volume strengthening; its justification gives no concrete data-generating design plausibly supplying superquadratically many suitably mixing proxy rows, and the named Korean application explicitly lacks them."
  - "Replace the proxy-growth justification with a named feasible measurement design and a quantitative proxy-count audit, or weaken the headline to a slower-rate theorem under p comparable to N and retain the frontier as the principal open question."
reusable_artifacts:
  - "discovery/proto_core.json — corrected LTV causal model, donor-invariant oracle recursion, joint influence/covariance architecture, and T=2 covariance witness."
  - "discovery/gaps.json — literature map and precise nuisance-rate bottleneck."
  - "reviews/angle0_v2.json — clear novelty assessment plus the terminal proxy-volume feasibility audit."
seeds_burned:
  - index: 0
    one_liner: "seed:joint-recursive-limit"
    reason: "Angle 0 received one coherent whole-model repair, but the same load-bearing proxy-volume defect recurred in v2."
proof_attempt_summary: |
  The proposal repaired its LTV causal identification, donor recursion, uniform class, source-model alignment, and Gram assumptions while preserving a novel joint influence and donor-reuse covariance kernel. The feasible root-N expansion nevertheless continued to require superquadratically many proxy rows; under p comparable to N, its stored remainder envelope does not vanish, and the named Korean application has no such measurements. A future topic would need a new feasible nuisance-rate theorem or a different fixed-weight projection estimand, followed by a fresh novelty review.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 7824654
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 7824654
  total_tokens_consumed: null
banked_on: "2026-09-10"
---

# panel_sblip_joint_limit_selection / v1 — Failed

**Topic.** Joint influence recursion and selection-valid path inference for LTV Synthetic-Blips panels. Fix one target unit, finite T and action set, q=1, fixed latent rank, and a finite budget-feasible path class. Conditional on deterministic LTV latent factors and assignments, let every required action-time donor cell grow proportionally to N; impose independent cross-unit sub-Gaussian innovations with bounded fourth moments, separated normalized factor/loading Grams, row-space inclusion and donor exogeneity, diffuse minimum-norm donor weights, p_N/N^(2+delta)->infinity noisy factor covariates, and a positive-definite limiting oracle covariance. Construct a covariate-row-cross-fitted orthogonal recursive SBE-PCR estimator with an explicit computable unit influence array and uniform joint root-N expansion for all target path values. Prove a multivariate Gaussian approximation and uniform consistency of covariance obtained by replaying the fitted recursion on leave-one-out residuals, including off-diagonal donor-reuse terms; then derive simultaneous path bands, an honest maximizing-path set, and the finite-Gaussian local-gap regret law. Consumer: Synthetic Blips' Korean export-insurance/loan schedule and targeting analysis. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The oracle source coefficients can be propagated exactly through the finite backward graph: each blip-node coefficient equals its donor-weighted observed-outcome coefficient minus propagated baseline and later-blip coefficients. This gives Phi_{r,N}^pi=N H_r^pi epsilon_r and Sigma_N=N sum_r H_r H_r' Var(epsilon_r). In the legal T=2 LTV witness with control, time-1 action, and time-2 action cells, the two path errors are (A,A+B-C), yielding Sigma=[[1,1],[1,3]] without cancellation. A separated rank-k spectral projector is differentiable. Row-space augmentation w'Z+xi'(X_i-X_S w), with xi estimated on opposite covariate-row folds and unit leave-out, makes the population derivative in w vanish, suggesting only nuisance-product remainders remain when p_N/N^(2+delta)->infinity. Checks found no collision with Synthetic Interventions scalar CLTs or dynamic softmax inference, and fixed spectral margins avoid projector boundary nonregularity. UNRESOLVED BOTTLENECK: Prove uniformly that the orthogonalized finite leave-one-out PCR recursion differs from its oracle version by o_P(N^(-1/2)), controlling spectral derivatives and every cross-fitted augmentation product. EARLY KILL TEST: At one rank-one equal-loading donor node with p_N=N^(2+delta), prove the augmented estimator's oracle expansion and influence-coefficient consistency uniformly; pivot if either root-N remainder fails under the stated gap and diffuseness.

**Novelty target.** field

**Stage -0.5 verdict.** REVISE

**Stage 0.5 verdict.** NA

**Banking reason.** The load-bearing p_N>=ell_N N^(2+delta_0) condition has no concrete feasible design, the named Korean application lacks the proxies, and the stored proof architecture leaves validity at or below N^2 open.

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

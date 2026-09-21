---
qid: exp_outcome_delay_inference_frontier
spec: v1
topic: "Outcome-dependent delayed-feedback phase diagram for adaptive causal contrasts. For horizons T and two arms, observe bounded iid potential outcomes under predictable logged allocation, with one prespecified arm having assignment probability comparable to t^(-alpha), alpha in [0,1), and finite arm-specific delays jointly distributed with outcomes but satisfying a known polynomial tail envelope. Determine the minimax expected-length order max{T^(-(1-alpha)/2),T^(-beta)} for uniformly honest intervals for the arm-mean contrast; prove a matching same-experiment converse, the ordinary-Wald versus hidden-tail boundary, and the attained bounded-shift Gaussian calibration. Construct a measurable two-cohort AIPW/HT procedure with an observable variance gate and concentration fallback, and show when Liberali et al.'s delayed-endpoint real-time adaptive cardiovascular-trial intervals require a tail pad or extended follow-up. PRESOLVE EVIDENCE REQUIRING VERIFICATION: An independent-arm-tape reduction and deterministic quota design yield a derived two-cohort construction: a large cohort estimates rewards revealed by age T^rho, while an early cohort estimates the newly revealed tail. The correction variance is lower order when rho beta>(1-rho)(1-alpha), leaving contrast bias at most 2L T^(-beta)(1+o(1)); rho=3/4 works at the boundary. A Rademacher hidden-sign family attains the folded-normal envelope. Checks covered adaptive stopping, nonconvergent allocation scaling, shrinking variance, infinite-delay exclusions, and collisions with Bai-Hu-Rosenberger, Lancewicki et al., and Armstrong-Kolesar. UNRESOLVED BOTTLENECK: Prove the uniform studentized two-cohort approximation, including the observable variance gate at 1/log T and its fallback, without conditioning on quota success or assuming propensity convergence. EARLY KILL TEST: Prove the fixed-quota arm-tape equivalence and the old-tail correction variance bound in a finite-support policy that switches after an early reward; pivot if it requires reward-delay independence or conditioning on recruitment success. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_outcome_delay_inference_frontier.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: null
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The delivered theorems establish matching upper and lower expected-length orders over the one-sided policy class, together with the regular-subclass ordinary-Wald boundary and an attained boundary shift; they do not establish the exact normalized minimax constant or globally optimal variable-length interval posed in oeq:exact-minimax-constant."
  - "The arm-tape proof silently infers that each current arrival vector is independent of the full past filtration, although the stated iid-arrivals assumption does not explicitly require independence from the policy's auxiliary randomization; that exogeneity condition must be stated to make the reduction valid over the declared class."
  - "These scope and practical-evidence limitations, plus the unresolved constant-efficiency problem, keep the package below the strongest leading-journal papers despite the proved rate frontier."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_one_sided_minimax_length_frontier.json
  - discovery/solve_thm_attained_boundary_calibration.json
  - discovery/solve_prop_one_sided_clinical_followup_rule.json
seeds_burned: []
proof_attempt_summary: |
  Six D0 solve rounds produced a sound exact-order minimax frontier for the one-sided
  forced-exploration class, a measurable two-cohort hybrid interval, matching sampling
  and informative-tail converses, and boundary calibration. Source auditing repaired
  the original clinical kernel substitution, but D0.5 capped the resulting package at
  subfield because exact normalized constants/global variable-length optimality remain
  open and several dependency, exogeneity, comparison, and ballast issues remain.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 34553190
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 34553190
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# exp_outcome_delay_inference_frontier / v1 — Downgraded

**Topic.** Outcome-dependent delayed-feedback phase diagram for adaptive causal contrasts. For horizons T and two arms, observe bounded iid potential outcomes under predictable logged allocation, with one prespecified arm having assignment probability comparable to t^(-alpha), alpha in [0,1), and finite arm-specific delays jointly distributed with outcomes but satisfying a known polynomial tail envelope. Determine the minimax expected-length order max{T^(-(1-alpha)/2),T^(-beta)} for uniformly honest intervals for the arm-mean contrast; prove a matching same-experiment converse, the ordinary-Wald versus hidden-tail boundary, and the attained bounded-shift Gaussian calibration. Construct a measurable two-cohort AIPW/HT procedure with an observable variance gate and concentration fallback, and show when Liberali et al.'s delayed-endpoint real-time adaptive cardiovascular-trial intervals require a tail pad or extended follow-up. PRESOLVE EVIDENCE REQUIRING VERIFICATION: An independent-arm-tape reduction and deterministic quota design yield a derived two-cohort construction: a large cohort estimates rewards revealed by age T^rho, while an early cohort estimates the newly revealed tail. The correction variance is lower order when rho beta>(1-rho)(1-alpha), leaving contrast bias at most 2L T^(-beta)(1+o(1)); rho=3/4 works at the boundary. A Rademacher hidden-sign family attains the folded-normal envelope. Checks covered adaptive stopping, nonconvergent allocation scaling, shrinking variance, infinite-delay exclusions, and collisions with Bai-Hu-Rosenberger, Lancewicki et al., and Armstrong-Kolesar. UNRESOLVED BOTTLENECK: Prove the uniform studentized two-cohort approximation, including the observable variance gate at 1/log T and its fallback, without conditioning on quota success or assuming propensity convergence. EARLY KILL TEST: Prove the fixed-quota arm-tape equivalence and the old-tail correction variance bound in a finite-support policy that switches after an early reward; pivot if it requires reward-delay independence or conditioning on recruitment success. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_outcome_delay_inference_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G graded the sound matched-rate package subfield with paper_score_ceiling 7.3 < 7.4, salvageable=false, and no bounded field-tier improvement directive.

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

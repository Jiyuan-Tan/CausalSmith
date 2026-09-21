---
qid: panel_bhar_proxy_modulus_frontier
spec: proxy_modulus_v1
topic: "Sharp rough-Holder generated-donor-proxy minimax frontier for realized-path causal buy-and-hold level wealth. Fix H, proxy dimension p, and finitely many cohorts, and restrict the constructive theory to 0<lambda<=1. Observe N donor scores, exact historical proxy paths at T pre-event sites, n_s replicated bounded untreated histories, and replicated treated event outcomes. At each fixed admissible query z_0, assume query-conditional design densities bounded above and below, geometrically beta-mixing design sequences, conditional independence of complete unit histories across replicas given the exact design, a cohort-common treated conditional mean invariant to the design, rough-Holder historical regressions, event-date transport, interior overlap, limited anticipation, no spillovers, and a uniformly elliptic full covariance for the stacked donor-error path. Determine sharp fixed-query-kernel conditional MSE and uniformly honest expected-length rates, and transfer the constructive upper conclusions to joint panel laws only for marginal-almost-every query through the labelled regular conditional tuple. The target rate has three nonredundant channels: treated replication sum_s pi_s^2/n_s, calendar-design spacing {log(T vee 2)/T}^{2lambda/d}, and generated-query uncertainty N^{-lambda}; on the independent-calendar subclass the spacing term is T^{-2lambda/d}. In the deterministic fixed-design experiment, use a nearest-site estimator with (X,z_0,Sigma) treated as known specifications; in the generated-query experiment, use one feasible observable anchor estimator and total interval chosen before the unknown donor mean, with whole-unit bounded-range concentration and matching treated, spacing, and full-covariance donor lower bounds under the stated strict-slack conditions. TARGET ADJUSTMENT FROM THE ORIGINAL PROPOSAL: local-polynomial/tensor-sieve theory for lambda>1 and calendar-block score inference are outside the proved scope; the replicated-response smoothing expression remains valid bookkeeping but is algebraically dominated by treated replication and spacing for fixed cohorts, so it is not a fourth phase; geometric design mixing incurs the displayed logarithmic spacing penalty, while the iid-design subclass has the no-log rate. PRESOLVE EVIDENCE RETAINED: in the scalar H=0 one-cohort donor subexperiment, donor means separated by order N^{-1/2} can have bounded testing distance, while admissible rough-Holder regressions separate targets by order N^{-lambda/2}, giving the N^{-lambda} MSE and N^{-lambda/2} honest-length lower channels without deconvolution. The scalar iid bookkeeping rate n^{-1} vee (Tn)^{-2lambda/(2lambda+1)} vee T^{-2lambda} vee N^{-lambda} reduces because its smoothing term is dominated. RESOLVED BOTTLENECK: exact historical training coordinates mean no deconvolution phase, whole-unit concentration removes the need for response-calendar mixing or block studentization, and explicit channelwise witnesses match the three-channel frontier. REMAINING LIMITATION: higher-order smoothness and exact phase-intersection constants require separate new arguments."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The original sharp causal panel frontier is under-delivered: actual panel laws receive identification and upper risk/coverage/length transfer, but no panel-induced converse, genuine FWL anchor, or named DID reductions."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The matched three-channel MSE and expected-length rates are proved over a bespoke union of labelled fixed-query conditional-kernel classes, not over the joint causal panel-law class."
  - "For actual panel laws, the note proves identification and transfers only the upper risk, coverage, and expected-length conclusions at marginal-almost-every query; it expressly supplies no panel-induced converse."
  - "Although declared Panel, the core defines only a labelled conditional mean contrast: it supplies neither an assignment/regression specification nor the required panel regression/FWL representation tying this estimand to a panel estimand."
  - "The main panel result lacks the required named panel reductions (homogeneous/no-carry-over or vanishing-contamination and a T=2 canonical DID or explicitly named special-case reduction)."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_conditional_frontier.json
  - discovery/solve_thm_marginal_phase_diagram.json
  - discovery/solve_thm_honest_length_frontier.json
  - reviews/review_general.json
  - reviews/review_math.json
  - reviews/review_rubric.json
seeds_burned: []
proof_attempt_summary: |
  Discovery built a sound rough-Hölder fixed-query kernel frontier with matched treated-replication,
  geometric-calendar-spacing, and generated-query channels, plus a total honest interval; the final
  mathematics referee passed with no findings. The field claim collapsed because only upper conclusions
  transfer to joint causal panel laws, while a panel-induced converse, genuine FWL anchor, and named DID
  reductions require a new model-and-proof architecture. A future re-raise should lift the explicit
  channel witnesses into admissible joint panel-law submodels and add those panel reductions.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 137905695
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-07"
---

# panel_bhar_proxy_modulus_frontier / proxy_modulus_v1 — Downgraded

**Topic.** Sharp rough-Holder generated-donor-proxy minimax frontier for realized-path causal buy-and-hold level wealth. Fix H, proxy dimension p, and finitely many cohorts, and restrict the constructive theory to 0<lambda<=1. Observe N donor scores, exact historical proxy paths at T pre-event sites, n_s replicated bounded untreated histories, and replicated treated event outcomes. At each fixed admissible query z_0, assume query-conditional design densities bounded above and below, geometrically beta-mixing design sequences, conditional independence of complete unit histories across replicas given the exact design, a cohort-common treated conditional mean invariant to the design, rough-Holder historical regressions, event-date transport, interior overlap, limited anticipation, no spillovers, and a uniformly elliptic full covariance for the stacked donor-error path. Determine sharp fixed-query-kernel conditional MSE and uniformly honest expected-length rates, and transfer the constructive upper conclusions to joint panel laws only for marginal-almost-every query through the labelled regular conditional tuple. The target rate has three nonredundant channels: treated replication sum_s pi_s^2/n_s, calendar-design spacing {log(T vee 2)/T}^{2lambda/d}, and generated-query uncertainty N^{-lambda}; on the independent-calendar subclass the spacing term is T^{-2lambda/d}. In the deterministic fixed-design experiment, use a nearest-site estimator with (X,z_0,Sigma) treated as known specifications; in the generated-query experiment, use one feasible observable anchor estimator and total interval chosen before the unknown donor mean, with whole-unit bounded-range concentration and matching treated, spacing, and full-covariance donor lower bounds under the stated strict-slack conditions. TARGET ADJUSTMENT FROM THE ORIGINAL PROPOSAL: local-polynomial/tensor-sieve theory for lambda>1 and calendar-block score inference are outside the proved scope; the replicated-response smoothing expression remains valid bookkeeping but is algebraically dominated by treated replication and spacing for fixed cohorts, so it is not a fourth phase; geometric design mixing incurs the displayed logarithmic spacing penalty, while the iid-design subclass has the no-log rate. PRESOLVE EVIDENCE RETAINED: in the scalar H=0 one-cohort donor subexperiment, donor means separated by order N^{-1/2} can have bounded testing distance, while admissible rough-Holder regressions separate targets by order N^{-lambda/2}, giving the N^{-lambda} MSE and N^{-lambda/2} honest-length lower channels without deconvolution. The scalar iid bookkeeping rate n^{-1} vee (Tn)^{-2lambda/(2lambda+1)} vee T^{-2lambda} vee N^{-lambda} reduces because its smoothing term is dominated. RESOLVED BOTTLENECK: exact historical training coordinates mean no deconvolution phase, whole-unit concentration removes the need for response-calendar mixing or block studentization, and explicit channelwise witnesses match the three-channel frontier. REMAINING LIMITATION: higher-order smoothness and exact phase-intersection constants require separate new arguments.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The matched three-channel MSE and expected-length rates are proved over a bespoke union of labelled fixed-query conditional-kernel classes, not over the joint causal panel-law class.

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

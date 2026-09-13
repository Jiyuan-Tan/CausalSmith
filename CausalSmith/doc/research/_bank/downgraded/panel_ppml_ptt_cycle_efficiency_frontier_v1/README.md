---
qid: panel_ppml_ptt_cycle_efficiency_frontier
spec: v1
topic: "Cycle-rank efficiency frontier for proportional staggered difference-in-differences. In a fixed-T staggered panel with independent units, arbitrary within-unit dependence and finite fourth moments, impose no anticipation and a positive connected multiplicative rank-one untreated-mean array mu_gt=a_g b_t. Target Moreau-Kastler's proportional treatment on the treated, theta_PTT=A/B-1. On the untreated cohort-time bipartite graph H_U let q=|U|-|C_U|-|T_U|+1. Prove that weighted alternating even-cycle vectors span the complete tangent restriction space, derive the canonical gradient and an attaining feasible covariance-weighted estimator, and differentiate the published PPML-imputation estimator. The hard theorem is topology-level: PPML imputation is efficient for every legal bounded nonnegative-outcome covariance law iff q=0. If q>0, show the universally efficient covariances satisfy exactly q independent primitive alternating balance equations, form a proper lower-dimensional subset, and construct an open realizable covariance family on which the exact loss Gamma=b'(R'Omega R)^(-1)b is strictly positive, with the sharp quadratic/spectral characterization and pointwise Wald inference. Keep the banked population PPML forbidden-comparison theorem and routine sandwich theory out of scope. Consumers are the Nagengast--Yotov regional-trade-agreement and Menkhoff--Miethe treaty/bank-deposit PPML applications. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolver derived the weighted-cycle nullspace, bounded-score tangent construction, explicit PPML coefficient, canonical gradient, and exact loss. For every cycle it perturbed Cov(Y_gt,Y_gg), obtaining a diagonal balance response -1/(B mu_gt); a positive fixed-support Rademacher density realizes the full q-dimensional covariance family while keeping means and variances fixed, so the loss is an explicit positive-definite quadratic form. Exact rational calculation reproduced the legal 3x3 witness: theta=.5, V*=.06333936, PPML variance=.06506836, and Gamma=.00172900. All 56 staggered supports through T=6 passed independent cycle-basis/response checks. Singular covariances, zero means, absent never-treated support, unrealizable perturbations, generic-GMM collapse, and the additive PT-All quotient collision were checked and excluded or placed outside scope. UNRESOLVED BOTTLENECK: Prove the general finite-fourth-moment tangent lower bound with an explicit differentiable-mean submodel convention and justify score-moment differentiation while preserving the bounded-law topology construction. EARLY KILL TEST: Reconstruct every canonical cycle and covariance-response matrix through T=6, verifying the diagonal -1/(B mu_gt) response, unchanged cycle Gram, and exact fixed-support covariances; any failure stops the topology converse. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/panel_ppml_ptt_cycle_efficiency_frontier.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "Does not establish the unrestricted Moreau--Kastler individual-level efficiency frontier or the q=0 individual-level efficiency conclusion; application-matching controls/dependence and growing-horizon theory remain outside the delivered fixed-T cohort-mean experiment."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The proof establishes only pointwise asymptotic linearity at P; equation (5) is an influence-function identity, not regularity under every local DQM path, so the claimed semiparametric-efficiency equivalence needs a fixed-strata LAN/local-alternative argument (or must be weakened to a pointwise variance comparison)."
  - "Position the main frontier explicitly against the accepted-bank panel_ppml_forbidden_comparison result (a distinct pooled-PPML contamination theorem), and remove or give relevance sentences for the otherwise unused Wooldridge1999 and SantAnnaZhao2020 bibliography entries."
  - "Delivered tier subfield < floor field; not salvageable within scope."
reusable_artifacts:
  - "discovery/core.json — complete weighted-cycle tangent graph, canonical-gradient construction, rank-q exceptional covariance characterization, and source-repaired fixed-strata CLT proof"
  - "discovery/solve_thm_realizable_quadratic_loss.json — bounded positive-law covariance perturbation and strict-loss construction"
  - "discovery/solve_prop_individual_aggregation_bridge.json — exact balanced-intersection bridge to the Moreau--Kastler individual estimator"
  - "discovery/writeup.tex — fixed-T derivation note and exact three-period witness"
seeds_burned: []
proof_attempt_summary: |
  The run established the fixed-T cohort-mean cycle geometry, canonical bound and attaining estimator,
  exact codimension-q exceptional covariance laws, and bounded realizable strict-loss witnesses; it also
  proved q>0 nonuniversality for the Moreau--Kastler estimator on the exact balanced intersection. The
  field-tier claim collapsed because the unrestricted individual-level frontier, q=0 individual result,
  application-matching controls/dependence, and growing-horizon theory were not delivered; a local-DQM
  regularity argument and related-work cleanup also remain before reusing the strongest efficiency wording.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 50234375
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 50234375
  total_tokens_consumed: null
banked_on: "2026-09-12"
---

# panel_ppml_ptt_cycle_efficiency_frontier / v1 — Downgraded

**Topic.** Cycle-rank efficiency frontier for proportional staggered difference-in-differences. In a fixed-T staggered panel with independent units, arbitrary within-unit dependence and finite fourth moments, impose no anticipation and a positive connected multiplicative rank-one untreated-mean array mu_gt=a_g b_t. Target Moreau-Kastler's proportional treatment on the treated, theta_PTT=A/B-1. On the untreated cohort-time bipartite graph H_U let q=|U|-|C_U|-|T_U|+1. Prove that weighted alternating even-cycle vectors span the complete tangent restriction space, derive the canonical gradient and an attaining feasible covariance-weighted estimator, and differentiate the published PPML-imputation estimator. The hard theorem is topology-level: PPML imputation is efficient for every legal bounded nonnegative-outcome covariance law iff q=0. If q>0, show the universally efficient covariances satisfy exactly q independent primitive alternating balance equations, form a proper lower-dimensional subset, and construct an open realizable covariance family on which the exact loss Gamma=b'(R'Omega R)^(-1)b is strictly positive, with the sharp quadratic/spectral characterization and pointwise Wald inference. Keep the banked population PPML forbidden-comparison theorem and routine sandwich theory out of scope. Consumers are the Nagengast--Yotov regional-trade-agreement and Menkhoff--Miethe treaty/bank-deposit PPML applications. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolver derived the weighted-cycle nullspace, bounded-score tangent construction, explicit PPML coefficient, canonical gradient, and exact loss. For every cycle it perturbed Cov(Y_gt,Y_gg), obtaining a diagonal balance response -1/(B mu_gt); a positive fixed-support Rademacher density realizes the full q-dimensional covariance family while keeping means and variances fixed, so the loss is an explicit positive-definite quadratic form. Exact rational calculation reproduced the legal 3x3 witness: theta=.5, V*=.06333936, PPML variance=.06506836, and Gamma=.00172900. All 56 staggered supports through T=6 passed independent cycle-basis/response checks. Singular covariances, zero means, absent never-treated support, unrealizable perturbations, generic-GMM collapse, and the additive PT-All quotient collision were checked and excluded or placed outside scope. UNRESOLVED BOTTLENECK: Prove the general finite-fourth-moment tangent lower bound with an explicit differentiable-mean submodel convention and justify score-moment differentiation while preserving the bounded-law topology construction. EARLY KILL TEST: Reconstruct every canonical cycle and covariance-response matrix through T=6, verifying the diagonal -1/(B mu_gt) response, unchanged cycle Gram, and exact fixed-support covariances; any failure stops the topology converse. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/panel_ppml_ptt_cycle_efficiency_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** Delivered tier subfield below novelty_target field (paper_score_ceiling 7.2 < 7.4); not salvageable within scope.

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

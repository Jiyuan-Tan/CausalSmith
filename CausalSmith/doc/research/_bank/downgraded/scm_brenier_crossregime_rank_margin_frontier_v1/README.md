---
qid: scm_brenier_crossregime_rank_margin_frontier
spec: v1
topic: "Exact Euclidean rank-preservation and sharp rank-margin inference for multivariate Brenier counterfactual mechanisms; use the full queued specification and unverified presolve draft at <repo-root>/internal/presolve_drafts/scm_brenier_crossregime_rank_margin_frontier.md"
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: null
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The exact population Hessian characterizations and the fixed-support testing lower bound are proved, but probability-calibrated rank-margin inference is not: the raw-Hessian band, coverage, power, and matching upper separation rate are obtained only after assuming the entire analytic and stochastic argument they require."
  - "Unconditionally, the paper has only a one-sided lower rate under a strict-slack class-constant qualification plus deterministic conclusions on an event whose probability is unproved."
  - "The absent feasible upper procedure and class-uniform evidence are the principal constraints on the projected paper score."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_prop_dynamic_ot_counterexample.json
  - discovery/solve_thm_cyclic_frontier.json
  - discovery/solve_thm_sharp_separation_lower.json
  - discovery/solve_prop_finite_negative_certificate.json
seeds_burned: []
proof_attempt_summary: |
  The run established exact Euclidean and cyclic cross-Hessian criteria, an unconditional
  counterexample to the published strict-monotonicity implication, deterministic event-to-band and
  finite-certificate results, and a fixed-support lower separation rate with a nonvacuous strict-slack
  family. The field contract collapsed because the uniform raw-Hessian probability envelope and its
  matching upper testing rate still require the unresolved endpoint-response, wavelet, Green-kernel,
  nonlinear-remainder, and concentration program; the cold review found no bounded in-scope repair.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 55209833
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 55209833
  total_tokens_consumed: null
banked_on: "2026-09-10"
---

# scm_brenier_crossregime_rank_margin_frontier / v1 — Downgraded

**Topic.** Exact Euclidean rank-preservation and sharp rank-margin inference for multivariate Brenier counterfactual mechanisms; use the full queued specification and unverified presolve draft at <repo-root>/internal/presolve_drafts/scm_brenier_crossregime_rank_margin_frontier.md

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** The exact population Hessian criteria, counterexample, deterministic certificates, and fixed-support lower rate survive, but probability-calibrated rank-margin inference and the matching upper frontier remain conditional on the unresolved endpoint-response and Green-kernel program.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

The deterministic geometry, explicit ellipsoid counterexample, fixed-support Le Cam construction,
and event-to-certificate argument are the reusable core. A follow-on should not rerun those pieces;
it must first supply the missing class-uniform endpoint-response and influence-kernel estimates before
claiming probability-calibrated Hessian bands or a matching statistical frontier.

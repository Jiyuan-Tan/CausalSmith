---
qid: exp_rollout_carryover_endpoint_design
spec: v1
topic: "PRESOLVE EVIDENCE REQUIRING VERIFICATION: In a finite-population rollout with p_0=0 and stages t=1,...,T, assume lag-one carryover and a secular polynomial trend of explicitly declared degree r; the mean-design row is [1,t,...,t^r,p_t,p_{t-1}] and the target is the direct-plus-carryover contrast c. Prove identification if and only if c lies in row(X), derive the minimum-variance linear unbiased representer, and characterize the least number and placement of endpoint-support stages. The legal r=1 witness uses t=1,...,4 and p=(0,0,1/2,1): det(X)=1/4 and w=(2,-2,-2,2) satisfies X' w=(0,0,1,1). A linear ramp p_t=t/4 has deficient treatment-column rank and a target-active null direction. LinkedIn's documented deterministic hash assignment and multi-stage ramp workflows are the consumer; the theorem would certify schedule sufficiency, not claim platform implementation. UNRESOLVED BOTTLENECK: Generalize the row-space certificate to arbitrary declared trend degree and carryover lag, prove a sharp minimal-support design theorem, and obtain finite-population risk without silently treating repeated rollout stages as independent samples. Require explicit nonidentification schedules at each support deficit and state all endpoint conventions. EARLY KILL TEST: Drop if the determinant or weight identity fails, if every legal nonconstant ramp automatically identifies c, or if existing rollout-with-carryover theory already gives the same necessary-and-sufficient minimal-support characterization."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "It does not deliver the requested general minimum-variance representer: the oracle weight is defined by a quadratic-program argmin, with no general solution or optimal schedule characterization beyond a singleton example."
  - "The variance displays are exact identities for selected Horvitz–Thompson estimators, not efficiency bounds or a matched minimax risk frontier."
  - "The unrestricted bounded-class minimax frontier is a new open problem, not a scoped D0 repair with a demonstrated matching lower bound."
  - "The published-class transfer is unavailable without adding hypotheses or changing the estimand/design, which would not be faithful."
reusable_artifacts:
  - "discovery/writeup.tex — fixed-schedule threshold-block span certificate, sharp horizon/wave support frontiers, plateau witness, and shared-hash variance identities"
  - "discovery/core.json — typed theorem graph and synchronized metadata"
  - "discovery/literature_map.md — scoped comparisons with rollout, carryover, and design-based panel work"
  - "reviews/review_general.json — field-tier boundary and bounded minimax-risk upgrade requirement"
seeds_burned: []
proof_attempt_summary: |
  Discovery proved a rule-wide threshold-block span criterion for exact identification under arbitrary fixed schedules and observed-wave sets, derived sharp measurement-support frontiers, and retained exact shared-hash dependence in the risk identities. The result remained subfield because the field-tier upgrade requires an unrestricted bounded-class minimax risk frontier with a matching lower bound; the available singular-BLUE formula and restricted one-wave calculation are supporting or estimator-class-specific results, while transfer to a published class would change the hypotheses, design, or estimand.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 51786072
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-05"
---

# exp_rollout_carryover_endpoint_design / v1 — Downgraded

**Topic.** PRESOLVE EVIDENCE REQUIRING VERIFICATION: In a finite-population rollout with p_0=0 and stages t=1,...,T, assume lag-one carryover and a secular polynomial trend of explicitly declared degree r; the mean-design row is [1,t,...,t^r,p_t,p_{t-1}] and the target is the direct-plus-carryover contrast c. Prove identification if and only if c lies in row(X), derive the minimum-variance linear unbiased representer, and characterize the least number and placement of endpoint-support stages. The legal r=1 witness uses t=1,...,4 and p=(0,0,1/2,1): det(X)=1/4 and w=(2,-2,-2,2) satisfies X' w=(0,0,1,1). A linear ramp p_t=t/4 has deficient treatment-column rank and a target-active null direction. LinkedIn's documented deterministic hash assignment and multi-stage ramp workflows are the consumer; the theorem would certify schedule sufficiency, not claim platform implementation. UNRESOLVED BOTTLENECK: Generalize the row-space certificate to arbitrary declared trend degree and carryover lag, prove a sharp minimal-support design theorem, and obtain finite-population risk without silently treating repeated rollout stages as independent samples. Require explicit nonidentification schedules at each support deficit and state all endpoint conventions. EARLY KILL TEST: Drop if the determinant or weight identity fails, if every legal nonconstant ramp automatically identifies c, or if existing rollout-with-carryover theory already gives the same necessary-and-sufficient minimal-support characterization.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The fixed-schedule threshold-block identification and sharp measurement-support frontier are mathematically sound, but the unrestricted bounded-class minimax frontier needed for field tier is a new open problem and published-class transfer is unavailable without changing hypotheses, design, or estimand.

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

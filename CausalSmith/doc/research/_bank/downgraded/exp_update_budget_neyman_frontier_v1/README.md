---
qid: exp_update_budget_neyman_frontier
spec: v1
topic: "Sharp policy-update budget frontier for adaptive Neyman allocation. For n binary Gaussian experimental units, exact-count batches with treatment share in [1/4,3/4], compact nondegenerate arm-variance box, and deterministic normalized weights on batchwise mean differences, define the exactly-B normalized excess-MSE frontier above the constrained oracle variance. Characterize it for every 1<=B<=floor(n/4), derive the at-most-B lower envelope and operational saturation regime, prove matching adaptive schedules and chronological information lower bounds, solve the one- and two-batch anchors, and derive a variance estimator, CLT, and fixed-time Wald coverage. The Amazon adaptive-abtester update cadence is the consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: the exact risk decomposition reduces design loss to batch-weight mismatch plus allocation regret; adaptive Fisher information, van Trees, grid quantization, and harmonic weight optimization support Psi_exact,B asymptotic to B((n+1)^(1/B)-1)/n+(B/n)^2. A legal square-root pilot attains the matching two-batch exponent, while B=n/4 reveals a genuine exact-batch overscheduling penalty; the at-most-B envelope reaches order log(n)/n. UNRESOLVED BOTTLENECK: prove the sharp chronological Gaussian learning constant and matching logarithmic-batch construction needed for the literal factor-two saturation threshold; rate bounds alone do not settle that constant. EARLY KILL TEST: on sigma(theta)=(s exp(theta),s exp(-theta)), derive exact adaptive-history information 2T and test whether one smooth prior yields the claimed sharp cumulative allocation-loss coefficient; failure pivots the factor-two claim to an unspecified constant-factor threshold. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_update_budget_neyman_frontier.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: null
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The note proves a two-sided constant-factor rate characterization of the exactly-B and at-most-B frontiers, not a sharp leading-constant frontier."
  - "The exact saturation factor A=2, the limit of n Psi_infty(n)/log n, and an exact two-batch minimax rule remain open."
  - "The contribution is also confined to Gaussian outcomes, exact-count batches, deterministic schedules, and deterministic batch-contrast weights; the comparison with broader adaptive-design games is therefore conceptual rather than a transfer theorem."
  - "The Amazon connection supplies no implementation study or quantitative operational validation."
  - "Panel findings left unrepaired (the tier, not these, is the reason for the halt): redundant-assumption@ass:parameter-box, ballast@prop:exact-b-phase-diagram, related_work@thm:uniform-wald."
reusable_artifacts:
  - "discovery/core.json — typed theorem graph for the matched every-B rate frontier, exact anchors, phase diagram, and Wald result."
  - "discovery/solve_tex/solve_thm_envelope_overscheduling.tex — derivation of the two-elbow exact-B overscheduling phase diagram."
  - "discovery/proto_core.json — repaired observed-law and adaptive-policy formulation used before the final D0 solve."
seeds_burned:
  - index: 0
    one_liner: "seed:exact-b-frontier"
    reason: "The sole proposal angle was revised through well-posedness and maximality checks, but the cold field-tier gate found no bounded same-topic repair across the 0.4 score gap."
proof_attempt_summary: |
  Discovery repaired the sampling-law and adaptive-policy definitions, proved the constant-factor every-B and at-most-B rate frontier, checked the one-batch minimax anchor, and added the logarithmic and compulsory-batching elbows. The result stopped at D0.5 because the field-level promise required a sharp chronological learning constant, literal factor-two saturation, or an exact two-batch minimax rule; those remain open, while the unrepaired panel findings concern redundant scope, duplicated exposition, and incomplete related-work positioning rather than a false theorem.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 14693814
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 14693814
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# exp_update_budget_neyman_frontier / v1 — Downgraded

**Topic.** Sharp policy-update budget frontier for adaptive Neyman allocation. For n binary Gaussian experimental units, exact-count batches with treatment share in [1/4,3/4], compact nondegenerate arm-variance box, and deterministic normalized weights on batchwise mean differences, define the exactly-B normalized excess-MSE frontier above the constrained oracle variance. Characterize it for every 1<=B<=floor(n/4), derive the at-most-B lower envelope and operational saturation regime, prove matching adaptive schedules and chronological information lower bounds, solve the one- and two-batch anchors, and derive a variance estimator, CLT, and fixed-time Wald coverage. The Amazon adaptive-abtester update cadence is the consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: the exact risk decomposition reduces design loss to batch-weight mismatch plus allocation regret; adaptive Fisher information, van Trees, grid quantization, and harmonic weight optimization support Psi_exact,B asymptotic to B((n+1)^(1/B)-1)/n+(B/n)^2. A legal square-root pilot attains the matching two-batch exponent, while B=n/4 reveals a genuine exact-batch overscheduling penalty; the at-most-B envelope reaches order log(n)/n. UNRESOLVED BOTTLENECK: prove the sharp chronological Gaussian learning constant and matching logarithmic-batch construction needed for the literal factor-two saturation threshold; rate bounds alone do not settle that constant. EARLY KILL TEST: on sigma(theta)=(s exp(theta),s exp(-theta)), derive exact adaptive-history information 2T and test whether one smooth prior yields the claimed sharp cumulative allocation-loss coefficient; failure pivots the factor-two claim to an unspecified constant-factor threshold. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_update_budget_neyman_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G tier=subfield < floor=field and NOT salvageable in scope; the delivered result is a matched constant-factor frontier, while sharp leading constants, literal factor-two saturation, and the exact two-batch minimax rule remain open.

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

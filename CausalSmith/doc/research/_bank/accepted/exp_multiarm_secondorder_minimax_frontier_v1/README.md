---
qid: exp_multiarm_secondorder_minimax_frontier
spec: v1
topic: "Derive the exact 2^K-response-type minimax game for fixed K>=3 binary-potential-outcome contrasts under unrestricted designs and estimators. Prove C0=(sum_a |c_a|)^2/4 and determine the second-order exponent. Establish the universal Theta(n^(-4/3)) improvement using an explicit contrast-weighted clipped-shrinkage rule and an unrestricted embedded two-arm converse; give exact-rational finite-program procedure/prior certificates for rational contrasts and continuity-transfer certificates for every real contrast. Characterize the remaining sharp frontier—convergence, exact constant or subsequential set, second-order optimality of q*, optimizer/prior convergence, and any face/corner HJB, spectral, separable, or other limiting operator—as explicit unresolved questions. Include the K=3 c=(1,-1/2,-1/2) n<=5 showcase and ACTG 175 consumer."
novelty_target: field
banked_novelty_tier: field
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: null
reusable: unknown
reraise_status: unknown
gap_reasons:
  - "No promised conjecture collapsed; the sharp constant, convergence, optimizer/prior convergence, and limiting face/corner operator were explicitly scoped as unresolved frontier questions."
reusable_artifacts:
  - "Causalean/Mathlib/Optimization/RationalLP.lean — promoted general exact rational LP primal/dual attainment substrate."
  - "Causalean/Mathlib/Topology/SubsequentialLimits.lean — promoted general subsequential-limit and compact-cluster-set substrate."
  - "CausalSmith/Experimentation/EXP_MultiarmSecondorderMinimaxFrontier_Research/Helpers/RationalLPBridge.lean — run-specific exact grid-program bridge and rational certificates."
  - "CausalSmith/Experimentation/EXP_MultiarmSecondorderMinimaxFrontier_Research/Helpers/K3FullDataWitness.lean — exact K=3 full-data witness and risk certificate."
seeds_burned: []
proof_attempt_summary: |
  The run formalized the exact response-type orbit game, first-order saddle value, universal n^(-4/3) improvement, embedded two-arm converse, and exact-rational finite certificates, with all delivered nodes passing dual-model convergence review and Lean verification. Manual de-laundering repaired inconsistent cited-scope carriers and one generated-instance docstring without weakening the mathematical claims. The exact support-at-least-three second-order constant, convergence behavior, optimizer/prior limits, and limiting face/corner operator remain deliberately open.
token_usage:
  complete: false
  orchestrator_tokens: 5467800
  pipeline_codex_tokens: 1067380045
  pipeline_claude_tokens: 264523896
  total_tokens_consumed: null
banked_on: "2026-09-02"
---

# exp_multiarm_secondorder_minimax_frontier / v1 — Accepted

**Topic.** Derive the exact 2^K-response-type minimax game for fixed K>=3 binary-potential-outcome contrasts under unrestricted designs and estimators. Prove C0=(sum_a |c_a|)^2/4 and determine the second-order exponent. Establish the universal Theta(n^(-4/3)) improvement using an explicit contrast-weighted clipped-shrinkage rule and an unrestricted embedded two-arm converse; give exact-rational finite-program procedure/prior certificates for rational contrasts and continuity-transfer certificates for every real contrast. Characterize the remaining sharp frontier—convergence, exact constant or subsequential set, second-order optimality of q*, optimizer/prior convergence, and any face/corner HJB, spectral, separable, or other limiting operator—as explicit unresolved questions. Include the K=3 c=(1,-1/2,-1/2) n<=5 showcase and ACTG 175 consumer.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** F5 completed with a green Lean build, complete 548-object crosswalk, dual-model F4 convergence, and field-tier D0.5 acceptance.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

F7 promoted the run-independent exact rational-LP attainment theorem to
`Causalean/Mathlib/Optimization/RationalLP.lean` and the compact
subsequential-limit theorem to
`Causalean/Mathlib/Topology/SubsequentialLimits.lean`. The experiment now
imports those shared results through thin, run-specific bridges. Orbit/grid
encoding, K=3 witnesses, and certificate assembly remain local because their
interfaces are specific to this research question.

The sharp second-order constant, convergence of the scaled deficit,
optimizer/prior convergence, and any limiting face/corner operator remain
open. They are documented frontier questions, not claims established by this
banked run.

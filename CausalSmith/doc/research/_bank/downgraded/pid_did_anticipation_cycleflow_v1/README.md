---
qid: pid_did_anticipation_cycleflow
spec: v1
topic: "Sharp cycle-flow bounds for coupled comparison-cohort anticipation. In finite staggered adoption under PT-All, let pre-adoption means satisfy mu_ht=alpha_h+lambda_t+a_ht, with a_ht zero outside known anticipation horizons and bounded inside them. Characterize the sharp joint fiber by the fundamental cycles of the cohort-time graph; prove a causal completion theorem for every compatible mean vector; give necessary and sufficient variation-independence and box-endpoint exactness frontiers; compute arbitrary ATT-aggregate endpoints using interval-tension feasibility and min-cost circulation; and construct finite-sample honest outer confidence sets by jointly optimizing simultaneous bounded-mean bands. The consumer is the Callaway-Sant'Anna not-yet-treated risk-set workflow for announced staggered policies, including the Indonesian anti-cheating rollout. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Orienting the cohort-time graph gives an incidence matrix B and a cycle matrix C with ker(C)=im(B^T), so compatibility reduces to C_U a_U=C mu after clean coordinates are fixed. The presolver derived the affine dimension, component gauges, interval-tension feasibility certificate, and a min-cost-transshipment dual for every linear support function. It also derived that full primitive-box variation independence holds exactly when every positive-width uncertain edge is a bridge, subject to fixed-cycle compatibility. The checked three-cohort witness forces a_43-a_53=1/2 and tightens the equal-weight bias range from [-1,1] to [-3/4,3/4]. Disconnected graphs, zero-width edges, forests, infeasible means, arbitrary ATT weights, and active-face changes produced no counterexample; Fenaroli's staggered analysis leaves anticipatory not-yet-treated comparisons open. UNRESOLVED BOTTLENECK: Prove the causal sharpness/completion lemma embedding every cycle-compatible mean vector in one announced-policy staggered-adoption potential-outcome law that simultaneously supports all overlapping risk-set estimands and maintained outcome bounds. EARLY KILL TEST: Exhaustively enumerate bipartite graphs through three cohorts by three periods, including disconnected and zero-width cases, and compare direct rational-LP feasibility and support values with the negative-cycle and circulation formulations; any mismatch stops or pivots the run."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "missing_manski_corner@prop:known-corners: explicit no-restriction/vacuous-Manski reduction is absent"
  - "The delivered contribution remains a narrow exact analysis of a purpose-built class rather than a field-level resolution of coupled anticipation in the published workflow."
  - "The result therefore remains subfield-tier under the SAME-assumptions constraint."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_causal_completion.json
  - discovery/solve_thm_circulation_endpoints.json
  - discovery/solve_tex/solve_thm_causal_completion.tex
  - discovery/solve_tex/solve_thm_circulation_endpoints.tex
  - reviews/review_general.json
seeds_burned: []
proof_attempt_summary: |
  The run proved the cycle-fiber, bridge frontier, negative-cycle certificate, a
  common-law causal completion theorem, sharp ATT region, circulation endpoints,
  and fixed-weight finite-sample outer coverage under its proposal-specific PT-All
  class. The field claim collapsed because published not-yet-treated risk-set
  assumptions do not preserve that cycle-flow kernel; replacing PT-All produces
  weighted hyperedges, while the remaining external Manski benchmark would repair
  a corner check but cannot raise the result above subfield tier.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 31745457
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-08"
---

# pid_did_anticipation_cycleflow / v1 — Downgraded

**Topic.** Sharp cycle-flow bounds for coupled comparison-cohort anticipation. In finite staggered adoption under PT-All, let pre-adoption means satisfy mu_ht=alpha_h+lambda_t+a_ht, with a_ht zero outside known anticipation horizons and bounded inside them. Characterize the sharp joint fiber by the fundamental cycles of the cohort-time graph; prove a causal completion theorem for every compatible mean vector; give necessary and sufficient variation-independence and box-endpoint exactness frontiers; compute arbitrary ATT-aggregate endpoints using interval-tension feasibility and min-cost circulation; and construct finite-sample honest outer confidence sets by jointly optimizing simultaneous bounded-mean bands. The consumer is the Callaway-Sant'Anna not-yet-treated risk-set workflow for announced staggered policies, including the Indonesian anti-cheating rollout. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Orienting the cohort-time graph gives an incidence matrix B and a cycle matrix C with ker(C)=im(B^T), so compatibility reduces to C_U a_U=C mu after clean coordinates are fixed. The presolver derived the affine dimension, component gauges, interval-tension feasibility certificate, and a min-cost-transshipment dual for every linear support function. It also derived that full primitive-box variation independence holds exactly when every positive-width uncertain edge is a bridge, subject to fixed-cycle compatibility. The checked three-cohort witness forces a_43-a_53=1/2 and tightens the equal-weight bias range from [-1,1] to [-3/4,3/4]. Disconnected graphs, zero-width edges, forests, infeasible means, arbitrary ATT weights, and active-face changes produced no counterexample; Fenaroli's staggered analysis leaves anticipatory not-yet-treated comparisons open. UNRESOLVED BOTTLENECK: Prove the causal sharpness/completion lemma embedding every cycle-compatible mean vector in one announced-policy staggered-adoption potential-outcome law that simultaneously supports all overlapping risk-set estimands and maintained outcome bounds. EARLY KILL TEST: Exhaustively enumerate bipartite graphs through three cohorts by three periods, including disconnected and zero-width cases, and compare direct rational-LP feasibility and support values with the negative-cycle and circulation formulations; any mismatch stops or pivots the run.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The delivered contribution remains a narrow exact analysis of a purpose-built class rather than a field-level resolution of coupled anticipation in the published workflow.

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

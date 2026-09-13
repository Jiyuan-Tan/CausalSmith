---
qid: scm_selpag_delta_closed_fiber
spec: v1
topic: "Closed-margin sharp compatibility fibers for selection-PAG interventions. Given a finite COPAG, a positive rational selected law q, a bounded outcome h, and delta>0, characterize all SCMs whose selected MAG lies in the COPAG, P(V=v,S=1)=rho q(v), rho in [delta,1], and P(S=1|do(B=b))>=delta. Prove a graph-legal finite response representation, compactness and attained algebraic extrema, give elementary complexity bounds, and develop confidence-fiber inference. Use the binary saturated B circle-A witness with q=(1,2,3,4)/10, delta=1/4 and sharp interval [1/20,39/40]; Lee et al.'s survivor-selected cardiac-surgery FCI/LV-IDA analysis is the consumer. Distinguish Evans canonicalization, Rosset-Gisin-Wolfe cardinality, Duarte finite disturbance models, Yang PAG models, and Carey selected-marginalized graphs. PRESOLVE EVIDENCE REQUIRING VERIFICATION: For the saturated finite COPAG, presolve derives the exact interval [h_min+delta sum_{B=b}q(h-h_min), h_max-delta sum_{B=b}q(h_max-h)] with one-source attained endpoints and finite-sample coverage. Source merging by child set gives H<=2^N-1, and fixed-slot moment preservation gives K<=m+3; legality is retained when q is faithful. Exact arithmetic verifies the five-type witness and independent 32-response optimization. A positive XOR support-deletion example shows that moment preservation alone need not preserve actual edges, although an equal-moment legal lift exists. Checks included zero-width outcomes, vacuous interventions, delta endpoints, latent-child-set merging, shared normalization, graph deletion, and nearby canonicalization results without finding a full collision. UNRESOLVED BOTTLENECK: Prove compact exact-graph canonicalization and graph-legal lifting of limiting moments for every positive, potentially unfaithful q. EARLY KILL TEST: Settle the lifting lemma on a binary three-observed-variable COPAG with a compelled collider using essential-parent polynomial strata; an unattained closure endpoint with no legal lift kills the general theorem. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_selpag_delta_closed_fiber.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The exact positive-unfaithful COPAG compatibility fiber is not shown closed, finitely representable, or endpoint-attaining; equality with the bounded finite image remains open as universal legal lifting."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The compiler characterizes only the enumerated bounded finite legal image, while the promised all-SCM sharp fiber is expressly left open; reframe the headline and deliverable to that bounded object (or prove the lifting property)."
  - "The exact positive-unfaithful COPAG compatibility fiber is not shown closed, finitely representable, or endpoint-attaining; all such conclusions for the full arbitrary-SCM class remain conditional on oeq:universal-legal-lifting."
  - "This is a genuine kernel substitution relative to the accepted topic, despite the manuscript now disclosing the substitution honestly."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_saturated_closed_form.json
  - discovery/solve_thm_certified_attainment_procedure.json
  - discovery/solve_thm_compact_algebraic_fiber.json
  - discovery/solve_thm_confidence_fiber.json
seeds_burned: []
proof_attempt_summary: |
  The run built an exact semialgebraic compiler for an enumerated bounded finite response-SCM image, a saturated closed-form benchmark with attained endpoint witnesses, and certified finite-branch optimization machinery. The field-level claim collapsed because sourcewise moment compression was not shown to preserve strict actual-graph legality, so the bounded image was never proved equal to the promised arbitrary-SCM COPAG fiber. The remaining load-bearing problem is oeq:universal-legal-lifting for positive, potentially unfaithful selected laws.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 31705441
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 31705441
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# scm_selpag_delta_closed_fiber / v1 — Failed

**Topic.** Closed-margin sharp compatibility fibers for selection-PAG interventions. Given a finite COPAG, a positive rational selected law q, a bounded outcome h, and delta>0, characterize all SCMs whose selected MAG lies in the COPAG, P(V=v,S=1)=rho q(v), rho in [delta,1], and P(S=1|do(B=b))>=delta. Prove a graph-legal finite response representation, compactness and attained algebraic extrema, give elementary complexity bounds, and develop confidence-fiber inference. Use the binary saturated B circle-A witness with q=(1,2,3,4)/10, delta=1/4 and sharp interval [1/20,39/40]; Lee et al.'s survivor-selected cardiac-surgery FCI/LV-IDA analysis is the consumer. Distinguish Evans canonicalization, Rosset-Gisin-Wolfe cardinality, Duarte finite disturbance models, Yang PAG models, and Carey selected-marginalized graphs. PRESOLVE EVIDENCE REQUIRING VERIFICATION: For the saturated finite COPAG, presolve derives the exact interval [h_min+delta sum_{B=b}q(h-h_min), h_max-delta sum_{B=b}q(h_max-h)] with one-source attained endpoints and finite-sample coverage. Source merging by child set gives H<=2^N-1, and fixed-slot moment preservation gives K<=m+3; legality is retained when q is faithful. Exact arithmetic verifies the five-type witness and independent 32-response optimization. A positive XOR support-deletion example shows that moment preservation alone need not preserve actual edges, although an equal-moment legal lift exists. Checks included zero-width outcomes, vacuous interventions, delta endpoints, latent-child-set merging, shared normalization, graph deletion, and nearby canonicalization results without finding a full collision. UNRESOLVED BOTTLENECK: Prove compact exact-graph canonicalization and graph-legal lifting of limiting moments for every positive, potentially unfaithful q. EARLY KILL TEST: Settle the lifting lemma on a binary three-observed-variable COPAG with a compelled collider using essential-parent polynomial strata; an unattained closure endpoint with no legal lift kills the general theorem. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_selpag_delta_closed_fiber.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The compiler characterizes only the enumerated bounded finite legal image, while the promised all-SCM sharp fiber is expressly left open.

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

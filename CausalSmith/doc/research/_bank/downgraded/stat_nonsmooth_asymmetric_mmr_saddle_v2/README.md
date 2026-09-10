---
qid: stat_nonsmooth_asymmetric_mmr_saddle
spec: v2
topic: "Face-complete endpoint-prior saddles and the answer-open indexability correspondence for asymmetric nonsmooth partial identification: solve the compact non-centrosymmetric polyhedral Gaussian endpoint game over all measurable randomized rules; characterize every saddle, classify the full optimal correspondence into all one-index, coexistence, or no one-index cases, construct convergent primal-dual certificates without a complexity-rate claim, and prove tie-uniform perturbation plus LAN/Le Cam transfer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: a legal 2D witness has value 2/3 and both constant one-index and tanh-perturbed non-one-index optima. UNRESOLVED BOTTLENECK: a non-tautological general indexability criterion. EARLY KILL TEST: interval certification of an unbalanced-prior non-halfspace case."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "No explicit rational unbalanced-prior interval certificate or two-dimensional impossibility theorem was produced; the primitive indexability classifier and realized no-index witness remain open."
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  - "The delivered kernel leaves the advertised primitive all/coexistence/none classifier open; conditional curved-score implication is not a realized no-index frontier."
  - "Neither an explicit rational unbalanced-prior interval certificate nor a two-dimensional impossibility theorem is present in, or derivable from, the frozen primitives."
  - "The tested rational candidate fails because b(pi) <= 1/3 < 3/7 <= v."
reusable_artifacts:
  - "discovery/core.json"
  - "discovery/writeup.tex"
  - "discovery/solve_oeq_unbalanced_no_index_witness.json"
  - "discovery/solve_tex/solve_oeq_unbalanced_no_index_witness.tex"
  - "discovery/solve_prop_conditional_tie_uniform_transfer.json"
  - "discovery/solve_thm_complete_saddle_duality.json"
seeds_burned: []
proof_attempt_summary: |
  The run established a sound compact asymmetric Gaussian endpoint-game core: unrestricted
  saddle duality, convergent exchange certificates, and an exact coexistence example. A final
  scoped construction attempted to realize the no-one-index branch with a rational unbalanced
  prior and exact global interval/tail/curvature certificates, but its candidate was not least
  favorable and no replacement or impossibility theorem was obtained. The primitive
  all/coexistence/none criterion and a realized no-index witness therefore remain open.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 66405952
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-07"
---

# stat_nonsmooth_asymmetric_mmr_saddle / v2 — Downgraded

**Topic.** Face-complete endpoint-prior saddles and the answer-open indexability correspondence for asymmetric nonsmooth partial identification: solve the compact non-centrosymmetric polyhedral Gaussian endpoint game over all measurable randomized rules; characterize every saddle, classify the full optimal correspondence into all one-index, coexistence, or no one-index cases, construct convergent primal-dual certificates without a complexity-rate claim, and prove tie-uniform perturbation plus LAN/Le Cam transfer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: a legal 2D witness has value 2/3 and both constant one-index and tanh-perturbed non-one-index optima. UNRESOLVED BOTTLENECK: a non-tautological general indexability criterion. EARLY KILL TEST: interval certification of an unbalanced-prior non-halfspace case.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The delivered kernel leaves the advertised primitive all/coexistence/none classifier open; conditional curved-score implication is not a realized no-index frontier.

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

---
qid: exp_graphon_indirect_honest_length_frontier
spec: v1
topic: "Finite-sample conditional certification and a same-class minimax lower benchmark for one-network graphon indirect derivatives. In the Li--Wager finite-rank sparse-graphon subclass with Bernoulli(1/2) assignment, anonymous treated-neighbor-fraction interference, known response and C3 radii B and L, and C_log log n <= d=o(n), target the realized finite-population midpoint indirect derivative. Construct the exact degree-adaptive discrete score, a polynomial-time first-Hoeffding-projection PC-balanced estimator, and a graph-observable finite-sample conditional confidence interval with explicit bias and bounded-difference variance certificates retaining isolates. Prove exact score moments and first two Hoeffding projections, the graph-conditional isolate wall, and same-class linear, local C3-bump, and degree-lattice lower bounds whose supported analytic envelope has graph-floor, interior, and lattice phases for minimax absolute risk and interval expected length. Establish a lower-upper bracket using the conservative feasible envelope; do not claim that the feasible envelope matches the lower benchmark, a sharp minimax or honest expected-length rate, or an achieved frontier. Leave a rate-sharp feasible PC construction at logarithmic degree open."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REVISE
proposal_promise_gap: "kernel_substituted"
reusable: solver_blocked
reraise_status: true-negative
gap_reasons:
  - "The note proves a same-class three-component minimax lower benchmark and a computable conditionally honest interval, but it never bounds the interval's feasible envelope by the analytic lower envelope."
  - "The title's honest length frontier is not delivered: what is established is a conservative finite-sample procedure plus a nonmatching lower benchmark for a distinct target on the note's maintained class."
  - "Two supported response configurations that agree on all nonisolates and assign respectively +1 and -1 to every isolate induce exactly the same conditional observed-data law, yet their targets differ by 2B I_0(A)/n."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/d0_working.json
  - reviews/reviews.jsonl
  - orchestrator/decision_log.jsonl
seeds_burned: []
proof_attempt_summary: |
  The run derived exact degree-adaptive lattice-score moments and Hoeffding
  projections, a polynomial-time graph-adaptive PC-balanced interval with
  finite-sample conditional coverage, and same-class graph, interior-bump,
  and lattice lower benchmarks. The requested matched field-level frontier
  collapsed because conditional isolate indistinguishability forces a linear
  isolate radius, while the feasible positive-degree certificate remains too
  coarse; closing either gap requires a redesigned problem or new substrate.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 154782262
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-05"
---

# exp_graphon_indirect_honest_length_frontier / v1 — Downgraded

**Topic.** Finite-sample conditional certification and a same-class minimax lower benchmark for one-network graphon indirect derivatives. In the Li--Wager finite-rank sparse-graphon subclass with Bernoulli(1/2) assignment, anonymous treated-neighbor-fraction interference, known response and C3 radii B and L, and C_log log n <= d=o(n), target the realized finite-population midpoint indirect derivative. Construct the exact degree-adaptive discrete score, a polynomial-time first-Hoeffding-projection PC-balanced estimator, and a graph-observable finite-sample conditional confidence interval with explicit bias and bounded-difference variance certificates retaining isolates. Prove exact score moments and first two Hoeffding projections, the graph-conditional isolate wall, and same-class linear, local C3-bump, and degree-lattice lower bounds whose supported analytic envelope has graph-floor, interior, and lattice phases for minimax absolute risk and interval expected length. Establish a lower-upper bracket using the conservative feasible envelope; do not claim that the feasible envelope matches the lower benchmark, a sharp minimax or honest expected-length rate, or an achieved frontier. Leave a rate-sharp feasible PC construction at logarithmic degree open.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REVISE

**Banking reason.** D0.5 tier=subfield below field: sound finite-sample conditional certification and same-class lower benchmark, but no matched feasible honest-length frontier; isolate indistinguishability blocks the directed lift.

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

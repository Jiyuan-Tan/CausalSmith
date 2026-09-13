---
qid: exp_adaptive_qte_anytime_regret_frontier
spec: v1
topic: "Allocation-regret and LIL-width frontier for anytime whole-curve QTE inference, with the presolve capsule embedded in this queued entry."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: REVISE
tier_at_derivation: NA
proposal_promise_gap: null
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  - "N-pub: MineiroHoward2023 already covers the importance-weighted running conditional CDF whose deterministic-potential-outcome specialization is F_{a,t}; armwise inversion and subtraction give the asserted anytime QTE band."
  - "N-mischar: The core attributes coverage to MineiroHoward2023 Theorem 3.4 and calls absence of an off-policy regression nuisance a strict simplification, but Theorem 3.1 supplies coverage, Theorem 3.4 is a smoothness-conditional width result, and the paper importance-weighted construction itself uses only (W_t,X_t)."
  - "C-assumption-nonstandard: The cited DaiGraduHarshaw2023 source does not support the displayed uniform sup-norm condition: its Assumption 1 imposes bounded second/fourth prefix moments, while Definition 1 defines the Neyman ratio."
reusable_artifacts:
  - discovery/proto_core.json
  - discovery/gaps.json
  - reviews/angle0_v6.json
  - orchestrator/decision_log.jsonl
seeds_burned: []
proof_attempt_summary: |
  Six D-0.5 proposal versions developed the functional-LIL converse and two-quantile Phi frontier, repaired observability and domain issues, and performed a whole-core bibliography/comparator audit. The run exhausted its sole extra revision when load-bearing source-to-claim fidelity defects recurred, so the validity gate prohibited another localized repair. The mathematical kernel remains a plausible field-tier retry, but no D0 derivation or Lean formalization was attempted in this run.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 21922970
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 21922970
  total_tokens_consumed: null
banked_on: "2026-09-10"
---

# exp_adaptive_qte_anytime_regret_frontier / v1 — Failed

**Topic.** Allocation-regret and LIL-width frontier for anytime whole-curve QTE inference, with the presolve capsule embedded in this queued entry.

**Novelty target.** field

**Stage -0.5 verdict.** REVISE

**Stage 0.5 verdict.** NA

**Banking reason.** D-0.5 revision cap exhausted after recurring source-to-claim fidelity failures following a whole-core audit and the sole extra revision; validity gate ruled further local repair prohibited rotation.

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

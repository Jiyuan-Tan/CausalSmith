---
qid: exp_block_adaptive_ot_variance_envelope
spec: v1
topic: "Identify the nodewise-exact rectangular predictable AIPW quadratic-variation envelope under growing block-adaptive complete randomization; provide two-arm sorting and a fixed-K LP, history-uniform observable plug-in rates over the general moment class and the bounded-residual q_n^{-1/2} subclass, and conservative martingale Wald coverage from the rectangular upper endpoint under explicit predictable-QV stabilization, together with a fixed-fraction no-discount certificate on a nonadaptive fixed-quota subclass. Do not claim that one globally consistent adaptive-history completion attains independently chosen nodewise optimizers."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: retry
gap_reasons:
  - "The source-free CLT and sharper rate are mathematically viable, but the atomic transaction cannot land while its CLT edit is stale, and the actual regenerated proof bytes are malformed."
  - "The TeX seal has demonstrated false negatives for nested dollar math in text, ensuremath, and non-allowlisted math environments, plus a false positive for valid mbox prose."
  - "Required Stage 0 suite passed 315/315 and separate TypeScript checking passed, but audit PASS is mandatory; no further repair or resume is authorized."
reusable_artifacts:
  - discovery/proto_core.json
  - discovery/d0_working.json
  - discovery/writeup.tex
  - discovery/gaps.json
  - reviews/reviews.jsonl
  - orchestrator/decision_log.jsonl
seeds_burned: []
proof_attempt_summary: |
  The D0 derivation developed the nodewise rectangular envelope, fixed-K transport/LP
  characterization, plug-in rates, source-free martingale CLT route, conservative Wald
  result, and fixed-fraction witness, but the atomic CLT replacement repeatedly carried
  a stale cited-view revision and regenerated proof payloads contained malformed TeX.
  A bounded pipeline repair made the revision/catalog boundary sound, yet its TeX seal
  failed the mandatory independent inverse audit, so the run was not resumed or formalized.
  The mathematical target remains a retry candidate; no Lean theorem was delivered.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 99157420
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-05"
---

# exp_block_adaptive_ot_variance_envelope / v1 — Failed

**Topic.** Identify the nodewise-exact rectangular predictable AIPW quadratic-variation envelope under growing block-adaptive complete randomization; provide two-arm sorting and a fixed-K LP, history-uniform observable plug-in rates over the general moment class and the bounded-residual q_n^{-1/2} subclass, and conservative martingale Wald coverage from the rectangular upper endpoint under explicit predictable-QV stabilization, together with a fixed-fraction no-discount certificate on a nonadaptive fixed-quota subclass. Do not claim that one globally consistent adaptive-history completion attains independently chosen nodewise optimizers.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** Supervisor-bounded pipeline repair remained NOT_SOUND: the revision boundary was repaired, but the TeX seal retained demonstrated context false positives and false negatives; no further repair or resume was authorized.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

The terminal classification records an exhausted supervisor-authorized pipeline repair,
not a mathematical refutation. Future work should reuse the typed core and D0 receipts,
but must first replace the ad-hoc TeX context recognizer with an independently audited
balanced scanner before replaying the exact-target transaction.

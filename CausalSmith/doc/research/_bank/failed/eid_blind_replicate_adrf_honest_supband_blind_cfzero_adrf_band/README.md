---
qid: eid_blind_replicate_adrf_honest_supband
spec: blind_cfzero_adrf_band
topic: "Blind replicated continuous-treatment ADRF identification and qualitative honest simultaneous bands over a compatible nonempty fixed class. Under finite strata, compact dose support, a bounded structural response surface, Sobolev radii beta>1/2, overlap, and independent nonidentical asymmetric replicate errors with a uniform q_e>1 moment bound and possible open spectral zeros, prove analytic-cocycle identification of f_x, q_x, and mu(a)=sum_x P(X=x)q_x(a)/f_x(a). Construct finite-dimensional semi-infinite constrained-sieve and parallel exact-class bands with uniform simultaneous 1-alpha coverage, width at most 2B_Y, and uniformly o(1) expected maximal width. No finite decision algorithm, explicit O(r_n) rate, minimax match, or unconditional converse is claimed; the quantitative protected-cube inverse and fixed-nuisance Bernoulli packet remain open."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: null
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "Delivered tier=incremental below novelty_target=field (floor=field)."
  - "The note proves identification of f_x, q_x, and the ADRF, plus abstract exact-class and semi-infinite finite-sieve bands with uniform honesty and only o(1) expected maximal width. It does not prove the advertised candidate r_n rate or any unconditional converse."
  - "The math panel returned revise and its findings were never repaired, so this note is NOT established as mathematically sound — do not bank it as downgraded on this verdict alone."
  - "Directive round 15 is atomic; no PR opened because unit failure(s) left the directive incomplete; solve JSON invalid at proposed_assumptions[0].not_crux (expected string, received boolean); cap reached on an incomplete round."
reusable_artifacts:
  - "discovery/core.json — versioned theorem graph containing the analytic-cocycle identification and qualitative exact/finite-sieve band program."
  - "discovery/vcs/ — complete 77-plus-commit derivation history, including corrected source attestations for Capitao et al. and Low (1997)."
  - "orchestrator/decision_log.jsonl — maximality, assumption, citation, below-floor, and soundness-repair adjudications."
  - "logs/pr_eb082cb6774d_adjudication_verbatim.txt — audited explicit bump/product-law nonemptiness witness and dependency-repair specification for a future re-anchored run."
  - "logs/d05_below_floor_boundary_consult_verbatim.txt — terminal novelty assessment and unrepaired-panel inventory."
seeds_burned: []
proof_attempt_summary: |
  Six initial D0 rounds replaced the unsupported sharp r_n claim with analytic-cocycle identification and qualitative uniformly honest bands whose expected maximal width is o(1), while leaving the quantitative protected-cube inverse and fixed-nuisance Bernoulli modulus explicitly open. D0.5 assessed that delivered package as incremental below the field floor and also found five bounded soundness/framing defects. A validity-gated repair developed an explicit nonempty bump/product-law witness and structural-response rewiring, but its one authorized corrective redispatch exhausted rounds 12–15 with malformed semantic and TeX output before a sound PR or mathematical re-review could land.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 87077297
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 87077297
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# eid_blind_replicate_adrf_honest_supband / blind_cfzero_adrf_band — Failed

**Topic.** Blind replicated continuous-treatment ADRF identification and qualitative honest simultaneous bands over a compatible nonempty fixed class. Under finite strata, compact dose support, a bounded structural response surface, Sobolev radii beta>1/2, overlap, and independent nonidentical asymmetric replicate errors with a uniform q_e>1 moment bound and possible open spectral zeros, prove analytic-cocycle identification of f_x, q_x, and mu(a)=sum_x P(X=x)q_x(a)/f_x(a). Construct finite-dimensional semi-infinite constrained-sieve and parallel exact-class bands with uniform simultaneous 1-alpha coverage, width at most 2B_Y, and uniformly o(1) expected maximal width. No finite decision algorithm, explicit O(r_n) rate, minimax match, or unconditional converse is claimed; the quantitative protected-cube inverse and fixed-nuisance Bernoulli packet remain open.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** Field novelty was terminal below floor, and the only authorized bounded soundness repair exhausted its cap with invalid semantic and TeX output before mathematical review could pass; downgraded banking was therefore unauthorized.

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

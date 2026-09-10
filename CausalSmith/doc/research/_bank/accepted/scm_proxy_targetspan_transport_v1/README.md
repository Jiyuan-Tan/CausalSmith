---
qid: scm_proxy_targetspan_transport
spec: v1
topic: "Target-span completeness for rank-deficient proxy transport. In a strictly positive finite latent-shift SCM E→U→{W,X}, with Y allowed to depend on U,W,X, source law P(E,W,X,Y), target proxy law Q(W), invariant mechanisms, and unknown full-column-rank proxy channel M=P(W|U), prove for every x that Q(Y|do(x)) is identified iff Q(W) belongs to col(B_x), B_x=P(W|E,x). On success prove every lambda solving B_x lambda=Q(W) yields the same functional P(Y|E,x)lambda. On failure construct two strictly positive SCMs agreeing on the entire supplied source and target laws but differing on the intervention law. Add Anderson–Rubin-style projection confidence sets robust to weak rank. Consumer: Iglesias-Alonso et al.'s Expedia hotel-ranking analysis. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolver derived B_x=M R_x, c_x=g_x^T R_x, and theta_x=g_x^T q. Injectivity of M gives the success functional and solution independence. Outside the span, a proxy-stratum-specific left-null perturbation preserves every source joint cell while changing the target effect; exact rational checks covered all 24 cells of paired positive countermodels and the supplied deficient-rank success witness. It also checked incomplete proxies, deterministic outcome boundaries, signed weights, other treatment arms, and abstract nullspace/source-span collisions. UNRESOLVED BOTTLENECK: Identification is derived, but uniform studentized Anderson–Rubin calibration under diverging balancing weights and degenerate covariance remains open; the causal novelty must also survive exact comparison with Zhang Proposition 2.3 and Rahiminasab Theorem 3. EARLY KILL TEST: Compare the proved converse line-by-line with those two results and stop if either already implies the identical deficient-source-rank SCM iff with full-joint-law countermodels. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_proxy_targetspan_transport.md."
novelty_target: field
banked_novelty_tier: field
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: null
reusable: unknown
reraise_status: unknown
gap_reasons: []
reusable_artifacts:
  - discovery/writeup.tex
  - formalization/crosswalk_full.json
  - orchestrator/substrate_requirements/rank_one_spectral_projector_smoothness/requirement.md
seeds_burned: []
proof_attempt_summary: |
  The run proved the target-span identification equivalence, solution independence,
  a strictly positive full-law converse, finite-sample projection coverage, and the
  impossibility of uniformly studentized Wald adaptation. The final proof used the
  promoted rank-one spectral-projector and pseudoinverse smoothness substrate; all
  graph obligations were delivered with no added assumptions, gates, or sorry axioms.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 190366788
  pipeline_claude_tokens: 101504166
  total_tokens_consumed: null
banked_on: "2026-09-06"
---

# scm_proxy_targetspan_transport / v1 — Accepted

**Topic.** Target-span completeness for rank-deficient proxy transport. In a strictly positive finite latent-shift SCM E→U→{W,X}, with Y allowed to depend on U,W,X, source law P(E,W,X,Y), target proxy law Q(W), invariant mechanisms, and unknown full-column-rank proxy channel M=P(W|U), prove for every x that Q(Y|do(x)) is identified iff Q(W) belongs to col(B_x), B_x=P(W|E,x). On success prove every lambda solving B_x lambda=Q(W) yields the same functional P(Y|E,x)lambda. On failure construct two strictly positive SCMs agreeing on the entire supplied source and target laws but differing on the intervention law. Add Anderson–Rubin-style projection confidence sets robust to weak rank. Consumer: Iglesias-Alonso et al.'s Expedia hotel-ranking analysis. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolver derived B_x=M R_x, c_x=g_x^T R_x, and theta_x=g_x^T q. Injectivity of M gives the success functional and solution independence. Outside the span, a proxy-stratum-specific left-null perturbation preserves every source joint cell while changing the target effect; exact rational checks covered all 24 cells of paired positive countermodels and the supplied deficient-rank success witness. It also checked incomplete proxies, deterministic outcome boundaries, signed weights, other treatment arms, and abstract nullspace/source-span collisions. UNRESOLVED BOTTLENECK: Identification is derived, but uniform studentized Anderson–Rubin calibration under diverging balancing weights and degenerate covariance remains open; the causal novelty must also survive exact comparison with Zhang Proposition 2.3 and Rahiminasab Theorem 3. EARLY KILL TEST: Compare the proved converse line-by-line with those two results and stop if either already implies the identical deficient-source-rank SCM iff with full-joint-law countermodels. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_proxy_targetspan_transport.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** CKPT 2 approved by supervisor after clean F5: full build, source scan, five headline axiom audits, dual F4 convergence, empty assumption/debt audit, and field-tier recommendation.

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

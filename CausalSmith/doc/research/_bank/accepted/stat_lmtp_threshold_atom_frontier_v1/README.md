---
qid: stat_lmtp_threshold_atom_frontier
spec: v1
topic: "Honest minimax risk and confidence-length frontier for noninvertible threshold modified-treatment policies under polynomial generalized-propensity thinning. On the fixed finite-stratum Holder model, prove the exact natural-course-plus-Dirac decomposition, let h solve n h^(2 beta+1)(delta+h)^kappa asymptotic to one, and establish the sharp rate n^(-1/2)+delta^(kappa+1)h^beta with its regular, critical, atom-dominated, and fixed-threshold regimes. Construct a total-Gram-stabilized local-polynomial atom estimator and bias-aware uniformly honest interval attaining the rate for every declared threshold sequence, and prove matching same-class global-shift and localized-Bernoulli lower bounds. Use the official lmtp threshold-policy workflow as consumer and do not smooth or replace the target. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The target equals an observable natural-course mean plus q_x(delta)mu_x(delta), with q_x(delta) asymptotic to delta^(kappa+1). Local information is n h(delta+h)^kappa, so Holder bias-variance balance gives the stated scale. For beta=kappa=1, pi(a)=2a yields h=(n delta)^(-1/3), KL of order n delta h^3, target separation delta^2h, and transition delta=n^(-1/10). Searches found threshold policies explicitly excluded from published LMTP EIF theory although the package accepts user policies. UNRESOLVED BOTTLENECK: Prove a uniform realized-design total-Gram lemma, under only two-sided polynomial density bounds, controlling exact local-polynomial l1/l2 weights and the singular-Gram fallback probability tightly enough for honest O(r_n) expected length over all deterministic delta sequences. EARLY KILL TEST: In the one-cell beta=kappa=1 class with arbitrary measurable density c_-a<=pi(a)<=c_+a, prove those weight and bad-event bounds and a finite-sample honest interval of length O(n^-1/2+delta^2h); pivot or stop if propensity smoothness is unavoidable."
novelty_target: field
banked_novelty_tier: field
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: "kernel_substituted"
reusable: solver_blocked
reraise_status: unknown
gap_reasons:
  - "The proved order bounds do not select a deterministic split sequence or establish a joint sharp limit experiment. Fixed-design convex-modulus theory also does not settle uniform honesty of the zero-totalized radius, the moving random design under a merely measurable polynomial density envelope, or the three mixed regular-plus-local matching limits."
reusable_artifacts:
  - "CausalSmith/Stat/STAT_LmtpThresholdAtomFrontier_Research/Helpers/TotalGram.lean"
  - "CausalSmith/Stat/STAT_LmtpThresholdAtomFrontier_Research/Helpers/LocalWindowGram.lean"
  - "CausalSmith/Stat/STAT_LmtpThresholdAtomFrontier_Research/Helpers/CausalBridgeMeasure.lean"
  - "discovery/core.json"
  - "formalization/crosswalk_full.json"
seeds_burned: []
proof_attempt_summary: |
  The run proved the matched minimax-risk and uniformly honest expected-length orders, the four-regime phase diagram, exact causal transport for the declared full-data class, and the continuity-only frontier. It also formalized the total-Gram construction and supporting lower/upper-bound machinery without sorries or project axioms. The exact asymptotic minimax constant, honesty of the explicit zero-totalized modulus interval, adaptation, and broader longitudinal or flexible-covariate extensions remain open.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 547628276
  pipeline_claude_tokens: 114316472
  total_tokens_consumed: null
banked_on: "2026-09-06"
paper_score: 6.2
paper_score_rationale: "The paper establishes a potentially valuable and formally verified minimax frontier, but substantial revisions are needed to clarify the theorem scope, identify the implemented tuning choices, document reproducibility, streamline the presentation, and establish novelty against the closest literature."
---

# stat_lmtp_threshold_atom_frontier / v1 — Accepted

**Topic.** Honest minimax risk and confidence-length frontier for noninvertible threshold modified-treatment policies under polynomial generalized-propensity thinning. On the fixed finite-stratum Holder model, prove the exact natural-course-plus-Dirac decomposition, let h solve n h^(2 beta+1)(delta+h)^kappa asymptotic to one, and establish the sharp rate n^(-1/2)+delta^(kappa+1)h^beta with its regular, critical, atom-dominated, and fixed-threshold regimes. Construct a total-Gram-stabilized local-polynomial atom estimator and bias-aware uniformly honest interval attaining the rate for every declared threshold sequence, and prove matching same-class global-shift and localized-Bernoulli lower bounds. Use the official lmtp threshold-policy workflow as consumer and do not smooth or replace the target. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The target equals an observable natural-course mean plus q_x(delta)mu_x(delta), with q_x(delta) asymptotic to delta^(kappa+1). Local information is n h(delta+h)^kappa, so Holder bias-variance balance gives the stated scale. For beta=kappa=1, pi(a)=2a yields h=(n delta)^(-1/3), KL of order n delta h^3, target separation delta^2h, and transition delta=n^(-1/10). Searches found threshold policies explicitly excluded from published LMTP EIF theory although the package accepts user policies. UNRESOLVED BOTTLENECK: Prove a uniform realized-design total-Gram lemma, under only two-sided polynomial density bounds, controlling exact local-polynomial l1/l2 weights and the singular-Gram fallback probability tightly enough for honest O(r_n) expected length over all deterministic delta sequences. EARLY KILL TEST: In the one-cell beta=kappa=1 class with arbitrary measurable density c_-a<=pi(a)<=c_+a, prove those weight and bad-event bounds and a finite-sample honest interval of length O(n^-1/2+delta^2h); pivot or stop if propensity smoothness is unavoidable.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** Supervisor-approved clean F5: field-tier D0.5 pass, full source build, zero sorry/admit/declared axiom, and headline/support axiom audit clean.

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

---
qid: exp_psrr_entrance_diffusion_ate
spec: v1
topic: "For original equal-allocation pair-switching rerandomization on bounded finite-population triangular arrays, with fixed covariate dimension, fixed positive Mahalanobis threshold, finite Metropolis tuning, and nondegenerate outcome residual variance, derive the joint allocation-chain functional limit and its first-entry stopping law without assuming Markovian projected scores, stabilization, or outcome-residual independence. Prove that terminal standardized covariate imbalance is a radially clipped Gaussian, independent of a stationary Gaussian outcome-residual component, and that fixed tuning affects the proposal-time search clock but not the first-order terminal law. Establish stopped-design consistency of observed-arm projection moments and construct a computable variance-envelope critical value yielding sequencewise asymptotically conservative finite-population ATE intervals under heterogeneous effects; also derive the fully interacted adjusted corollary. Do not replace the original first-entry algorithm by its stationary or rejection-corrected variants, and do not claim shrinking thresholds, growing dimension, unequal arms, or finite-sample exactness. PRESOLVE EVIDENCE REQUIRING VERIFICATION: An all-pairs coupling keeps the search path o_p(1) in arm empirical averages from a stationary uniform shadow over n-scaled horizons, and an exact antisymmetric-score identity cancels the Metropolis acceptance kink without assuming an empirical-law limit; exact absorption and cube-generator checks support the predicted drift, diffusion, radial entrance, and the necessity of variance-envelope critical values. UNRESOLVED BOTTLENECK: Prove trajectory-uniform predictable-characteristic bounds and assemble joint functional convergence, opposite-pair proposal-clock conversion, compact containment, martingale-problem uniqueness, and continuous first-hit transfer for the generally non-Markov projected scores. EARLY KILL TEST: Prove the localized actual-filtration characteristic lemma at a=1 for gamma=1 and 10 while stress-testing the six-row zero-correlation witness; pivot if an order-one residual term survives or any extra empirical-distribution or initialization assumption is needed. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_psrr_entrance_diffusion_ate.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "The delivered package is restricted to bounded fixed-dimensional, fixed-threshold, equal-allocation PSRR and worst-compatible-residual conservative inference; it does not cover the full Zhu--Liu domain or identify residual variance, establish efficiency/optimality, or provide finite-sample validity."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The delivered result is a functional limit, first-entry law, clipped-Gaussian endpoint, and conservative ATE inference theorem for the bounded fixed-dimension, fixed-threshold, equal-allocation subclass, not for the full Zhu--Liu algorithmic domain."
  - "The inference result proves sequencewise asymptotic coverage through a worst-compatible-residual envelope; it neither identifies the residual variance nor establishes efficiency, optimality, or finite-sample validity."
  - "Panel findings left unrepaired (the tier, not these, is the reason for the halt): scope_leak@lem:covariate-path-characteristics-and-clock, clock_horizon_gap@lem:actual-path-arm-uniformity, undeclared_cited_substrate@lem:regular-tail-wellposedness, undeclared_cited_substrate@lem:initial-score-clt, undeclared_dependency@lem:all-pairs-coupling-clock, undeclared_dependency@thm:radial-entrance-law-design-class, negative-target-unspecified@prop:not-uniform-rerandomization-design-class, related-work-omission@thm:joint-stopped-functional-limit-two-class."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_joint_stopped_functional_limit_two_class.json
  - discovery/solve_tex/solve_thm_joint_stopped_functional_limit_two_class.tex
  - discovery/solve_thm_ate_limit.json
  - discovery/solve_tex/solve_thm_ate_limit.tex
seeds_burned: []
proof_attempt_summary: |
  D0 derived the actual-filtration predictable characteristics, joint stopped diffusion,
  clipped-Gaussian entrance law, proposal/accepted-clock comparison, heterogeneous-effect
  ATE limit, stopped-moment consistency, and variance-envelope inference; the Li--Ding
  balanced-allocation vector CLT citation was independently verified from the authors'
  arXiv source. D0.5 stopped at triage because the fixed-dimensional, fixed-threshold,
  equal-allocation regular subclass and worst-compatible-residual envelope cap the package
  at subfield tier, below the field floor. The listed dependency, scope, clock-horizon,
  negative-target, and related-work findings were intentionally left unrepaired once the
  tier was found unsalvageable within scope and must be resolved before reusing these claims.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 28050303
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 28050303
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# exp_psrr_entrance_diffusion_ate / v1 — Downgraded

**Topic.** For original equal-allocation pair-switching rerandomization on bounded finite-population triangular arrays, with fixed covariate dimension, fixed positive Mahalanobis threshold, finite Metropolis tuning, and nondegenerate outcome residual variance, derive the joint allocation-chain functional limit and its first-entry stopping law without assuming Markovian projected scores, stabilization, or outcome-residual independence. Prove that terminal standardized covariate imbalance is a radially clipped Gaussian, independent of a stationary Gaussian outcome-residual component, and that fixed tuning affects the proposal-time search clock but not the first-order terminal law. Establish stopped-design consistency of observed-arm projection moments and construct a computable variance-envelope critical value yielding sequencewise asymptotically conservative finite-population ATE intervals under heterogeneous effects; also derive the fully interacted adjusted corollary. Do not replace the original first-entry algorithm by its stationary or rejection-corrected variants, and do not claim shrinking thresholds, growing dimension, unequal arms, or finite-sample exactness. PRESOLVE EVIDENCE REQUIRING VERIFICATION: An all-pairs coupling keeps the search path o_p(1) in arm empirical averages from a stationary uniform shadow over n-scaled horizons, and an exact antisymmetric-score identity cancels the Metropolis acceptance kink without assuming an empirical-law limit; exact absorption and cube-generator checks support the predicted drift, diffusion, radial entrance, and the necessity of variance-envelope critical values. UNRESOLVED BOTTLENECK: Prove trajectory-uniform predictable-characteristic bounds and assemble joint functional convergence, opposite-pair proposal-clock conversion, compact containment, martingale-problem uniqueness, and continuous first-hit transfer for the generally non-Markov projected scores. EARLY KILL TEST: Prove the localized actual-filtration characteristic lemma at a=1 for gamma=1 and 10 while stress-testing the six-row zero-correlation witness; pivot if an order-one residual term survives or any extra empirical-distribution or initialization assumption is needed. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_psrr_entrance_diffusion_ate.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** Delivered tier subfield < floor field; not salvageable within scope.

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

---
qid: stat_hir_policy_dimension_phase
spec: v1
topic: "Proportional-dimensional HIR regret phase transition in a binary randomized trial. Let p/n tend to kappa in a compact subset of (0,1/2), q be standard Gaussian in R^p, A be Bernoulli(1/2), and Y be binary with arm-invariant mean expit(gamma q_1), gamma bounded away from zero. Compare maximizers over ||theta||<=R sqrt(p) of the fixed-lambda KL-regularized logistic policy objective estimated by known-propensity IPW, exact same-coordinate entropy-balanced IPW, and oracle DR. Derive their deterministic population-regret limits through a finite fixed-point/resolvent system; characterize the exact pooled-target balance-feasibility threshold and the positive/zero/negative HIR-dividend cells, including radius saturation; give plug-in phase inference away from boundaries. Consumer: high-dimensional targeting reanalyses of Ashraf-Karlan-Yin's commitment-savings trial. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The beta=theta/sqrt(p) reduction makes regret a strictly increasing function of the fitted norm, while row-sign symmetrization makes the entire true-IPW optimization law independent of gamma. A deformed-orthant calculation gives the pooled-target exact-balance threshold kappa_bal approximately 0.3043687064, rather than the naive Wendel value. Fixed-dimensional score variances are 1/8 for true IPW, 1/16 for entropy balance, and E[m(1-m)]/4 for oracle DR, so balance yields only a partial efficient-score projection. Valid finite fits show entropy-balance improvement at kappa 0.05 and 0.15 but reversal at 0.27; small policy radii create equal-regret saturation cells. Current primary and internal checks found no joint-regret collision. UNRESOLVED BOTTLENECK: Prove a joint deterministic equivalent with globally unique selected norms for the same-sample entropy tilts and nonconcave KL-policy optimizer, retaining tilt-policy overlaps and Jacobian response terms. EARLY KILL TEST: At gamma=1 and kappa=1/8, prove concentration of the exact same-sample entropy-balanced quadratic identity and recover its small-kappa coefficient; pivot if coherent leverage terms prevent finite closure. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_hir_policy_dimension_phase.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The promised proportional same-sample deterministic system and nonempty HIR phase diagram were not proved; the banked package instead delivers the exact balance threshold, entropy quadratic bounds, and fixed-dimensional regret ordering."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The proportional deterministic norm system, global selector certificate, HIR sign cells, radius boundaries, and unconditional classifier remain open."
  - "The advertised proportional-dimensional HIR regret phase transition is not proved: the note establishes neither deterministic regret limits nor any positive, zero, or negative dividend cell, ranking reversal, or radius boundary."
reusable_artifacts:
  - "discovery/core.json — maximized honest theorem graph, including the exact pooled balance threshold and fixed-dimensional regret ordering."
  - "discovery/solve_prop_quadratic_identity.json — endogenous entropy-weight quadratic decomposition, feasible-side energy floor, and small-aspect bracket attempt."
  - "discovery/writeup.tex — rendered mathematical note with verified source attestations."
  - "reviews/review_general.json — final incremental-tier assessment and the precise missing proportional-regime kernel."
seeds_burned: []
proof_attempt_summary: |
  The run attempted a same-sample augmented cavity/resolvent analysis retaining entropy-tilt response terms and a global certificate for the nonconcave policy selector. It proved the exact pooled-target feasibility threshold, finite-sample entropy quadratic identities and bounds, and strict fixed-dimensional limiting-regret ordering, but could not close the proportional deterministic equivalent or exhibit certified HIR sign/radius cells. The unresolved joint phase system is therefore recorded openly, and the sound remainder is banked at incremental tier.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 39898348
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 39898348
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# stat_hir_policy_dimension_phase / v1 — Downgraded

**Topic.** Proportional-dimensional HIR regret phase transition in a binary randomized trial. Let p/n tend to kappa in a compact subset of (0,1/2), q be standard Gaussian in R^p, A be Bernoulli(1/2), and Y be binary with arm-invariant mean expit(gamma q_1), gamma bounded away from zero. Compare maximizers over ||theta||<=R sqrt(p) of the fixed-lambda KL-regularized logistic policy objective estimated by known-propensity IPW, exact same-coordinate entropy-balanced IPW, and oracle DR. Derive their deterministic population-regret limits through a finite fixed-point/resolvent system; characterize the exact pooled-target balance-feasibility threshold and the positive/zero/negative HIR-dividend cells, including radius saturation; give plug-in phase inference away from boundaries. Consumer: high-dimensional targeting reanalyses of Ashraf-Karlan-Yin's commitment-savings trial. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The beta=theta/sqrt(p) reduction makes regret a strictly increasing function of the fitted norm, while row-sign symmetrization makes the entire true-IPW optimization law independent of gamma. A deformed-orthant calculation gives the pooled-target exact-balance threshold kappa_bal approximately 0.3043687064, rather than the naive Wendel value. Fixed-dimensional score variances are 1/8 for true IPW, 1/16 for entropy balance, and E[m(1-m)]/4 for oracle DR, so balance yields only a partial efficient-score projection. Valid finite fits show entropy-balance improvement at kappa 0.05 and 0.15 but reversal at 0.27; small policy radii create equal-regret saturation cells. Current primary and internal checks found no joint-regret collision. UNRESOLVED BOTTLENECK: Prove a joint deterministic equivalent with globally unique selected norms for the same-sample entropy tilts and nonconcave KL-policy optimizer, retaining tilt-policy overlaps and Jacobian response terms. EARLY KILL TEST: At gamma=1 and kappa=1/8, prove concentration of the exact same-sample entropy-balanced quadratic identity and recover its small-kappa coefficient; pivot if coherent leverage terms prevent finite closure. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_hir_policy_dimension_phase.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The proportional deterministic norm system, global selector certificate, HIR sign cells, radius boundaries, and unconditional classifier remain open.

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

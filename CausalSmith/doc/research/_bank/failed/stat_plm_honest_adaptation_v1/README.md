---
qid: stat_plm_honest_adaptation
spec: v1
topic: "Honest adaptation to weak non-Gaussianity in structure-agnostic partially linear inference. In the bounded/sub-Gaussian JMS partially linear class with eta independent of X, unit variance, supplied L8 nuisance errors epsilon_g,n and epsilon_q,n, require one interval to be honest over the union of eta exactly Gaussian and |kappa_4(eta)|>=delta_n. Characterize the coordinatewise Pareto lower boundary of Gaussian and non-Gaussian worst-case expected lengths. With s_n=n^-1/2+epsilon_g,n^4, d_n=n^-1/2+epsilon_g,n epsilon_q,n and B_n=n^-1/2+epsilon_g,n^3 epsilon_q,n+epsilon_g,n^4, construct a split cumulant-test plus unnormalized DML/cubic-ACE inversion attaining (d_n,min{d_n,B_n/delta_n}) when delta_n/s_n diverges. Prove matching branch-designated fuzzy-Hermite lower bounds: below s_n no shortening from d_n, and above it strict shortening occurs exactly when B_n/delta_n=o(d_n). Retain any necessary Gaussian logarithms. Do not claim improvement of global union-supremum length; use the vector frontier as the rate-level object, recognizing that the absolute cross-modulus is symmetric and fixed positive-weight scalarizations are rate-degenerate. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolve derived the exact unnormalized DML bias identity E[(Y-qhat)(T-ghat)]-theta_0=E[(ghat-g_0)(qhat-q_0)], the cubic identity E[eta(eta^3-3eta-kappa_3)]=kappa_4, and a split test/intersection construction with non-Gaussian length at most B_n/delta_n+d_n(s_n/delta_n)^2. It solved epsilon_g=epsilon_q=delta_n=n^-1/8, giving lengths n^-1/4 and n^-3/8, and checked the Gaussian-mixture witness has squared Hellinger distance of order delta_n^2. It also found no current-paper or bank collision. UNRESOLVED BOTTLENECK: Build a fuzzy-Hermite pair with bounded n-sample chi-square distance that obeys the exact PLM residual law and L8 nuisance budgets while hiding an epsilon_g^4 cumulant signal and sustaining target displacement min{d_n,B_n/delta_n}. EARLY KILL TEST: Solve the finite Rademacher-partition exponential-Hermite two-prior program and require a certified feasible pair at separation comparable to epsilon_g^4+n^-1/2; failure after optimizing partition size and moment-matched nuisance priors should stop the sharp converse. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_plm_honest_adaptation.md"
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "No matching lower bound for the non-Gaussian branch was proved. Restoring the promised field kernel requires new target-separated, mixture-close priors wholly inside N_n(delta_n), or a new constrained-risk method under diverging cross-branch divergence; neither exists in the run."
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "kernel_substituted@thm:cross-fuzzy-does-not-close-frontier — the claimed coordinatewise Pareto boundary and matching strong-separation converse were replaced by an upper result plus a proof that the stipulated cross-branch route cannot establish the non-Gaussian face; the core leaves that lower face open."
  - "dropped_fallback_term@thm:adaptive-upper-frontier — the selected-but-disjoint branch returns I_D, but its fixed-alpha expected-length contribution is absent from the proof, so the displayed shortening and its downstream propositions are unproved."
  - "Construct and certify a within-N_n(delta_n) lower-bound experiment that yields L_N(C_n) greater than or comparable to min{d_n^-, B_n/delta_n}; this would establish necessity of the claimed shortening threshold without relying on the refuted cross-branch construction."
reusable_artifacts:
  - "discovery/solve_oeq_branchwise_lower_frontier.json — attempted lower-frontier construction and negative resolution of the cross-branch bounded-chi-square route."
  - "discovery/solve_thm_adaptive_upper_frontier.json — adaptive upper construction; retain only after repairing the disjoint selected-branch fallback."
  - "discovery/solve_thm_gaussian_coordinate_lower.json — conditional Gaussian-coordinate lower argument with separated fuzzy-product and root-N mechanisms."
  - "discovery/core.json — final dependency graph, including the selector impossibility theorem and exact arXiv-v3 source attestation."
seeds_burned: []
proof_attempt_summary: |
  The run derived a union-honest adaptive interval, a conditional Gaussian-coordinate lower bound, and a theorem showing that a consistent common-fit selector forces the proposed cross-branch bounded-chi-square priors apart. The interval proof also omitted the selected-but-disjoint fallback contribution; a singleton fallback repairs that local issue, but cannot supply the promised matching non-Gaussian converse. The central within-N_n mixture-close lower experiment remains new unsolved mathematics, so the field-level Pareto-frontier kernel was not delivered.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 34575628
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 34575628
  total_tokens_consumed: null
banked_on: "2026-09-12"
---

# stat_plm_honest_adaptation / v1 — Failed

**Topic.** Honest adaptation to weak non-Gaussianity in structure-agnostic partially linear inference. In the bounded/sub-Gaussian JMS partially linear class with eta independent of X, unit variance, supplied L8 nuisance errors epsilon_g,n and epsilon_q,n, require one interval to be honest over the union of eta exactly Gaussian and |kappa_4(eta)|>=delta_n. Characterize the coordinatewise Pareto lower boundary of Gaussian and non-Gaussian worst-case expected lengths. With s_n=n^-1/2+epsilon_g,n^4, d_n=n^-1/2+epsilon_g,n epsilon_q,n and B_n=n^-1/2+epsilon_g,n^3 epsilon_q,n+epsilon_g,n^4, construct a split cumulant-test plus unnormalized DML/cubic-ACE inversion attaining (d_n,min{d_n,B_n/delta_n}) when delta_n/s_n diverges. Prove matching branch-designated fuzzy-Hermite lower bounds: below s_n no shortening from d_n, and above it strict shortening occurs exactly when B_n/delta_n=o(d_n). Retain any necessary Gaussian logarithms. Do not claim improvement of global union-supremum length; use the vector frontier as the rate-level object, recognizing that the absolute cross-modulus is symmetric and fixed positive-weight scalarizations are rate-degenerate. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolve derived the exact unnormalized DML bias identity E[(Y-qhat)(T-ghat)]-theta_0=E[(ghat-g_0)(qhat-q_0)], the cubic identity E[eta(eta^3-3eta-kappa_3)]=kappa_4, and a split test/intersection construction with non-Gaussian length at most B_n/delta_n+d_n(s_n/delta_n)^2. It solved epsilon_g=epsilon_q=delta_n=n^-1/8, giving lengths n^-1/4 and n^-3/8, and checked the Gaussian-mixture witness has squared Hellinger distance of order delta_n^2. It also found no current-paper or bank collision. UNRESOLVED BOTTLENECK: Build a fuzzy-Hermite pair with bounded n-sample chi-square distance that obeys the exact PLM residual law and L8 nuisance budgets while hiding an epsilon_g^4 cumulant signal and sustaining target displacement min{d_n,B_n/delta_n}. EARLY KILL TEST: Solve the finite Rademacher-partition exponential-Hermite two-prior program and require a certified feasible pair at separation comparable to epsilon_g^4+n^-1/2; failure after optimizing partition size and moment-matched nuisance priors should stop the sharp converse. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_plm_honest_adaptation.md

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** kernel_substituted@thm:cross-fuzzy-does-not-close-frontier: the claimed coordinatewise Pareto boundary and matching strong-separation converse were replaced by an upper result plus a proof that one cross-branch route cannot establish the non-Gaussian face.

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

---
qid: stat_cate_local_stabilized_hoif_frontier
spec: v1
topic: "Density-free attainment of the KBRW pointwise-CATE benchmark under a fixed positive two-sided covariate-density band. In the i.i.d. observational Holder model with strict overlap, bounded outcomes, alpha-smooth propensity, beta-smooth control regression and gamma-smooth continuous CATE, treat all smoothness indices and radii as known class inputs and construct one total local R-estimator using no density estimate or density smoothness. Let (h_n^*,k_n^*) be the lexicographically smallest optimizer of h^gamma+(h/k^(1/d))^(alpha+beta)+[1/(n h^d){1+k/(n h^d)}]^(1/2), N_n^*=n(h_n^*)^d, G_n={k_n^* log^3(n)<=N_n^*}, and P_n=G_n^c. Prove uniformly on compact smoothness sets that mean-absolute risk is at most the KBRW benchmark with no logarithmic loss: use a same-sample Mobius-stabilized empirical-Gram local HOIF on G_n and a finite-order multiresolution close-pair correction on P_n, with total bounded fallbacks. The P_n theorem must strictly extend the banked low-smoothness 0<beta<alpha<=1 region to a derived nonempty open subset outside it. Do not assume or claim a density-induced slowdown, do not use KBRW's support-hole fuzzy-hypothesis family as a positive-band converse, and do not treat local Gram singularity as an all-estimator lower bound. Estimator algebra, correction order and proof mechanics are outputs of the solve."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "No same-sample Mobius-stabilized empirical-Gram G branch was constructed; no finite-order multiresolution P branch was constructed; both branches instead use one order-one cross-pair ratio, which is sound only at subfield tier."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The title and the name ‘rank-feasible local HOIF’ misdescribe the delivered method: the estimator is an order-one close-pair ratio containing no empirical Gram matrix, Möbius stabilization, or higher-order influence-function construction."
  - "Attainment beyond alpha, beta, gamma at most one is also unproved, with only a saturated first-difference robustness bound available."
  - "D0.5 typed finding: kernel_substituted@thm:unified-benchmark-attainment."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_rank_feasible_local_hoif.json
  - discovery/solve_thm_unified_benchmark_attainment.json
seeds_burned: []
proof_attempt_summary: |
  The run attempted the promised same-sample localized Möbius-HOIF and multiresolution close-pair branches, but the available literature did not discharge their projection-stability, causal-ratio, cancellation, and collision bounds. It instead proved a sound explicit clipped order-one cross-pair risk bound on 0 < alpha,beta,gamma <= 1, including a reversed nuisance-order open set and an above-elbow positive-band minimax corollary. That result cannot satisfy the accepted method-level field claim: both branch handles use the same pair estimator, while the higher-order multiresolution construction remains open and the general referee grades the delivered package subfield.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 23180346
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 23180346
  total_tokens_consumed: null
banked_on: "2026-09-12"
---

# stat_cate_local_stabilized_hoif_frontier / v1 — Failed

**Topic.** Density-free attainment of the KBRW pointwise-CATE benchmark under a fixed positive two-sided covariate-density band. In the i.i.d. observational Holder model with strict overlap, bounded outcomes, alpha-smooth propensity, beta-smooth control regression and gamma-smooth continuous CATE, treat all smoothness indices and radii as known class inputs and construct one total local R-estimator using no density estimate or density smoothness. Let (h_n^*,k_n^*) be the lexicographically smallest optimizer of h^gamma+(h/k^(1/d))^(alpha+beta)+[1/(n h^d){1+k/(n h^d)}]^(1/2), N_n^*=n(h_n^*)^d, G_n={k_n^* log^3(n)<=N_n^*}, and P_n=G_n^c. Prove uniformly on compact smoothness sets that mean-absolute risk is at most the KBRW benchmark with no logarithmic loss: use a same-sample Mobius-stabilized empirical-Gram local HOIF on G_n and a finite-order multiresolution close-pair correction on P_n, with total bounded fallbacks. The P_n theorem must strictly extend the banked low-smoothness 0<beta<alpha<=1 region to a derived nonempty open subset outside it. Do not assume or claim a density-induced slowdown, do not use KBRW's support-hole fuzzy-hypothesis family as a positive-band converse, and do not treat local Gram singularity as an all-estimator lower bound. Estimator algebra, correction order and proof mechanics are outputs of the solve.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** kernel_substituted@thm:unified-benchmark-attainment: both promised constructions were replaced by the same order-one cross-pair estimator, while the required multiresolution correction remains open.

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

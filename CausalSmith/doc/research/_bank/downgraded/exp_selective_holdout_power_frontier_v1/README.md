---
qid: exp_selective_holdout_power_frontier
spec: v1
topic: "Exact selective holdout-power design for two-stratum, two-stage enrichment at a prespecified sharp zero-effect null. Use complete randomization within stratum and stage, an independent exchangeable simple-random stage-1 holdout with rho in a fixed compact interval, and an uncentered standardized treated-minus-control recruitment selector with fixed threshold. On a uniform local-pair-spacing finite-population class with fixed positive-margin selection cells and finite jointly realizable Gaussian primitives, optimize worst-cell conditional local power over compact positive alternatives and nonnegative unit-norm cell-specific stage weights. Prove the selected-quantile convexity reduction, Delta=A-kappa*b1 weight-side theorem, all-nonnegative-Delta unique largest-holdout result, certified negative-Delta interior regime, and complete mixed-sign analytic branch geometry. State equality strata symbolically; give tolerance-certified value and optimizer-set boxes generally and unique designs only with an explicit separation certificate. Consumer: continuous-outcome FOURIER-style future enrichment designs using exact selective randomization inference. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Ehrhard convexity makes the selected-score quantiles convex and reduces every above-size optimizing comparison over an arbitrary compact positive alternative set to its least coordinate. In the exchangeable square-root path, a Mills-ratio factorization proves that Delta determines which side of the proportional stage weight contains every optimum; a realizability bound then makes the largest allowed holdout uniquely optimal when all retained cells have nonnegative Delta. A 100-bit Arb certificate gives a legal negative-Delta mixture whose interior design has power above 0.86428621266 while both endpoint continua stay below 0.86304573855. Symbolic equality predicates and tolerance boxes avoid the refuted exact-real zero oracle. UNRESOLVED BOTTLENECK: Establish the uniform split-conditional Gaussian and zero-null reference transfer with common finite-population remainder, including random complement counts, studentization, rank stability, and conditional quantile transfer. EARLY KILL TEST: Independently verify the Ehrhard-to-quantile single-crossing reduction, then prove the reference approximation on one bounded nonproportional baseline family; pivot if additional population assumptions are necessary. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_selective_holdout_power_frontier.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: null
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The load-bearing joint split CLT is not reproduced: conditional on a holdout, the complement treatment count g^1 is still random, so the cited fixed-group-proportion complete-randomization CLT cannot be applied directly to (X,R_1)."
  - "The Fisher-reference conclusion is asserted by 'the same finite-population argument' after completion B_i+h_s Z_i/sqrt(n), but no conditional split/count CLT or uniform rank/covariance comparison for this random completed population is derived."
  - "The selective transfer and power frontier are plausibly distinct, but the core gives no relevance sentence or theorem-level comparison for several listed closest threads."
  - "DELETE this unconsumed numbered obstruction and its sole supporting def:shrinking-margin-handle, or make it an explicit positioned delivered boundary contribution with a consumer."
reusable_artifacts:
  - "discovery/core.json — exact selective-validity argument, Gaussian convexity/weight-side/endpoint package, literature map, and the unresolved transfer claim with its dependency graph."
  - "discovery/solve_thm_exact_selective_level.tex — finite-space sharp-null randomization proof that is independent of the failed asymptotic transfer."
  - "discovery/solve_thm_full_branch_geometry.tex — analytic branch-stratification attempt, reusable only after pruning dependencies on the unproved transfer and interior claim."
  - "reviews/review_math.json and reviews/stage_0.5.G_attempt1.json — exact soundness and tier failure receipts for a future re-anchored transfer theorem."
seeds_burned:
  - index: 0
    one_liner: "Uniform split-conditional Gaussian and zero-null reference transfer"
    reason: "The sole selected angle exhausted its proposal revisions and then failed the field gate because its load-bearing finite-population transfer remained unproved."
proof_attempt_summary: |
  The run built an exact same-cell Fisher reference, a finite-stratum Gaussian optimizer package, and a proposed finite-population sampling/reference transfer. The transfer collapsed because the proof never established a uniform CLT after conditioning on random split counts, studentization, rank perturbation, and the random Fisher-completed population; therefore its finite-population power consequences and downstream interior/branch claims are not established as written. A future re-anchored run must prove that joint conditional permutation theorem first; the exact sharp-null validity proof and the purely Gaussian analytic reductions are the principal reusable pieces.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 51948786
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 51948786
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# exp_selective_holdout_power_frontier / v1 — Downgraded

**Topic.** Exact selective holdout-power design for two-stratum, two-stage enrichment at a prespecified sharp zero-effect null. Use complete randomization within stratum and stage, an independent exchangeable simple-random stage-1 holdout with rho in a fixed compact interval, and an uncentered standardized treated-minus-control recruitment selector with fixed threshold. On a uniform local-pair-spacing finite-population class with fixed positive-margin selection cells and finite jointly realizable Gaussian primitives, optimize worst-cell conditional local power over compact positive alternatives and nonnegative unit-norm cell-specific stage weights. Prove the selected-quantile convexity reduction, Delta=A-kappa*b1 weight-side theorem, all-nonnegative-Delta unique largest-holdout result, certified negative-Delta interior regime, and complete mixed-sign analytic branch geometry. State equality strata symbolically; give tolerance-certified value and optimizer-set boxes generally and unique designs only with an explicit separation certificate. Consumer: continuous-outcome FOURIER-style future enrichment designs using exact selective randomization inference. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Ehrhard convexity makes the selected-score quantiles convex and reduces every above-size optimizing comparison over an arbitrary compact positive alternative set to its least coordinate. In the exchangeable square-root path, a Mills-ratio factorization proves that Delta determines which side of the proportional stage weight contains every optimum; a realizability bound then makes the largest allowed holdout uniquely optimal when all retained cells have nonnegative Delta. A 100-bit Arb certificate gives a legal negative-Delta mixture whose interior design has power above 0.86428621266 while both endpoint continua stay below 0.86304573855. Symbolic equality predicates and tolerance boxes avoid the refuted exact-real zero oracle. UNRESOLVED BOTTLENECK: Establish the uniform split-conditional Gaussian and zero-null reference transfer with common finite-population remainder, including random complement counts, studentization, rank stability, and conditional quantile transfer. EARLY KILL TEST: Independently verify the Ehrhard-to-quantile single-crossing reduction, then prove the reference approximation on one bounded nonproportional baseline family; pivot if additional population assumptions are necessary. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_selective_holdout_power_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** Stage 0.5 graded the delivered package incremental below the field floor, with the split/count and Fisher-reference transfer not established and no bounded in-scope repair.

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

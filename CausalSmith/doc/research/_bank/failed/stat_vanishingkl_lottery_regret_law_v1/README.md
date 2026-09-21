---
qid: stat_vanishingkl_lottery_regret_law
spec: v1
topic: "Computably honest uniform inference for the compactified Gibbs-to-hard causal-lottery regret curve. In an iid randomized causal model with fixed finite strata and actions, positive baseline lotteries, overlap, bounded outcomes, local reward contrasts, and declared uniform Gaussian/covariance error envelopes, define the categorical Gibbs map q, log-sum-exp potential Ψ, Bregman loss ℓ=c KL(q(u+z)||q(u)), and the normalized regret path indexed by t=c/(1+c). Include the benchmark-weighted hard argmax endpoint at t=0 and projected categorical-covariance quadratic endpoint at t=1. Prove a quantitative uniform C([0,1]) Gaussian approximation, computable inflation, and a certified least-favorable simultaneous upper envelope valid after every measurable temperature choice. Give a terminating grid/Gaussian integration algorithm with explicit off-grid and probability errors and apply it to Fang–Ridder–Xie’s three-arm commitment-savings frontier. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The score-blind presolve derived the exact categorical Bregman identity, the projected high-temperature expansion with an explicit O(1/c) bound, a multiaction hard-endpoint error bound, and a Gaussian tie-slab inequality O(JK²a/√v_min). It solved a legal three-arm Bernoulli witness with contrast covariance [[3/2,3/4],[3/4,3/2]], hard-tie loss 1, and quadratic endpoint 4/9. Exact and multiway ties, zero local rewards, boundary baselines, singular covariance, growing dimension, disappearing strata, hard discontinuities, quantile atoms, plug-in covariance, generic continuous-mapping collapse, and current collisions were checked; excluded regimes remain outside the model. UNRESOLVED BOTTLENECK: Prove a uniform computable small-interval/anti-concentration modulus for sup_t G(h,Z_V), including multiway ties, or prove that one-sided probability bracketing supplies the claimed certified critical value without it. EARLY KILL TEST: For J=1,K=3, uniform baseline, h near (1,0), and V near [[3/2,3/4],[3/4,3/2]], close one certified temperature/parameter grid; an atom, nonvanishing off-grid error, or failure of both anti-concentration and conservative bracketing forces a pivot or stop. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_vanishingkl_lottery_regret_law.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "kernel_substituted@thm:atom-safe-envelope — The promised application to Fang--Ridder--Xie's three-arm commitment-savings frontier is absent: this theorem supplies only a generic certificate/coverage result, while the sole instantiated design is the binary negative witness."
  - "The note contains neither a fitted instance, a certified grid computation, nor a substantive temperature-selection result beyond allowing an arbitrary measurable functional of the defined plug-in frontier."
  - "paper_score_ceiling 6.1 < 7.4, so the graded tier 'field' is capped at 'incremental'."
reusable_artifacts:
  - "discovery/core.json — proved 13-node theorem graph for the fixed finite-cell Gibbs regret path."
  - "discovery/writeup.tex — abstract path law, atom-safe one-sided certificate, exact hard-cell atom formula, and binary collision witness."
  - "discovery/vcs/ — preserved proof/PR history, including the Fang--Ridder--Xie negative class-transfer corollary."
seeds_burned: []
proof_attempt_summary: |
  Discovery proved the abstract compactified Gibbs regret path law, an atom-safe one-sided
  certificate, and a binary collision theorem ruling out a uniform atom-removed modulus; all 13
  graph statements were discharged. The run failed because it never executed the promised certified
  J=1,K=3 grid/Gaussian integration or produced the substantive Fang--Ridder--Xie three-arm
  application, instead falling back to a generic conservative certificate and illustrative framing.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 34217087
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 34217087
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# stat_vanishingkl_lottery_regret_law / v1 — Failed

**Topic.** Computably honest uniform inference for the compactified Gibbs-to-hard causal-lottery regret curve. In an iid randomized causal model with fixed finite strata and actions, positive baseline lotteries, overlap, bounded outcomes, local reward contrasts, and declared uniform Gaussian/covariance error envelopes, define the categorical Gibbs map q, log-sum-exp potential Ψ, Bregman loss ℓ=c KL(q(u+z)||q(u)), and the normalized regret path indexed by t=c/(1+c). Include the benchmark-weighted hard argmax endpoint at t=0 and projected categorical-covariance quadratic endpoint at t=1. Prove a quantitative uniform C([0,1]) Gaussian approximation, computable inflation, and a certified least-favorable simultaneous upper envelope valid after every measurable temperature choice. Give a terminating grid/Gaussian integration algorithm with explicit off-grid and probability errors and apply it to Fang–Ridder–Xie’s three-arm commitment-savings frontier. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The score-blind presolve derived the exact categorical Bregman identity, the projected high-temperature expansion with an explicit O(1/c) bound, a multiaction hard-endpoint error bound, and a Gaussian tie-slab inequality O(JK²a/√v_min). It solved a legal three-arm Bernoulli witness with contrast covariance [[3/2,3/4],[3/4,3/2]], hard-tie loss 1, and quadratic endpoint 4/9. Exact and multiway ties, zero local rewards, boundary baselines, singular covariance, growing dimension, disappearing strata, hard discontinuities, quantile atoms, plug-in covariance, generic continuous-mapping collapse, and current collisions were checked; excluded regimes remain outside the model. UNRESOLVED BOTTLENECK: Prove a uniform computable small-interval/anti-concentration modulus for sup_t G(h,Z_V), including multiway ties, or prove that one-sided probability bracketing supplies the claimed certified critical value without it. EARLY KILL TEST: For J=1,K=3, uniform baseline, h near (1,0), and V near [[3/2,3/4],[3/4,3/2]], close one certified temperature/parameter grid; an atom, nonvanishing off-grid error, or failure of both anti-concentration and conservative bracketing forces a pivot or stop. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_vanishingkl_lottery_regret_law.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** kernel_substituted@thm:atom-safe-envelope: the promised Fang--Ridder--Xie three-arm certified computation/application is absent; only a generic certificate and binary negative witness were delivered.

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

---
qid: stat_dp_cate_fiber_tmechanism_frontier
spec: v1
topic: "Revive parent stat_dp_cate_uniform_design_nuisance_privacy_frontier by proving a log-free target-fiber private T-estimation theorem on the unchanged exact-uniform Hölder pointwise-CATE class. Construct one finite pure-DP estimator from Bernoulli reduction, coherent composite threshold tests, finite wavelet profiles, and scalar-shell exponential selection, and establish R_DP equivalent to max{R_NP,r_G,r_F} without assuming a formula for R_NP, using the separate nonprivate converse, stabilizing an unspecified minimax estimator, or retaining a nuisance-net logarithm. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Independent Bernoullization of bounded outcomes exactly preserves the propensity, arm means, CATE, and both full-class nonprivate and pure-DP minimax risks. Nonprivate minimax risk controls each composite threshold error, while an integrated absolute-risk identity gives a coherent nested family; summing the two candidates per scalar distance shell removes output-cardinality logarithms for stable scores. A finite d=1 randomized-treatment estimator attains max(n^-1/3,(n epsilon)^-1/2) without logs. On the parent’s coupled-nuisance component, singleton mixtures coincide but exact two-record TV equals 4ab and a bounded pair statistic has mean ±4ab, yielding log-free private pair testing. No counterexample forcing a log or third privacy radius was found. UNRESOLVED BOTTLENECK: At the same sample size, construct full-class stable composite scores whose distance-weighted shell errors sum independently of nuisance-sieve size, proving nuisance-entropy cancellation and that Hamming stabilization adds only r_G and r_F for arbitrary least-favorable priors. EARLY KILL TEST: On a finite d=1 two-resolution wavelet family with alpha=beta=1/8 and gamma=1 containing both constant-mixture and shared-sign witnesses, compute nonprivate and private finite programs at the same n, verify every neighboring quantized dataset, and grow the nuisance-sign dimension; a persistent entropy penalty or reliance on the excluded nonprivate formula kills the route. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_dp_cate_fiber_tmechanism_frontier.md"
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "No full-class stable composite score, nuisance-entropy cancellation, dense-occupancy construction, total pure-DP estimator, or two-sided R_DP equivalence was proved."
reusable: unknown
reraise_status: retry
gap_reasons:
  - "The proposed log-free full-class pure-DP frontier is not delivered: this node leaves the required nuisance-independent full-fiber score construction open, so the explicit signed-subclass pair test cannot yet supply the promised full-class estimator or R_DP equivalence."
  - "Dense occupancy and the full-class target-fiber lift remain open."
reusable_artifacts:
  - "discovery/solve_thm_pair_composite_test.json — sparse-occupancy signed-family pure-DP pair-test derivation"
  - "discovery/solve_thm_one_record_obstruction.json — exact one-record affine-separation obstruction"
  - "discovery/proto_core_angle0_rejected.json — exhausted one-record full-fiber proposal angle and anti-constraints"
  - "discovery/core.json — finalized node graph, including the unresolved full-fiber lift certificate"
seeds_burned:
  - index: 0
    one_liner: "seed-log-free-frontier"
    reason: "Angle 0 exhausted one-record affine separation because exact same-class convex-hull identity obstructs it; angle 1 reached only a sparse-occupancy signed-family pair test."
proof_attempt_summary: |
  The run first attempted a one-record target-fiber selector, but an exact convex-hull identity obstructed affine separation, so it pivoted to higher-order occupancy-normalized pair scores. It derived and audited a sensitivity-8/3 pure-DP test for a legal smooth signed binary family in the sparse-occupancy regime, including the relevant compatibility elbow. The field headline collapsed because dense occupancy, nuisance-cardinality-independent full-fiber scores, a total full-class estimator, and matching same-class bounds remain precisely the unresolved central theorem.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 31407397
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 31407397
  total_tokens_consumed: null
banked_on: "2026-09-10"
---

# stat_dp_cate_fiber_tmechanism_frontier / v1 — Downgraded

**Topic.** Revive parent stat_dp_cate_uniform_design_nuisance_privacy_frontier by proving a log-free target-fiber private T-estimation theorem on the unchanged exact-uniform Hölder pointwise-CATE class. Construct one finite pure-DP estimator from Bernoulli reduction, coherent composite threshold tests, finite wavelet profiles, and scalar-shell exponential selection, and establish R_DP equivalent to max{R_NP,r_G,r_F} without assuming a formula for R_NP, using the separate nonprivate converse, stabilizing an unspecified minimax estimator, or retaining a nuisance-net logarithm. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Independent Bernoullization of bounded outcomes exactly preserves the propensity, arm means, CATE, and both full-class nonprivate and pure-DP minimax risks. Nonprivate minimax risk controls each composite threshold error, while an integrated absolute-risk identity gives a coherent nested family; summing the two candidates per scalar distance shell removes output-cardinality logarithms for stable scores. A finite d=1 randomized-treatment estimator attains max(n^-1/3,(n epsilon)^-1/2) without logs. On the parent’s coupled-nuisance component, singleton mixtures coincide but exact two-record TV equals 4ab and a bounded pair statistic has mean ±4ab, yielding log-free private pair testing. No counterexample forcing a log or third privacy radius was found. UNRESOLVED BOTTLENECK: At the same sample size, construct full-class stable composite scores whose distance-weighted shell errors sum independently of nuisance-sieve size, proving nuisance-entropy cancellation and that Hamming stabilization adds only r_G and r_F for arbitrary least-favorable priors. EARLY KILL TEST: On a finite d=1 two-resolution wavelet family with alpha=beta=1/8 and gamma=1 containing both constant-mixture and shared-sign witnesses, compute nonprivate and private finite programs at the same n, verify every neighboring quantized dataset, and grow the nuisance-sign dimension; a persistent entropy penalty or reliance on the excluded nonprivate formula kills the route. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_dp_cate_fiber_tmechanism_frontier.md

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The proposed log-free full-class pure-DP frontier is not delivered: the nuisance-independent full-fiber score construction, dense occupancy, and matched full-class estimator remain open; the sound contribution is an incremental sparse signed-family pair test.

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

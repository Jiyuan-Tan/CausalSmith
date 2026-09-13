---
qid: stat_discrete_ate_honest_inference_frontier
spec: v1
topic: "Honest high-dimensional inference for the ATE with unrestricted discrete confounders. Observe n iid (X,A,Y), X in [d], binary A, real Y, consistency, conditional exchangeability, fixed epsilon overlap, known M>=1, cellwise mean envelope M, and conditional fourth central moments at most M^4. For d<=c_epsilon n log(en), define W* as the minimax worst expected length over uniformly (1-alpha)-honest intervals. Prove W* is of order M min{1,n^(-1/2)+d/[n log(en)]}. Construct one explicit polynomial-time robust heavy/light interval whose rare-cell four-cell Chebyshev factorial-moment statistic has a fully data-computable directly calibrated tail radius; Markov/Chebyshev conversion of the banked MSE result, union bounds, and generic median-of-means wrappers do not count. On triangular arrays with d=o(sqrt(n)), cell masses at least c_0/d, fixed overlap, and efficient variance in [v_0 M^2,v_1 M^2], prove endpointwise o_P(n^(-1/2)) equivalence to the cross-fitted saturated-cell one-step Gaussian interval and ratio-consistent influence-function variance, while retaining honesty without Gaussianity at the rare-cell transition. Prove a direct same-class confidence-length testing converse for the full width frontier. Use Zeng et al.'s n=9915,d=8196 401(k) application as the consumer. Tail calibration, robust blocks, polynomial constants, critical-value computation, and testing priors are solve outputs."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The direct data-computable sharp global radius, certified score inversion, and heavy-light Gaussian endpoint bridge remain unproved; the bank retains the same-class honest-length lower bound, loose deterministic range bracket, factorial-bias infrastructure, and saturated one-step benchmark."
reusable: unknown
reraise_status: retry
gap_reasons:
  - "The selected logarithmic-degree pilot-dependent factorial statistic lacks a direct factorial variance/MGF certificate about the unconditional target."
  - "The heavy Gaussian/fallback score is absent."
  - "Therefore sharp expected radius, score-root arithmetic, frontier attainment, Gaussian-radius expansion, endpoint equivalence, and fixed-alphabet Wald-radius transfer cannot be asserted."
reusable_artifacts:
  - discovery/core.json
  - discovery/solve_thm_same_class_testing_converse.json
  - discovery/solve_tex/solve_thm_same_class_testing_converse.tex
  - discovery/solve_thm_global_honest_upper.json
  - discovery/solve_tex/solve_prop_fixed_alphabet_degenerate_variance.tex
seeds_burned: []
proof_attempt_summary: |
  The run constructed and repaired a constant-block Catoni route for the selected
  factorial statistic, an all-heavy override tied to the saturated one-step estimator,
  and an interval-level Poissonization/de-Poissonization converse.  The direct
  selected-factorial tail certificate and heavy Gaussian/fallback radius could not be
  proved under the frozen assumptions, so the sharp global upper bound, certified
  implementation, and endpoint bridge remain open.  The bank retains the direct
  same-class lower bound, deterministic range bracket, factorial-bias results, and
  saturated one-step local benchmark.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 57598396
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-08"
---

# stat_discrete_ate_honest_inference_frontier / v1 — Downgraded

**Topic.** Honest high-dimensional inference for the ATE with unrestricted discrete confounders. Observe n iid (X,A,Y), X in [d], binary A, real Y, consistency, conditional exchangeability, fixed epsilon overlap, known M>=1, cellwise mean envelope M, and conditional fourth central moments at most M^4. For d<=c_epsilon n log(en), define W* as the minimax worst expected length over uniformly (1-alpha)-honest intervals. Prove W* is of order M min{1,n^(-1/2)+d/[n log(en)]}. Construct one explicit polynomial-time robust heavy/light interval whose rare-cell four-cell Chebyshev factorial-moment statistic has a fully data-computable directly calibrated tail radius; Markov/Chebyshev conversion of the banked MSE result, union bounds, and generic median-of-means wrappers do not count. On triangular arrays with d=o(sqrt(n)), cell masses at least c_0/d, fixed overlap, and efficient variance in [v_0 M^2,v_1 M^2], prove endpointwise o_P(n^(-1/2)) equivalence to the cross-fitted saturated-cell one-step Gaussian interval and ratio-consistent influence-function variance, while retaining honesty without Gaussianity at the rare-cell transition. Prove a direct same-class confidence-length testing converse for the full width frontier. Use Zeng et al.'s n=9915,d=8196 401(k) application as the consumer. Tail calibration, robust blocks, polynomial constants, critical-value computation, and testing priors are solve outputs.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** No explicit globally honest sharp upper construction is established: the selected pilot-dependent factorial statistic lacks a direct variance/MGF certificate and the heavy Gaussian/fallback score is absent.

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

---
qid: stat_manyarm_optimal_value_joint_frontier
spec: v1
topic: "Sharp optimal-personalized-treatment-value estimation with jointly growing treatment menus and sparse categorical patient groups. For every n>=1,d>=1,K>=2, observe n iid (X,A,Y), X in [d], A in [K], Y binary, under consistency and conditional exchangeability. Allow arbitrary unknown masses p_x, unrestricted conditional outcome means mu_ax in [0,1], and unknown propensities with sum_a e_ax=1 and 1/(2K)<=e_ax<=2/K on positive-mass cells; null cells, exact ties and boundary means are legal. Target Vstar=sum_x p_x max_a mu_ax and R(n,d,K)=inf over all estimators sup over this law class of mean squared error. Derive an explicit all-regime rate, including every logarithm, transition and saturation branch, bounded above and below by R with absolute constants independent of n,d,K. Construct a total computable attaining estimator and matching same-class all-estimator converse. Determine necessary and sufficient consistency and parametric-MSE conditions for arbitrary dimension sequences. The exact rate and estimator mechanics are outputs; an unevaluated optimization or fixed-K constants do not solve the kernel. Preserve unknown masses and logging in the upper bound; known-uniform lower subexperiments are legal. Recover d=1 and K=2 benchmarks independently, without replacing the full joint theorem by those slices or the presolved K>=d^2 region. Consumer: the unrestricted attainable-value benchmark for maq/grf multi-arm treatment targeting as intervention menus expand; this does not replace learned-policy inference or claim a full budget-curve result. The legal d=2,K=3 unequal-propensity witness has Vstar=43/50 with switching maximizing arms. Put the dimension-uniform approximation/variance and matching mixture geometry in the headline; do not silently narrow or downgrade if it fails.\n\nPRESOLVE EVIDENCE REQUIRING VERIFICATION: A centered random winner in every patient group yields an exact fixed-sample likelihood-mixture identity with a binomial count of coinciding winners. Its derived lower risk is c min{1,dK log(1+sqrt(K/d))/n}; a total empirical cell-weighted maximum has upper risk C min{1,dK log(eK)/n} on the full unknown-mass and unknown-propensity class. These match for K>=d^2. The one-group passive benchmark and a grouped-arm reduction to the binary parent also yield the bounded-d-and-K parametric criterion. Small exact likelihood calculations passed; null cells, ties, boundary means, unequal logging, saturation, adaptive best-mean prior art, and the known-logging Bayes-accuracy reduction were checked. These are unverified derivations, not a solved full frontier.\nUNRESOLVED BOTTLENECK: Open Lemma J must jointly control approximation bias, factorial covariance, and normalized moment-prior separation with absolute constants, closing 2<K<d^2 and the full consistency boundary for arbitrary masses and propensities.\nEARLY KILL TEST: Test the first certificate on the K=64 Boolean slice at degrees 4,7,8 and compute its exact lifted variance. A verified dual bound or rigorous OR obstruction must support any refutation; floating-point LP output alone cannot. Stop a route that hides K in its constants.\nSTRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_manyarm_optimal_value_joint_frontier.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REVISE
proposal_promise_gap: "kernel_substituted"
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The note proves the full-class upper bound C min{1,dK log(eK)/n} and the lower bound c min{1,dK log(1+sqrt(K/d))/n}, which match only in the region K>=d^2; the exact frontier for 2<K<d^2, the advertised attaining estimator, and the consistency boundary remain open."
  - "The missing central transition, absence of an instantiated certificate, and stale headline claims prevent a field-tier paper."
reusable_artifacts:
  - "discovery/writeup.tex — proved K>=d^2 matched region, one-group benchmark, binary grouping transfer, parametric-MSE criterion, and exact mixture/factorial identities"
  - "discovery/core.json — dependency graph, honest-scope boundary, and the two isolated open nodes"
  - "discovery/solve_thm_manyarm_region.json — structured regional-frontier derivation"
  - "discovery/solve_tex/solve_thm_manyarm_region.tex — rendered proof of the matched many-arm region"
  - "reviews/review_general.json — novelty map and theorem-level literature comparisons"
seeds_burned:
  - index: 0
    one_liner: "Sharp all-regime minimax MSE for unrestricted optimal-treatment value with jointly growing patient groups and treatment menus."
    reason: "Chosen all-regime angle discharged only the K>=d^2 region; the proposed salvage repeated the unresolved dimension-uniform certificate without a construction."
proof_attempt_summary: |
  The run verified a computable full-class upper bound and centered-winner lower bound, matching them for K>=d^2, and discharged the one-group and parametric-boundary results. It then tested whether a dimension-uniform polynomial/factorial certificate could close 2<K<d^2, but the proposed salvage supplied no candidate rate, coefficient construction, variance control, or matching normalized priors. The exact central frontier, attaining all-regime estimator/converse, and general consistency boundary therefore remain open.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 26140051
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 26140051
  total_tokens_consumed: null
banked_on: "2026-09-09"
---

# stat_manyarm_optimal_value_joint_frontier / v1 — Downgraded

**Topic.** Sharp optimal-personalized-treatment-value estimation with jointly growing treatment menus and sparse categorical patient groups. For every n>=1,d>=1,K>=2, observe n iid (X,A,Y), X in [d], A in [K], Y binary, under consistency and conditional exchangeability. Allow arbitrary unknown masses p_x, unrestricted conditional outcome means mu_ax in [0,1], and unknown propensities with sum_a e_ax=1 and 1/(2K)<=e_ax<=2/K on positive-mass cells; null cells, exact ties and boundary means are legal. Target Vstar=sum_x p_x max_a mu_ax and R(n,d,K)=inf over all estimators sup over this law class of mean squared error. Derive an explicit all-regime rate, including every logarithm, transition and saturation branch, bounded above and below by R with absolute constants independent of n,d,K. Construct a total computable attaining estimator and matching same-class all-estimator converse. Determine necessary and sufficient consistency and parametric-MSE conditions for arbitrary dimension sequences. The exact rate and estimator mechanics are outputs; an unevaluated optimization or fixed-K constants do not solve the kernel. Preserve unknown masses and logging in the upper bound; known-uniform lower subexperiments are legal. Recover d=1 and K=2 benchmarks independently, without replacing the full joint theorem by those slices or the presolved K>=d^2 region. Consumer: the unrestricted attainable-value benchmark for maq/grf multi-arm treatment targeting as intervention menus expand; this does not replace learned-policy inference or claim a full budget-curve result. The legal d=2,K=3 unequal-propensity witness has Vstar=43/50 with switching maximizing arms. Put the dimension-uniform approximation/variance and matching mixture geometry in the headline; do not silently narrow or downgrade if it fails.

PRESOLVE EVIDENCE REQUIRING VERIFICATION: A centered random winner in every patient group yields an exact fixed-sample likelihood-mixture identity with a binomial count of coinciding winners. Its derived lower risk is c min{1,dK log(1+sqrt(K/d))/n}; a total empirical cell-weighted maximum has upper risk C min{1,dK log(eK)/n} on the full unknown-mass and unknown-propensity class. These match for K>=d^2. The one-group passive benchmark and a grouped-arm reduction to the binary parent also yield the bounded-d-and-K parametric criterion. Small exact likelihood calculations passed; null cells, ties, boundary means, unequal logging, saturation, adaptive best-mean prior art, and the known-logging Bayes-accuracy reduction were checked. These are unverified derivations, not a solved full frontier.
UNRESOLVED BOTTLENECK: Open Lemma J must jointly control approximation bias, factorial covariance, and normalized moment-prior separation with absolute constants, closing 2<K<d^2 and the full consistency boundary for arbitrary masses and propensities.
EARLY KILL TEST: Test the first certificate on the K=64 Boolean slice at degrees 4,7,8 and compute its exact lifted variance. A verified dual bound or rigorous OR obstruction must support any refutation; floating-point LP output alone cannot. Stop a route that hides K in its constants.
STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_manyarm_optimal_value_joint_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REVISE

**Banking reason.** D0.5.G: delivered tier=subfield below floor=field; exact 2<K<d^2 frontier, instantiated certificate, matching estimator/converse, and general consistency boundary remain open.

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

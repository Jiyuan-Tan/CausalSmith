---
qid: exp_sparsepool_graph_discovery_frontier
spec: v1
topic: "Fixed-budget sparse graph-discovery and honest-inference frontier for adaptive network experiments. For even n and horizon T, observe the full outcome vector after each fixed-budget assignment Z_t with exactly B treated units, under the sparse additive interference model mu_i(z)=alpha_i+tau_i z_i+sum_{j!=i} beta_ij A_ij z_j, maximum degree s<=n/8, beta-min delta, bounded coefficients, and conditionally independent sub-Gaussian noise. Define R* as worst-case cumulative welfare regret minimized over legal sequential designs that also recover A with uniform error at most 1/T. Determine the sharp nonasymptotic order of R*, construct a polynomial-time balanced-pool adaptive design and decoder with simultaneous support certificates, and prove a matching lower bound over every recovery-valid design. For the attaining design, construct debiased martingale estimators with simultaneous support-selection-uniform terminal coverage for TATE and selected edge spillovers. Consumers are Yu et al.'s Instagram A/B interference-characterization workflow and Holtz et al.'s Airbnb pricing meta-experiment. PRESOLVE EVIDENCE REQUIRING VERIFICATION: For a uniform B-subset assignment with p=B/n, the centered design covariance was derived as p(1-p)n/(n-1) times the projector orthogonal to the all-ones vector; every k-sparse contrast consequently has eigenvalue at least p(1-p)(n-k)/(n-1). Since differences of two legal row models are at most (2s+1)-sparse, 2s+1<n removes the exact-budget null direction. Exact enumeration found three B=4 pools distinguishing all 764 degree-at-most-one graphs at n=8. The legal matching witness, s=n/8 boundary, partial matchings, empty-versus-one-edge alternatives, arbitrary signs, welfare-score cancellation, sigma=0, delta=L, short horizons, and the close Wang et al. 2026 unknown-support regret paper were checked without a collision or counterexample. UNRESOLVED BOTTLENECK: Prove a matching change-of-measure lower bound for regret, rather than sample size alone, forced by sparse restricted excitation under adaptive fixed-cardinality actions and graph error at most 1/T, with the correct joint dependence on s, delta, sigma, L, and the top-B learning term. EARLY KILL TEST: Solve the s=1 matching subclass first and prove matching upper and lower bounds for its balanced-pool discovery-regret tax while retaining the top-B optimization term; failure to beat singleton-style n-round exploration or failure of the additive regret lower bound should pivot the run."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "kernel_substituted"
reusable: solver_blocked
reraise_status: true-negative
gap_reasons:
  - "kernel_substituted@thm:sharp-pool-complexity-bracket: The delivered object is a recovery-only bracket for m*, whereas the proposal headlined a recovery-valid cumulative-welfare regret frontier with an attaining adaptive design, matching regret converse, and post-selection-uniform martingale inference; none of those headline objects is supplied here."
  - "The all-regime sharp frontier and finite-precision construction remain open; the broader project objective involving cumulative welfare regret, top-B optimization, TATE inference, and selection-uniform edge inference is not defined or proved in the delivered note."
reusable_artifacts:
  - "discovery/writeup.tex — internally honest recovery-only manuscript defining exact-budget signed-support identification and pool complexity."
  - "discovery/core.json — typed recovery core, including the proved excitation/concentration and adaptive recovery lower-bound components."
  - "discovery/proto_core_angle0_rejected.json — archived faithful regret/inference angle; theorem program remained unproved and must not be treated as established."
  - "discovery/solve_oeq_sharp_pool_complexity.json — attempted low-noise sharp-pool-complexity repair and remaining open gap."
seeds_burned: []
proof_attempt_summary: |
  Discovery first attacked the promised degree-one recovery-regret frontier, but its balanced-pool construction and information-to-welfare obligations did not close. A later angle produced sound recovery-only identification, concentration, certificate, and pool-complexity bracket results, yet substituted A and m* for the promised R*, omitted top-B welfare regret and selection-uniform TATE/edge inference, and left the recovery frontier itself open. Independent validity review found that restoring the original kernel would require several new theorem programs rather than a scoped repair, so the original topic terminated while these recovery artifacts remain reusable for a separately named salvage.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 67497166
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-05"
---

# exp_sparsepool_graph_discovery_frontier / v1 — Failed

**Topic.** Fixed-budget sparse graph-discovery and honest-inference frontier for adaptive network experiments. For even n and horizon T, observe the full outcome vector after each fixed-budget assignment Z_t with exactly B treated units, under the sparse additive interference model mu_i(z)=alpha_i+tau_i z_i+sum_{j!=i} beta_ij A_ij z_j, maximum degree s<=n/8, beta-min delta, bounded coefficients, and conditionally independent sub-Gaussian noise. Define R* as worst-case cumulative welfare regret minimized over legal sequential designs that also recover A with uniform error at most 1/T. Determine the sharp nonasymptotic order of R*, construct a polynomial-time balanced-pool adaptive design and decoder with simultaneous support certificates, and prove a matching lower bound over every recovery-valid design. For the attaining design, construct debiased martingale estimators with simultaneous support-selection-uniform terminal coverage for TATE and selected edge spillovers. Consumers are Yu et al.'s Instagram A/B interference-characterization workflow and Holtz et al.'s Airbnb pricing meta-experiment. PRESOLVE EVIDENCE REQUIRING VERIFICATION: For a uniform B-subset assignment with p=B/n, the centered design covariance was derived as p(1-p)n/(n-1) times the projector orthogonal to the all-ones vector; every k-sparse contrast consequently has eigenvalue at least p(1-p)(n-k)/(n-1). Since differences of two legal row models are at most (2s+1)-sparse, 2s+1<n removes the exact-budget null direction. Exact enumeration found three B=4 pools distinguishing all 764 degree-at-most-one graphs at n=8. The legal matching witness, s=n/8 boundary, partial matchings, empty-versus-one-edge alternatives, arbitrary signs, welfare-score cancellation, sigma=0, delta=L, short horizons, and the close Wang et al. 2026 unknown-support regret paper were checked without a collision or counterexample. UNRESOLVED BOTTLENECK: Prove a matching change-of-measure lower bound for regret, rather than sample size alone, forced by sparse restricted excitation under adaptive fixed-cardinality actions and graph error at most 1/T, with the correct joint dependence on s, delta, sigma, L, and the top-B learning term. EARLY KILL TEST: Solve the s=1 matching subclass first and prove matching upper and lower bounds for its balanced-pool discovery-regret tax while retaining the top-B optimization term; failure to beat singleton-style n-round exploration or failure of the additive regret lower bound should pivot the run.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** Terminal kernel substitution: the delivered recovery-only pool-complexity bracket omits the promised welfare-regret frontier, top-B learning term, and selection-uniform TATE/edge inference.

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

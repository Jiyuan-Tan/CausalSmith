---
qid: panel_ptsc_union_efficiency_envelope
spec: v1
topic: "Union-tangent efficiency and oracle-adaptation frontier for identification-robust short-panel ATT estimation. Observe iid fixed-length panels with finitely many groups and finite-support covariates, overlap, bounded fourth moments, one final-period treated group, and no anticipation. Let the ATT be identified on the nonnested union of conditional parallel trends and a uniquely identified full-rank group-level synthetic-control mean restriction. At every intersection law with fixed rank and overlap margins, characterize the PT and SC influence-function classes and their intersection; derive the union convolution bound; prove simultaneous equality with both branch oracle bounds iff their canonical gradients coincide, and one-sided equality iff the relevant branch gradient satisfies the other branch's derivative constraints; compute the envelope by finite covariance-weighted quadratic programs; and construct a cross-fitted attaining one-step estimator with consistent variance and multiplier coverage uniform over root-n local alternatives in either branch. Include the equal-share three-group, three-period witness with mean paths (0,0,0), (-1,-2,-2), (1,2,2), independent bounded innovations, and control change variances 1 and 4, which yields SC weights (1/2,1/2) versus PT-efficient weights (4/5,1/5). Consumers are Rummo et al.'s 2026 sugary-drink-tax synthetic-comparison DiD and Sun–Xie–Zhang's Alaska minimum-wage application. PRESOLVE EVIDENCE REQUIRING VERIFICATION: With finite covariate support, each branch is a finite conditional-moment manifold. Starting from a common union-valid influence function, the presolve represented the branch influence-function classes as affine translates of their restriction-normal spans; their intersection reduces the union canonical gradient to a covariance-weighted projection, computed by one finite quadratic program per stratum. Pythagorean projection identities give the stated simultaneous and one-sided adaptation criteria. In the legal equal-share witness, independent final innovations retain distinct SC and PT coefficients, while SC weight-path terms occupy preperiod coordinates. Checks of rank boundaries, covariance degeneracy, weight boundaries, local sequences, and current literature found no refutation or exact collision, subject to the stated interiority margins. UNRESOLVED BOTTLENECK: Prove a uniform asymptotic-linear expansion for the estimated profiled-normal projection, including rank stability and multiplier validity along every root-n sequence contained in either branch. EARLY KILL TEST: Symbolically build the no-covariate three-period, three-group restriction-gradient Gram matrices and solve their intersection quadratic program. Stop if the common influence-function class is empty or the claimed strict coefficient gap fails; pivot to characterization-only if the solution is identically Sun–Xie–Zhang's influence function for every full-rank covariance design."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "tier_genuinely_below"
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "it does not prove that any estimator attains the union bound"
  - "the advertised oracle-adaptation frontier characterizes equality of abstract variance bounds rather than existence of a procedure that adapts to either branch at those bounds"
  - "they supply neither implementable inference nor evidence that the diagnostic improves either cited application"
reusable_artifacts:
  - "discovery/core.json — citation-clean dependency graph and exact theorem statements"
  - "discovery/writeup.tex — corrected composition-gradient decomposition, finite-QP envelope, Gram adaptation criteria, and endpoint reductions"
  - "discovery/proposal.tex — scoped literature map and consumer framing"
  - "reviews/ — final zero-finding correctness reviews and below-floor novelty receipts"
seeds_burned: []
proof_attempt_summary: |
  The run derived the strict-interior, locally constant-rank PT/SC influence classes, corrected their common treated-composition term, computed the union lower bound by finite covariance-weighted QPs, and proved exact oracle-equality criteria, endpoint reductions, and a strict three-group witness. The requested uniform attaining estimator collapsed: finite-coordinate splicing rules out the frozen sequence-class claim, while a positive result on a conventional common neighborhood would require a new package proving profiled-normal estimation, uniform rank stability, asymptotic linearity, variance consistency, and multiplier validity. Both final correctness referees passed with no findings, but the delivered characterization-only package remained incremental.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 49458686
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 49458686
  total_tokens_consumed: null
banked_on: "2026-09-09"
---

# panel_ptsc_union_efficiency_envelope / v1 — Downgraded

**Topic.** Union-tangent efficiency and oracle-adaptation frontier for identification-robust short-panel ATT estimation. Observe iid fixed-length panels with finitely many groups and finite-support covariates, overlap, bounded fourth moments, one final-period treated group, and no anticipation. Let the ATT be identified on the nonnested union of conditional parallel trends and a uniquely identified full-rank group-level synthetic-control mean restriction. At every intersection law with fixed rank and overlap margins, characterize the PT and SC influence-function classes and their intersection; derive the union convolution bound; prove simultaneous equality with both branch oracle bounds iff their canonical gradients coincide, and one-sided equality iff the relevant branch gradient satisfies the other branch's derivative constraints; compute the envelope by finite covariance-weighted quadratic programs; and construct a cross-fitted attaining one-step estimator with consistent variance and multiplier coverage uniform over root-n local alternatives in either branch. Include the equal-share three-group, three-period witness with mean paths (0,0,0), (-1,-2,-2), (1,2,2), independent bounded innovations, and control change variances 1 and 4, which yields SC weights (1/2,1/2) versus PT-efficient weights (4/5,1/5). Consumers are Rummo et al.'s 2026 sugary-drink-tax synthetic-comparison DiD and Sun–Xie–Zhang's Alaska minimum-wage application. PRESOLVE EVIDENCE REQUIRING VERIFICATION: With finite covariate support, each branch is a finite conditional-moment manifold. Starting from a common union-valid influence function, the presolve represented the branch influence-function classes as affine translates of their restriction-normal spans; their intersection reduces the union canonical gradient to a covariance-weighted projection, computed by one finite quadratic program per stratum. Pythagorean projection identities give the stated simultaneous and one-sided adaptation criteria. In the legal equal-share witness, independent final innovations retain distinct SC and PT coefficients, while SC weight-path terms occupy preperiod coordinates. Checks of rank boundaries, covariance degeneracy, weight boundaries, local sequences, and current literature found no refutation or exact collision, subject to the stated interiority margins. UNRESOLVED BOTTLENECK: Prove a uniform asymptotic-linear expansion for the estimated profiled-normal projection, including rank stability and multiplier validity along every root-n sequence contained in either branch. EARLY KILL TEST: Symbolically build the no-covariate three-period, three-group restriction-gradient Gram matrices and solve their intersection quadratic program. Stop if the common influence-function class is empty or the claimed strict coefficient gap fails; pivot to characterization-only if the solution is identically Sun–Xie–Zhang's influence function for every full-rank covariance design.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** The note proves branch influence-function classes, their intersection-based convolution lower bound, finite Gram criteria, and an explicit strict-gap witness, but it does not prove that any estimator attains the union bound.

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

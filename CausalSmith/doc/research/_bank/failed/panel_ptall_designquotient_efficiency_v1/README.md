---
qid: panel_ptall_designquotient_efficiency
spec: v1
topic: "Observable PT-All design-quotient efficiency beyond chained DiD GMM. For fixed-T staggered adoption with declared cohort-specific structural observation-pattern supports, conditional pattern independence from the full potential-outcome path, no anticipation, overlap, finite fourth moments, and conditional PT-All, index every observable untreated cohort-time mean once and build its cohort-level/common-time design matrix A. Prove that null(A') is the complete observable linear PT-All restriction space; embed Bellégo's all-supported-link optimal-GMM restriction span L_B, compute the quotient Q=null(A')/L_B by rank-revealing elimination, and prove Q changes a target's efficiency bound iff its covariance-weighted target residual is nonzero. Derive the canonical gradient, exact Schur-complement gain, attaining cross-fitted one-step estimator, multiplier bands, and equality specialization to Bellégo. Include the seven-cell G3/G4/G5/never rotating-panel witness with patterns {1,3},{1,2},{2,3},{1,3}, unique quotient restriction, and n-scaled ATT variance improvement 16 to 40/3; audit Uhlemann's CBS rotating-firm chained-DiD application. PRESOLVE EVIDENCE REQUIRING VERIFICATION: With observable cells ordered as (G3,1),(G4,1),(G4,2),(G5,2),(G5,3),(never,1),(never,3), the presolver constructed the normalized six-column cohort/time design, proved rank(A)=6, and obtained the unique restriction vector (0,1,-1,1,-1,-1,1). Bellégo contributes no overidentifying row on this witness, so the quotient has rank one. With marginal-score covariance 4I, the direct ATT variance is 16, the restriction variance is 24, and target-restriction covariance is -8, yielding 16-64/24=40/3. Checks covered disconnected supports, separately sampled marginals, one-wave telescopes, singular covariance, target paths, Bellégo's all-k links, the Uhlemann sampling description, and adjacent literature without finding a collision. UNRESOLVED BOTTLENECK: Prove the observed-data tangent-space factorization for arbitrary nonmonotone structural patterns with conditional covariates, showing that the efficient marginal-score vector followed by quotient projection is the full canonical gradient rather than only the best linear-GMM score. EARLY KILL TEST: Construct Bellégo's complete equations 23-24 moment matrix for the seven-cell witness, row-reduce it jointly with A, and stop if Bellégo already spans the quotient or if the constrained Gaussian Fisher bound differs from 40/3."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: REVISE
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: retry
gap_reasons:
  - "The statistic inf_{η∈Nδ} distance equals distance to cl(Nδ), so it necessarily admits excluded rank-loss closure points; strict CAD inequalities cannot make this an exact nonclosed-null distance test."
  - "Separation only from lower-rank null strata does not exclude nearby higher-rank strata whose closures contain a rank-loss point; rank-zero oracle recovery is not automatic."
  - "Angle 0 exhausted on non-nested Bellégo comparator drift, and angle 2 did not meet the field novelty floor."
reusable_artifacts:
  - "discovery/proto_core.json — final actual-OVS finite-cell RIF collision, regular primitive chart, and CAD-envelope proposal"
  - "reviews/angle1_v10.json — closure-distance counterexample and literature corrections"
  - "orchestrator/decision_log.jsonl — verified Δ(0)=0, Δ(t)→8 algebra and closure-calibrated repair receipt"
seeds_burned:
  - index: 0
    one_liner: "Full observed-data PT-All design quotient and canonical-gradient efficiency under arbitrary nonmonotone structural patterns."
    reason: "Angle 0 exhausted on non-nested comparator drift; angle 1 exhausted its final authorized v10 on closure-distance correctness; angle 2 was below the field floor."
  - index: 1
    one_liner: "Rank-adaptive inference for a zero or locally singular PT-All quotient efficiency gain."
    reason: "Angle 0 exhausted on non-nested comparator drift; angle 1 exhausted its final authorized v10 on closure-distance correctness; angle 2 was below the field floor."
  - index: 2
    one_liner: "Survey-design correspondence and efficiency audit for the CBS rotating-firm chained-DiD application."
    reason: "Angle 0 exhausted on non-nested comparator drift; angle 1 exhausted its final authorized v10 on closure-distance correctness; angle 2 was below the field floor."
proof_attempt_summary: |
  Three proposal angles were explored through ten angle-1 revisions; no D0 derivation or Lean formalization began. The final revision successfully replaced the synthetic carrier with an actual OVS finite-cell RIF collision and verified Δ(0)=0 with Δ(t)→8, but its exact-null test collapsed because distance to a nonclosed null equals distance to its closure and its rank-zero oracle claim was false. A future explicitly authorized retry would need closure-calibrated semialgebraic inference, all-competing-strata separation, and the recorded Chen–Fang/OVS citation corrections.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 104562605
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-04"
---

# panel_ptall_designquotient_efficiency / v1 — Failed

**Topic.** Observable PT-All design-quotient efficiency beyond chained DiD GMM. For fixed-T staggered adoption with declared cohort-specific structural observation-pattern supports, conditional pattern independence from the full potential-outcome path, no anticipation, overlap, finite fourth moments, and conditional PT-All, index every observable untreated cohort-time mean once and build its cohort-level/common-time design matrix A. Prove that null(A') is the complete observable linear PT-All restriction space; embed Bellégo's all-supported-link optimal-GMM restriction span L_B, compute the quotient Q=null(A')/L_B by rank-revealing elimination, and prove Q changes a target's efficiency bound iff its covariance-weighted target residual is nonzero. Derive the canonical gradient, exact Schur-complement gain, attaining cross-fitted one-step estimator, multiplier bands, and equality specialization to Bellégo. Include the seven-cell G3/G4/G5/never rotating-panel witness with patterns {1,3},{1,2},{2,3},{1,3}, unique quotient restriction, and n-scaled ATT variance improvement 16 to 40/3; audit Uhlemann's CBS rotating-firm chained-DiD application. PRESOLVE EVIDENCE REQUIRING VERIFICATION: With observable cells ordered as (G3,1),(G4,1),(G4,2),(G5,2),(G5,3),(never,1),(never,3), the presolver constructed the normalized six-column cohort/time design, proved rank(A)=6, and obtained the unique restriction vector (0,1,-1,1,-1,-1,1). Bellégo contributes no overidentifying row on this witness, so the quotient has rank one. With marginal-score covariance 4I, the direct ATT variance is 16, the restriction variance is 24, and target-restriction covariance is -8, yielding 16-64/24=40/3. Checks covered disconnected supports, separately sampled marginals, one-wave telescopes, singular covariance, target paths, Bellégo's all-k links, the Uhlemann sampling description, and adjacent literature without finding a collision. UNRESOLVED BOTTLENECK: Prove the observed-data tangent-space factorization for arbitrary nonmonotone structural patterns with conditional covariates, showing that the efficient marginal-score vector followed by quotient projection is the full canonical gradient rather than only the best linear-GMM score. EARLY KILL TEST: Construct Bellégo's complete equations 23-24 moment matrix for the seven-cell witness, row-reduce it jointly with A, and stop if Bellégo already spans the quotient or if the constrained Gaussian Fisher bound differs from 40/3.

**Novelty target.** field

**Stage -0.5 verdict.** REVISE

**Stage 0.5 verdict.** NA

**Banking reason.** D-0.5 final NO-PASS: the exact nonclosed-null distance equals distance to its closure, invalidating claimed exclusion and automatic rank-zero oracle recovery after the last authorized reset.

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

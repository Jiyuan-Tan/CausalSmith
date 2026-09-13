---
qid: panel_hazard_hmm_att
spec: v1
topic: "Hazard-lift identification of staggered-adoption ATT in aliased hidden Markov panels. Fix a known finite hidden order K, finite untreated-output alphabet, T>=2K-1, time-homogeneous untreated HMM law, adoption hazard depending on current hidden state but conditionally independent of future untreated innovations, full predictive Hankel rank, invertible killed dynamics, and positive cohort masses. Prove that hazards in the current-emission algebra identify every adopter cohort's finite untreated counterfactual output law and group-time ATT despite non-permutation latent fibers. Prove a generic converse when aliased states have unequal hazards and unequal forecasts, including an exact positive same-observed-law fiber with ATT gap 2/185. On a predeclared fixed Hankel chart and coefficient-normalized polynomial frame with positive rank/frame gaps, derive joint influence functions and simultaneous fixed-grid inference; put algebra-collision sequences in an explicit gray zone. Consumer: Kim--Lee's six-period binary video-on-demand staggered-adoption panel. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact symbolic checks verified the canonical stopped-law realization, HDK invariance, two strictly positive three-state fibers, stochastic and similarity identities, invariant positive-fiber means, the 2/185 negative-fiber gap, full length-two ranks, and an 8/285 converse derivative. Differentiating the fixed Gram solve, de-killing inverse, matrix powers, and quotient yielded the panel-level influence expansion. The aliased witness frame has singular values 2.00332688 and 0.99833932; along a legal rank-three collision sequence, the declared chart has sigma3=(10.33271+o(1))*delta, so fixed separation keeps the exact repeated-emission witness while excluding false uniform root-N claims. Bounded primary checks found HMM alias geometry and outcome-driven adoption simulations, but no causal hazard-lift ATT theorem. UNRESOLVED BOTTLENECK: Apply the predeclared K=3 chart, HDK residual, frame-gap, cohort-mass, and influence-precision diagnostics to the six-period Kim--Lee panel and establish that at least one preregistered observable stratum is empirically usable. EARLY KILL TEST: Reproduce the stated Hankel singular value, legal fibers, 2/185 gap, and analytic derivative, then run the fixed diagnostics on Kim--Lee; kill the application claim if every chart is ill-conditioned, HDK fails, precision is unusable, or the law lies in the collision gray zone. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/panel_hazard_hmm_att.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "Field framing promised a complete alias-boundary diagnostic and an empirically usable Kim--Lee stratum, but delivered a sharp conditional identification theorem, converse, exact fiber, and no-uniform-consistency boundary without those two field-level closures."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The complete K=3 one-alias-block boundary classification remains open."
  - "No stratum is shown to pass the rank, HDK, conditioning, support, gray-zone, and precision gates, so practical usability is unestablished."
  - "The paper currently supplies neither the promised complete frontier diagnostic nor reproducible evidence that its demanding regular regime occurs in the motivating panel."
reusable_artifacts:
  - discovery/core.json
  - discovery/solve_thm_finite_realization.json
  - discovery/solve_thm_generic_converse.json
  - discovery/solve_prop_exact_fiber_gap.json
  - discovery/solve_prop_collision_gray_zone.json
  - discovery/writeup.tex
seeds_burned: []
proof_attempt_summary: |
  The run derived the finite stopped-law realization, hazard-lift identification,
  a direct generic converse, an exact positive alias fiber with ATT gap 2/185,
  and a two-parameter collision family ruling out uniform consistency and uniformly
  shrinking honest bands on the unseparated class. It also supplied guarded
  fixed-chart influence inference on separated strata. Field novelty failed because
  the complete bivariate K=3 alias frontier remains paper-scale open and the Kim--Lee
  application data or stopped-word moments were unavailable for the promised
  empirical certificate.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 37192310
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 37192310
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# panel_hazard_hmm_att / v1 — Downgraded

**Topic.** Hazard-lift identification of staggered-adoption ATT in aliased hidden Markov panels. Fix a known finite hidden order K, finite untreated-output alphabet, T>=2K-1, time-homogeneous untreated HMM law, adoption hazard depending on current hidden state but conditionally independent of future untreated innovations, full predictive Hankel rank, invertible killed dynamics, and positive cohort masses. Prove that hazards in the current-emission algebra identify every adopter cohort's finite untreated counterfactual output law and group-time ATT despite non-permutation latent fibers. Prove a generic converse when aliased states have unequal hazards and unequal forecasts, including an exact positive same-observed-law fiber with ATT gap 2/185. On a predeclared fixed Hankel chart and coefficient-normalized polynomial frame with positive rank/frame gaps, derive joint influence functions and simultaneous fixed-grid inference; put algebra-collision sequences in an explicit gray zone. Consumer: Kim--Lee's six-period binary video-on-demand staggered-adoption panel. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact symbolic checks verified the canonical stopped-law realization, HDK invariance, two strictly positive three-state fibers, stochastic and similarity identities, invariant positive-fiber means, the 2/185 negative-fiber gap, full length-two ranks, and an 8/285 converse derivative. Differentiating the fixed Gram solve, de-killing inverse, matrix powers, and quotient yielded the panel-level influence expansion. The aliased witness frame has singular values 2.00332688 and 0.99833932; along a legal rank-three collision sequence, the declared chart has sigma3=(10.33271+o(1))*delta, so fixed separation keeps the exact repeated-emission witness while excluding false uniform root-N claims. Bounded primary checks found HMM alias geometry and outcome-driven adoption simulations, but no causal hazard-lift ATT theorem. UNRESOLVED BOTTLENECK: Apply the predeclared K=3 chart, HDK residual, frame-gap, cohort-mass, and influence-precision diagnostics to the six-period Kim--Lee panel and establish that at least one preregistered observable stratum is empirically usable. EARLY KILL TEST: Reproduce the stated Hankel singular value, legal fibers, 2/185 gap, and analytic derivative, then run the fixed diagnostics on Kim--Lee; kill the application claim if every chart is ill-conditioned, HDK fails, precision is unusable, or the law lies in the collision gray zone. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/panel_hazard_hmm_att.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** The complete K=3 one-alias-block boundary classification remains open, and no Kim--Lee stratum is shown to pass the rank, HDK, conditioning, support, gray-zone, and precision gates; paper_score_ceiling 7.2 < 7.4.

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

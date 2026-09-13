---
qid: stat_capped_propensity_kink_bvm
spec: v1
topic: "Capped-propensity kink regularity and posterior calibration. In the iid binary-treatment unconfounded model with bounded outcomes, fix delta>1 and the intervention q_delta(1|x)=min(1,delta e(x)). Prove that its causal mean is pathwise differentiable exactly when K_delta(P)=E[tau(X)^2 1{e(X)=1/delta}]=0; derive the efficient influence function and exact branch-specific one-step remainder; establish its sharp propensity-margin rate; and prove a one-step posterior Bernstein-von Mises and pointwise credible-set coverage theorem without strong overlap for an explicit all-data histogram posterior whose draws cross the cap. When K_delta>0, prove nonregularity with a legal finite-cell tangent experiment. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact derivation gives a propensity-outcome product plus delta E[tau|e-c|1{estimated and true cap branches disagree}], branchwise bounded denominators, the rate rho*epsilon+rho^(1+alpha), and a matching continuous-margin example; 2,450 legal cases including endpoints were checked. A density-cone proof spine supports the regularity iff, while boundary-bin localization supplies a concrete threshold-process route; generic margin powers and finite-dimensional posterior failures remain credited prior art. UNRESOLVED BOTTLENECK: Prove joint posterior concentration for the all-data Beta histogram with J=ceil(n^(1/3)), including uniform branch-relevant outcome contraction under unequal random arm counts, then close the finite-basis empirical-process decomposition. EARLY KILL TEST: For delta=2, e(x)=x, and constant separated Bernoulli outcome means, prove the deterministic posterior sieve and uniform corrected-signal empirical-process remainder; if this requires eliminating cap crossings or restoring strong overlap, pivot before attempting SoftBART. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_capped_propensity_kink_bvm.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "The field-level posterior calibration promise was not delivered: equation (32) treats a posterior-draw-dependent branch remainder as deterministic, while the completed regularity and exact-remainder results survive only at subfield value."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The load-bearing equicontinuity proof asserts decomposition (32) without displaying its coefficients, and treats the within-bin remainder as a single deterministic function even though branch selection varies with the posterior draw; the stated variance argument therefore does not by itself establish uniform control over that remainder class."
  - "The posterior-calibration result is confined to the engineered one-dimensional class with uniform X, known identity propensity structure, Bernoulli outcomes, and Lipschitz regressions."
  - "The package also supplies no application or numerical evidence showing that the canonical histogram benchmark approximates empirically relevant propensity models, while inference under sequences approaching a cap atom remains open."
  - "paper_score_ceiling 6.7 < 7.4, so the graded tier 'field' is capped at 'subfield'."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_lem_exact_branch_remainder.json
  - discovery/solve_prop_causal_identification.json
  - discovery/solve_thm_histogram_bvm_coverage.json
  - reviews/review_math.json
  - reviews/review_rubric.json
seeds_burned: []
proof_attempt_summary: |
  The run derived the cap-contact pathwise-regularity characterization, a bounded canonical gradient, a legal nonregular tangent, and an exact branchwise one-step remainder with its margin rate. The field-level package collapsed because the histogram posterior BvM proof did not uniformly control its posterior-indexed branch-selection remainder, while its positive theorem remained restricted to an engineered one-dimensional benchmark. A future re-raise should keep the sound regularity/remainder core, replace equation (32) with an explicit indexed finite-bin decomposition, and then reassess field novelty with the closest accepted-bank comparator and an empirical application.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 10411965
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 10411965
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# stat_capped_propensity_kink_bvm / v1 — Downgraded

**Topic.** Capped-propensity kink regularity and posterior calibration. In the iid binary-treatment unconfounded model with bounded outcomes, fix delta>1 and the intervention q_delta(1|x)=min(1,delta e(x)). Prove that its causal mean is pathwise differentiable exactly when K_delta(P)=E[tau(X)^2 1{e(X)=1/delta}]=0; derive the efficient influence function and exact branch-specific one-step remainder; establish its sharp propensity-margin rate; and prove a one-step posterior Bernstein-von Mises and pointwise credible-set coverage theorem without strong overlap for an explicit all-data histogram posterior whose draws cross the cap. When K_delta>0, prove nonregularity with a legal finite-cell tangent experiment. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact derivation gives a propensity-outcome product plus delta E[tau|e-c|1{estimated and true cap branches disagree}], branchwise bounded denominators, the rate rho*epsilon+rho^(1+alpha), and a matching continuous-margin example; 2,450 legal cases including endpoints were checked. A density-cone proof spine supports the regularity iff, while boundary-bin localization supplies a concrete threshold-process route; generic margin powers and finite-dimensional posterior failures remain credited prior art. UNRESOLVED BOTTLENECK: Prove joint posterior concentration for the all-data Beta histogram with J=ceil(n^(1/3)), including uniform branch-relevant outcome contraction under unequal random arm counts, then close the finite-basis empirical-process decomposition. EARLY KILL TEST: For delta=2, e(x)=x, and constant separated Bernoulli outcome means, prove the deterministic posterior sieve and uniform corrected-signal empirical-process remainder; if this requires eliminating cap crossings or restoring strong overlap, pivot before attempting SoftBART. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_capped_propensity_kink_bvm.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G tier=subfield < floor=field: paper_score_ceiling 6.7 < 7.4; the histogram posterior equicontinuity/BvM argument remains incomplete.

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

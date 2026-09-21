---
qid: pid_ranksim_pathset_discontinuity
spec: v1
topic: "Common-rank policy-set continuity frontier without complier full support. Observe a binary instrument Z and treatment D=1{U<=p_Z}, with U uniform, 0<p0<p1<1, exclusion and instrument independence; outcomes lie in a fixed ordered K-point alphabet. Impose exactly Marx's existential rank similarity: marginally uniform ranks V0,V1 represent Y0,Y1 and have equal conditional laws given U, with no canonical independent-PIT restriction. For a fixed policy grid containing thresholds below p0 and above p1, prove the sharp joint policy-mean set is the union of at most binomial(2K-2,K-1) common-rank lattice-path allocation polytope images, with one-law constructions and finite failure certificates. Characterize Hausdorff continuity by finite path-survival inclusions and prove a centered local Lipschitz bound; give a legal K=3 KL-contiguous discontinuity and the matching impossibility of globally shrinking honest metric inference. Construct globally honest multinomial outer-set and set-of-sets inversion, then prove projected full-loss active-stratum Gaussian calibration only on certified continuity laws, including specified structural-zero sampling faces. Consumer: Marx's Oregon Health Insurance Experiment extrapolations to discounted Medicaid take-up and expansion to never-treated. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Two fresh presolves derived the common-law path construction, the finite survival criterion, and the observed-law discontinuity. Exact rational checks verified 25 primal allocations, six full-system Farkas exclusions of the separately attainable upper-upper corner, and a common certificate excluding five disappearing paths. The positive-t submodel has d_H(S_s,S_t)=2|s-t| and an explicit folded-normal limit. Stronger pairwise-neighborhood Lipschitzness and path-domain-only bootstrap shortcuts were refuted; global confidence-region inversion remained valid. UNRESOLVED BOTTLENECK: Prove that snapping every active diagonal boundary and value-intercept form of the full projected Hausdorff-loss partition consistently recovers the same homogeneous loss germ at every certified continuous multi-path switch, including relative lower-dimensional sampling cells. EARLY KILL TEST: Compile the projected K=3 Hausdorff-loss partition at a continuous internal-face point with a propensity/grid tie and compare the snapped germ against exact rational perturbations on every feasible tangent face; stop or pivot the regular branch if any loss piece is missed, any local intercept is nonzero, or the germ changes within the recovered stratum. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_ranksim_pathset_discontinuity.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "The proved finite-alphabet fixed-grid theory remains pointwise on known exact sampling faces, while exact inversion is doubly exponential and lacks an implementation or substantive Oregon application."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The proved contribution is a sharp finite-alphabet, fixed-grid identification and continuity theory, not a general rank-similar policy frontier."
  - "The Gaussian calibration is pointwise and conditional on the true exact sampling face and certified continuity."
  - "The exact inversion algorithm proves termination through quantifier elimination but has doubly exponential worst-case complexity and is accompanied by neither an implementation nor a substantive Oregon application demonstrating practical tractability."
reusable_artifacts:
  - discovery/core.json
  - discovery/solve_thm_continuity_frontier.json
  - discovery/solve_thm_active_germ_recovery.json
  - discovery/solve_prop_global_inversion_coverage.json
  - discovery/solve_thm_finite_inversion_algorithm.json
  - discovery/solve_prop_one_path_limit.json
  - discovery/solve_lem_observed_law_compatibility.json
  - discovery/writeup.tex
seeds_burned: []
proof_attempt_summary: |
  Discovery proved the common-rank finite path-union representation, path-survival
  continuity equivalence, a KL-contiguous Hausdorff jump and impossibility result,
  globally honest set-of-sets inversion, and pointwise exact-face active-germ Gaussian
  calibration; the Marx source claim was independently attested and the math referee
  passed with no findings. The field-tier claim collapsed because the result remains
  finite-alphabet/fixed-grid, inference is nonadaptive across neighboring faces, and
  exact inversion has no tractable implementation or substantive Oregon demonstration.
  A future upgrade would need broader outcome/grid theory, genuinely adaptive inference,
  or reproducible applied computation rather than another bounded positioning pass.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 30769955
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 30769955
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# pid_ranksim_pathset_discontinuity / v1 — Downgraded

**Topic.** Common-rank policy-set continuity frontier without complier full support. Observe a binary instrument Z and treatment D=1{U<=p_Z}, with U uniform, 0<p0<p1<1, exclusion and instrument independence; outcomes lie in a fixed ordered K-point alphabet. Impose exactly Marx's existential rank similarity: marginally uniform ranks V0,V1 represent Y0,Y1 and have equal conditional laws given U, with no canonical independent-PIT restriction. For a fixed policy grid containing thresholds below p0 and above p1, prove the sharp joint policy-mean set is the union of at most binomial(2K-2,K-1) common-rank lattice-path allocation polytope images, with one-law constructions and finite failure certificates. Characterize Hausdorff continuity by finite path-survival inclusions and prove a centered local Lipschitz bound; give a legal K=3 KL-contiguous discontinuity and the matching impossibility of globally shrinking honest metric inference. Construct globally honest multinomial outer-set and set-of-sets inversion, then prove projected full-loss active-stratum Gaussian calibration only on certified continuity laws, including specified structural-zero sampling faces. Consumer: Marx's Oregon Health Insurance Experiment extrapolations to discounted Medicaid take-up and expansion to never-treated. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Two fresh presolves derived the common-law path construction, the finite survival criterion, and the observed-law discontinuity. Exact rational checks verified 25 primal allocations, six full-system Farkas exclusions of the separately attainable upper-upper corner, and a common certificate excluding five disappearing paths. The positive-t submodel has d_H(S_s,S_t)=2|s-t| and an explicit folded-normal limit. Stronger pairwise-neighborhood Lipschitzness and path-domain-only bootstrap shortcuts were refuted; global confidence-region inversion remained valid. UNRESOLVED BOTTLENECK: Prove that snapping every active diagonal boundary and value-intercept form of the full projected Hausdorff-loss partition consistently recovers the same homogeneous loss germ at every certified continuous multi-path switch, including relative lower-dimensional sampling cells. EARLY KILL TEST: Compile the projected K=3 Hausdorff-loss partition at a continuous internal-face point with a propensity/grid tie and compare the snapped germ against exact rational perturbations on every feasible tangent face; stop or pivot the regular branch if any loss piece is missed, any local intercept is nonzero, or the germ changes within the recovered stratum. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_ranksim_pathset_discontinuity.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G tier=subfield, score 7.2 below field floor 7.4, salvageable=false; math and citation reviews pass.

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

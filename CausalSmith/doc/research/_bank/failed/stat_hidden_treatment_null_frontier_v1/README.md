---
qid: stat_hidden_treatment_null_frontier
spec: v1
topic: "Sharp connected-interval decision frontier at the hidden-treatment causal-null fiber. In the fixed-J iid Gaussian-outcome, binary-surrogate, binary-negative-control hidden-treatment model with compact ordered mechanisms and known shrinking effect radius, solve the product Gaussian posterior-contrast-fiber decision problem: characterize the minimax worst-case expected length among honest connected intervals by a least-favorable saddle, give certified convergent primal-dual computation and an attaining rule, derive the exact regret of the explicitly coverage-calibrated profile-distance hull including zero-regret conditions and a legal strict-positive-regret regime, and lift the rule uniformly to moving iid nuisance fibers and active constraint cones. Recover centered Gaussian efficiency only when sqrt(n) times every outcome gap and every declared regularity slack diverges. Zhou--Tchetgen Tchetgen arXiv:2405.09080v4 is the off-null anchor and its ADNI section 8 is a prospective reanalysis consumer; credit Zwiernik--Smith for tripod inversion, Drton/Andrews--Cheng/Cox/Schlemper--Moreira for generic singular and weak-ID machinery, and Evans--Hansen--Stark for bounded-normal optimal intervals. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolve derived the randomized endpoint-kernel primal and two-measure dual, reduced the positive q=(.31,.19,.19,.31) null fiber to an exact curved two-parameter Gaussian mean surface, and reduced the legal q=(.41,.09,.09,.41) active face to bounded normal location with scale sqrt(8/41), where strict Neyman--Pearson/Evans--Hansen--Stark duality implies positive profile regret for 0<sqrt(8/41)rho<=2z_.95. It verified profile-hull honesty and checked empty inversions, endpoint randomization, radius faces, topology changes, and interior margins; no same-theorem collision was found. UNRESOLVED BOTTLENECK: Prove uniform local asymptotic equivalence of the iid hidden-treatment experiment, including moving nuisance fibers and every active cone, strongly enough to transfer coverage and expected length of an attaining randomized connected interval. EARLY KILL TEST: On q=(.31,.19,.19,.31), epsilon=.1, sigma=1, and rho in {1,2,4}, run nested certified primal-upper and atomic-dual-lower programs over the exact fiber with tail and endpoint-dither errors; pivot if the certified gap does not decrease or continuum coverage cannot be certified. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_hidden_treatment_null_frontier.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: REVISE
tier_at_derivation: NA
proposal_promise_gap: "An explicit finite primal and dual program with grids, variables, support parametrization, objectives, constraints, and formulas for L_M/U_M, plus candidate-law-scoped legal-fiber assumptions, was never supplied."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "L_M and U_M are only named as quantities assembled from enclosures: no finite primal/dual optimization, action discretization, support parametrization, or formula defines either sequence, so their monotonicity and finite stopping claim has no determinate mathematical object."
  - "The fiber quantifies a candidate law R but every incorporated assumption is written under the fixed R_0, so ‘R satisfies ass:*’ does not state candidate-R restrictions and cannot support the claimed exact legal projection."
reusable_artifacts:
  - "discovery/proto_core.json — final full-data causal model, explicit local causal LAN family, outward-rounded normal-CDF construction, and mesh-modulus ingredients."
  - "reviews/angle2_v2.json — terminal independent review identifying the missing finite certificate programs and candidate-law binding defect."
  - "orchestrator/decision_log.jsonl — twelve bounded repair judgments and validity-gate receipts across all three angles."
seeds_burned:
  - index: 0
    one_liner: "seed:connected-null-saddle"
    reason: "All three proposal angles exhausted bounded repairs; the same load-bearing certificate-definition failure survived multiple mechanistically distinct fixes."
  - index: 1
    one_liner: "seed:uniform-moving-fiber-lift"
    reason: "All three proposal angles exhausted bounded repairs; the same load-bearing certificate-definition failure survived multiple mechanistically distinct fixes."
  - index: 2
    one_liner: "seed:certified-continuum-computation"
    reason: "All three proposal angles exhausted bounded repairs; the same load-bearing certificate-definition failure survived multiple mechanistically distinct fixes."
proof_attempt_summary: |
  Three proposal angles progressively repaired the Gaussian nonregularity criterion, finite-support
  architecture, primitive model scope, reduced covariance geometry, full-data causal semantics,
  explicit normal-CDF enclosures, between-mesh moduli, and the causal-to-Gaussian LAN bridge. The
  central certified-computation theorem nevertheless never defined finite primal and dual programs
  for L_M and U_M, and the final legal fiber still applied baseline-law assumptions to candidate laws;
  a future attempt needs those mathematical objects independently authored before re-proposal.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 54237248
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 54237248
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# stat_hidden_treatment_null_frontier / v1 — Failed

**Topic.** Sharp connected-interval decision frontier at the hidden-treatment causal-null fiber. In the fixed-J iid Gaussian-outcome, binary-surrogate, binary-negative-control hidden-treatment model with compact ordered mechanisms and known shrinking effect radius, solve the product Gaussian posterior-contrast-fiber decision problem: characterize the minimax worst-case expected length among honest connected intervals by a least-favorable saddle, give certified convergent primal-dual computation and an attaining rule, derive the exact regret of the explicitly coverage-calibrated profile-distance hull including zero-regret conditions and a legal strict-positive-regret regime, and lift the rule uniformly to moving iid nuisance fibers and active constraint cones. Recover centered Gaussian efficiency only when sqrt(n) times every outcome gap and every declared regularity slack diverges. Zhou--Tchetgen Tchetgen arXiv:2405.09080v4 is the off-null anchor and its ADNI section 8 is a prospective reanalysis consumer; credit Zwiernik--Smith for tripod inversion, Drton/Andrews--Cheng/Cox/Schlemper--Moreira for generic singular and weak-ID machinery, and Evans--Hansen--Stark for bounded-normal optimal intervals. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolve derived the randomized endpoint-kernel primal and two-measure dual, reduced the positive q=(.31,.19,.19,.31) null fiber to an exact curved two-parameter Gaussian mean surface, and reduced the legal q=(.41,.09,.09,.41) active face to bounded normal location with scale sqrt(8/41), where strict Neyman--Pearson/Evans--Hansen--Stark duality implies positive profile regret for 0<sqrt(8/41)rho<=2z_.95. It verified profile-hull honesty and checked empty inversions, endpoint randomization, radius faces, topology changes, and interior margins; no same-theorem collision was found. UNRESOLVED BOTTLENECK: Prove uniform local asymptotic equivalence of the iid hidden-treatment experiment, including moving nuisance fibers and every active cone, strongly enough to transfer coverage and expected length of an attaining randomized connected interval. EARLY KILL TEST: On q=(.31,.19,.19,.31), epsilon=.1, sigma=1, and rho in {1,2,4}, run nested certified primal-upper and atomic-dual-lower programs over the exact fiber with tail and endpoint-dither errors; pivot if the certified gap does not decrease or continuum coverage cannot be certified. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_hidden_treatment_null_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** REVISE

**Stage 0.5 verdict.** NA

**Banking reason.** Failed after three angles: despite explicit CDF enclosures, mesh moduli, and a causal LAN bridge, the central certificate still asserts convergence and stopping for undefined L_M/U_M programs, while the legal fiber applies R_0 assumptions to an unbound candidate R.

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

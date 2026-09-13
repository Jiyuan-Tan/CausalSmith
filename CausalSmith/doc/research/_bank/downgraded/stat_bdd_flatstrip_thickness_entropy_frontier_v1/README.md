---
qid: stat_bdd_flatstrip_thickness_entropy_frontier
spec: v1
topic: "Flat-strip completion of the thickness-multiplicity frontier for boundary causal traces. This is a new attempt at banked parent stat_bdd_thickness_estimability_frontier, not a retry of its circular annulus witness. Observe iid O=(X,T,Y), X=(R,S) in [-1,1]^2, T=1{R>=0}, on B={(0,s):|s|<=1/2}; target the contrast of unique bounded L-Lipschitz observed-side traces under conditionally sigma-sub-Gaussian errors. For q_t(x,h)=P{X in side t and B_2(x,h)}, impose common lower mass c_m h^kappa. Let J_P(h,u) be the h-packing number of boundary sites with min_t q_t(x,h)<=u. Define isolated laws by one threshold-thin site plus J_P(h,u)<=C_iso{1+h^-1(u/h^2)^(1/(kappa-2))}, and pervasive laws by J_P(h,C_m h^kappa)>=c_J/h. Prove explicit normalized Cartesian product/radial-power laws and Gaussian tent alternatives make both classes nonempty. Prove matched expected-sup risks n^-1/(kappa+2) and (log n/n)^1/(kappa+2), one kappa-free count estimator attaining the pervasive/base rate, and an explicit finite-pattern band with finite-sample simultaneous coverage over every declared nonempty triangular profile union and matching pervasive all-band expected-width lower bound. Do not use circular coordinates, unit-circle packing, the parent's vacuous side-mass placeholder, or claim arbitrary-profile/local-oracle band exactness. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Writing alpha=kappa-2, the flat pervasive density normalizes as (kappa-1)|r|^alpha/4, while the clipped radial-power law has explicit normalizer 4-V_alpha/(alpha+2). Cartesian rectangles and half-balls give uniform one-sided h^kappa masses, including both segment endpoints, and imply the full isolated J_P envelope. Severity-layer peeling yields the isolated no-log upper bound; deterministic boundary grids, finite-pattern calibration, and Gaussian tents give the pervasive lower and band routes. At kappa=3 the pervasive tent product KL is nL^2h^5/(480 sigma^2). Checks covered 78 mass configurations, large-radius clipping, u=1, asymmetric sides, empty counts, and endpoint geometry; constants are uniform only on compact exponent sets bounded away from 2, and the observed-side regressions themselves remain L-Lipschitz. UNRESOLVED BOTTLENECK: Independently formalize the combined normalized flat witness membership and tent-validity theorem, including Borel laws, support, conditional kernels, all mass/profile inequalities, target separations, and Gaussian product KL with the declared target segment. EARLY KILL TEST: Verify the draft's equations (2.1)-(2.6) and construct the actual observed Gaussian laws for both endpoints, clipped radii, u=1, and the smallest admitted exponent; stop if any membership inequality must be assumed. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_bdd_flatstrip_thickness_entropy_frontier.md.\n\nD-1 SCOPE AUDIT (controlling accepted scope): The exploratory topic above proposed matched lower bounds and a finite-pattern simultaneous-confidence-band/width program. Across D-1 revision, the accepted kernel was explicitly narrowed to the total global-bandwidth profile-adaptive estimator and its isolated, pervasive, and regular expected-sup risk conclusions. The confidence-band/width program was withdrawn and is not delivered here; no finite selector, packing event, or anchor construction is a confidence band. Exact endpoint lower bounds, if restated, are attributed supporting converses from the banked parent rather than a new novelty claim. The note’s novelty is simultaneous cross-regime attainment by the present estimator."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "The accepted D-1 scope withdrew the finite-pattern confidence-band program; the resulting severity-net estimator adapts across imposed packing-profile classes, but no primitive density characterization makes those classes broadly verifiable, and A_one/A_perv remain inert setup clauses."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The isolated thin-site clause is not consumed: the oracle upper bound uses only Base plus the isolated envelope, and the lower witness remains in that larger class, so the same matched rate is proved after dropping A_one."
  - "The pervasive-profile clause is inert in the matched route: the upper proof explicitly works on all Base_kappa, while its pervasive witness supplies the lower bound for that larger class; the exact rate therefore does not require A_perv."
  - "The isolated and pervasive regimes are defined directly through the packing functional that drives the oracle penalty, while the note proves only one specially constructed density witness for each regime rather than a usable primitive characterization of designs satisfying those conditions."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_prop_flat_witness_validity.json
  - discovery/solve_lem_empirical_packing_comparison.json
  - discovery/solve_thm_profile_adaptive_estimator.json
  - discovery/solve_prop_same_estimator_endpoint_adaptation.json
seeds_burned: []
proof_attempt_summary: |
  Discovery built a total global-bandwidth severity-net estimator and derived isolated,
  pervasive, and regular-design expected-sup rates, with exact endpoint lower bounds
  attributed to the banked parent. A counterexample killed the stronger pointwise local
  oracle, and the repaired global oracle remained sound. The paper stopped because the
  profile classes were imposed through the same packing functional used by the oracle;
  deriving them from primitive density geometry is a materially reframed future program.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 45370096
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 45370096
  total_tokens_consumed: null
banked_on: "2026-09-12"
---

# stat_bdd_flatstrip_thickness_entropy_frontier / v1 — Downgraded

**Topic.** Flat-strip completion of the thickness-multiplicity frontier for boundary causal traces. This is a new attempt at banked parent stat_bdd_thickness_estimability_frontier, not a retry of its circular annulus witness. Observe iid O=(X,T,Y), X=(R,S) in [-1,1]^2, T=1{R>=0}, on B={(0,s):|s|<=1/2}; target the contrast of unique bounded L-Lipschitz observed-side traces under conditionally sigma-sub-Gaussian errors. For q_t(x,h)=P{X in side t and B_2(x,h)}, impose common lower mass c_m h^kappa. Let J_P(h,u) be the h-packing number of boundary sites with min_t q_t(x,h)<=u. Define isolated laws by one threshold-thin site plus J_P(h,u)<=C_iso{1+h^-1(u/h^2)^(1/(kappa-2))}, and pervasive laws by J_P(h,C_m h^kappa)>=c_J/h. Prove explicit normalized Cartesian product/radial-power laws and Gaussian tent alternatives make both classes nonempty. Prove matched expected-sup risks n^-1/(kappa+2) and (log n/n)^1/(kappa+2), one kappa-free count estimator attaining the pervasive/base rate, and an explicit finite-pattern band with finite-sample simultaneous coverage over every declared nonempty triangular profile union and matching pervasive all-band expected-width lower bound. Do not use circular coordinates, unit-circle packing, the parent's vacuous side-mass placeholder, or claim arbitrary-profile/local-oracle band exactness. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Writing alpha=kappa-2, the flat pervasive density normalizes as (kappa-1)|r|^alpha/4, while the clipped radial-power law has explicit normalizer 4-V_alpha/(alpha+2). Cartesian rectangles and half-balls give uniform one-sided h^kappa masses, including both segment endpoints, and imply the full isolated J_P envelope. Severity-layer peeling yields the isolated no-log upper bound; deterministic boundary grids, finite-pattern calibration, and Gaussian tents give the pervasive lower and band routes. At kappa=3 the pervasive tent product KL is nL^2h^5/(480 sigma^2). Checks covered 78 mass configurations, large-radius clipping, u=1, asymmetric sides, empty counts, and endpoint geometry; constants are uniform only on compact exponent sets bounded away from 2, and the observed-side regressions themselves remain L-Lipschitz. UNRESOLVED BOTTLENECK: Independently formalize the combined normalized flat witness membership and tent-validity theorem, including Borel laws, support, conditional kernels, all mass/profile inequalities, target separations, and Gaussian product KL with the declared target segment. EARLY KILL TEST: Verify the draft's equations (2.1)-(2.6) and construct the actual observed Gaussian laws for both endpoints, clipped radii, u=1, and the smallest admitted exponent; stop if any membership inequality must be assumed. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_bdd_flatstrip_thickness_entropy_frontier.md.

D-1 SCOPE AUDIT (controlling accepted scope): The exploratory topic above proposed matched lower bounds and a finite-pattern simultaneous-confidence-band/width program. Across D-1 revision, the accepted kernel was explicitly narrowed to the total global-bandwidth profile-adaptive estimator and its isolated, pervasive, and regular expected-sup risk conclusions. The confidence-band/width program was withdrawn and is not delivered here; no finite selector, packing event, or anchor construction is a confidence band. Exact endpoint lower bounds, if restated, are attributed supporting converses from the banked parent rather than a new novelty claim. The note’s novelty is simultaneous cross-regime attainment by the present estimator.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** Stage 0.5 BELOW NOVELTY FLOOR: tier incremental < floor field and NOT salvageable in scope.

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

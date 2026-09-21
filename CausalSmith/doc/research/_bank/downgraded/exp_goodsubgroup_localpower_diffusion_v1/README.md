---
qid: exp_goodsubgroup_localpower_diffusion
spec: v1
topic: "Minimax local-power frontier for confirmatory subgroup enrichment under a fixed closed e-test. Fix K>=2 prespecified disjoint subgroups, known unit Gaussian variance, alpha=.05, positive normalized discovery weights, e-alternatives delta_j=1, uniform intersection e-value weights, horizon n, and a finite null-boundary-closed scenario set H0 subset [-H,H]^K. Predictable recruitment observes Y_i~N(h_{A_i}/sqrt(n),1). Use elementary e-processes exp(S_j/sqrt(n)-N_j/(2n)), arithmetic-mean intersection e-values, and closed testing at threshold 20, giving exact strong FWER under every policy. Define weighted missed-discovery loss, the scenario-aware oracle value, and minimax regret over H0. Prove convergence to the corresponding controlled score-diffusion frontier; derive the least-favorable-prior/posterior-state reduction; handle the discontinuous terminal rejection surfaces; construct predictable finite-n policies attaining the frontier; and give monotone upper/lower dynamic-programming schemes with a computable epsilon certificate. Report simultaneously calibrated one-sided confidence sequences by null-indexed e-process inversion. Consumer: rpact population-enrichment workflows and interAdapt finite-stage trial designs. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A derived virtual-score transformation feeds a policy X-epsilon Q and realizes its original law under common drift h+epsilon, while actual e-values gain exp(epsilon Q_j); the observed-law KL cost is epsilon^2/2. Combined with a small-information Brownian bound, this gives an explicit O(sqrt(delta)) initial-state squeeze between continuous terminal envelopes despite legal adaptive boundary atoms. Finite-scenario convex risk geometry yields minimax duality, the Gaussian grid embeds exactly, and the full K=2,n=2 problem reduces to one-dimensional Gaussian integrals with floating-point V_2 approximately 0.0001947683. Checks covered hit-and-freeze boundary atoms, zero allocations, null-only scenarios, the normalized n=1 witness, least-favorable best-response failure, and recent 2026 diffusion/e-process/enrichment work. These derivations are unverified and the numerical value is not interval-certified. UNRESOLVED BOTTLENECK: Prove generalized-terminal comparison and uniqueness for the degenerate posterior-control HJB on its viable state domain; the initial-state envelope squeeze alone does not cover every off-origin boundary state. EARLY KILL TEST: Reprove the quantitative envelope lemma for K=2 under both hit-and-freeze and unsampled-subgroup policies; any counterexample to admissibility or the coordinatewise envelope inequality, or any forced-exploration requirement, should pivot or stop. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_goodsubgroup_localpower_diffusion.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "No implemented solver or nontrivial interval-certified frontier run, and no finite-sample optimality theorem; delivered result is a qualitative validated diffusion/Bellman certificate for one fixed closed e-test."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The delivered contribution is an asymptotic diffusion-limit characterization and qualitative computability result for one fixed Gaussian closed e-test, not a finite-sample optimality theorem or a numerically realized local-power frontier."
  - "The certificate theorem proves eventual termination through an abstract enumeration, but the package supplies neither an implemented algorithm nor a nontrivial interval-certified run, so the claimed rpact and interAdapt usefulness is not demonstrated."
  - "D0.5.G: tier=subfield; paper_score_ceiling=6.7 < field floor=7.4; salvageable=false; meets_floor=false."
reusable_artifacts:
  - discovery/core.json
  - discovery/solve_thm_boundary_stable_frontier.json
  - discovery/solve_thm_certified_dynamic_program.json
  - discovery/solve_prop_k2_n1_sanity_reduction.json
  - discovery/writeup.tex
seeds_burned: []
proof_attempt_summary: |
  The run derived exact Gaussian-grid embedding, initial-state minimax diffusion-value convergence,
  conditional-kernel policy transfer, finite-scenario saddle structure, and a qualitative validated
  Bellman certificate. Repeated D-stage audits repaired the likelihood-multiplier modulus, comparator
  positioning, reverse policy transfer, and guard/taper ledger; the final math and decision referees
  passed with no findings. The package remained below the field floor because it lacks an implemented
  solver, a nontrivial interval-certified frontier computation, and finite-sample optimality.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 34586528
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 34586528
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# exp_goodsubgroup_localpower_diffusion / v1 — Downgraded

**Topic.** Minimax local-power frontier for confirmatory subgroup enrichment under a fixed closed e-test. Fix K>=2 prespecified disjoint subgroups, known unit Gaussian variance, alpha=.05, positive normalized discovery weights, e-alternatives delta_j=1, uniform intersection e-value weights, horizon n, and a finite null-boundary-closed scenario set H0 subset [-H,H]^K. Predictable recruitment observes Y_i~N(h_{A_i}/sqrt(n),1). Use elementary e-processes exp(S_j/sqrt(n)-N_j/(2n)), arithmetic-mean intersection e-values, and closed testing at threshold 20, giving exact strong FWER under every policy. Define weighted missed-discovery loss, the scenario-aware oracle value, and minimax regret over H0. Prove convergence to the corresponding controlled score-diffusion frontier; derive the least-favorable-prior/posterior-state reduction; handle the discontinuous terminal rejection surfaces; construct predictable finite-n policies attaining the frontier; and give monotone upper/lower dynamic-programming schemes with a computable epsilon certificate. Report simultaneously calibrated one-sided confidence sequences by null-indexed e-process inversion. Consumer: rpact population-enrichment workflows and interAdapt finite-stage trial designs. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A derived virtual-score transformation feeds a policy X-epsilon Q and realizes its original law under common drift h+epsilon, while actual e-values gain exp(epsilon Q_j); the observed-law KL cost is epsilon^2/2. Combined with a small-information Brownian bound, this gives an explicit O(sqrt(delta)) initial-state squeeze between continuous terminal envelopes despite legal adaptive boundary atoms. Finite-scenario convex risk geometry yields minimax duality, the Gaussian grid embeds exactly, and the full K=2,n=2 problem reduces to one-dimensional Gaussian integrals with floating-point V_2 approximately 0.0001947683. Checks covered hit-and-freeze boundary atoms, zero allocations, null-only scenarios, the normalized n=1 witness, least-favorable best-response failure, and recent 2026 diffusion/e-process/enrichment work. These derivations are unverified and the numerical value is not interval-certified. UNRESOLVED BOTTLENECK: Prove generalized-terminal comparison and uniqueness for the degenerate posterior-control HJB on its viable state domain; the initial-state envelope squeeze alone does not cover every off-origin boundary state. EARLY KILL TEST: Reprove the quantitative envelope lemma for K=2 under both hit-and-freeze and unsampled-subgroup policies; any counterexample to admissibility or the coordinatewise envelope inequality, or any forced-exploration requirement, should pivot or stop. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_goodsubgroup_localpower_diffusion.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G graded subfield with paper_score_ceiling 6.7 below the field floor 7.4; salvageable=false, while math and decision referees both passed with no findings.

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

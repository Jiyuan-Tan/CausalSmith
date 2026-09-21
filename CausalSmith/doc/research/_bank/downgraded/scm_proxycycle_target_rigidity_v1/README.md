---
qid: scm_proxycycle_target_rigidity
spec: v1
topic: "Boundary-complete proxy-cycle target rigidity for selected probabilities of causation. In the exact finite Shingaki--Yoshida--Kuroki four-response-type model with binary treatment and outcome, finite proxies, latent confounding, outcome-dependent selection, positive observed selected tables, and nonnegative latent proxy mechanisms, define the full normalized response-cycle factorization fiber. Treat separately the two-proxy design with supplied positive population cell margins and the relevant-IV design with unknown margins and shared-Z equations. Prove an observable rank/support/cycle criterion that is necessary and sufficient for PN/PS constancy on every nonempty mixed-rank and boundary fiber. Emit rational formulas where possible and exact algebraic certificates otherwise; on every nonrigid stratum emit two legal full SCMs with identical observables and margins but different targets, requiring strict-positive twins only in interior strata. Prove termination and fixed-alphabet exact output bounds, stable Wald inference on separated rigid strata, and multinomial confidence-fiber inversion near rank/support transitions. Apply the atlas to the GEUVADIS SWAP70-to-SBF2-AS1 selected-expression analysis. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The score-blind presolve derived the full nonnegative cycle-to-SCM lift, a complete all-rank-two orientation-box atlas including an identified assignment boundary, the stacked-rank-four affine-annihilation branch, and an exact relevant-IV residual-ratio/forest reduction with one cycle-product constraint. A complete mixed chart yields a cubic nuisance root and legal target-changing completions; fourteen mixed two-proxy and eight unknown-margin IV instances were checked exactly. Forced-zero boundaries, coincident lines, inactive rows, hidden Z splits, cross-face comparisons, and current NMF/counterfactual collisions were tested. UNRESOLVED BOTTLENECK: Prove explicit mixed-support cycle target elimination across every real component and support face, with target agreement tests or legal twin extraction, without reducing the classification to generic two-copy quantifier elimination. EARLY KILL TEST: Compile the residual-ratio/forest rules for ternary inactive-row and coincident-endpoint patterns and compare them with exact full-fiber elimination on independently sampled rational observable tables; any missed target-varying component kills the classifier, while an irrational singleton must use the authorized exact-algebraic branch. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_proxycycle_target_rigidity.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  - "The promised observable rank/support/cycle criterion is replaced by generic raw-fiber semialgebraic sampling plus an existential unequal-target query."
  - "Explicit target elimination and cross-chart agreement over every rank-two, L/R/E/D, support-face, coincident-endpoint, and residual-forest chart remains the unresolved oeq:mixed-support-elimination."
  - "The cited randomized submodel identification does not prove unrestricted design-A-fiber rigidity."
  - "The GEUVADIS contribution is only an audit protocol because the numerical table and binarization thresholds were not recovered."
reusable_artifacts:
  - discovery/writeup.tex
  - discovery/core.json
  - discovery/solve_thm_full_rigidity_atlas.tex
  - discovery/solve_thm_anchor_agreement_and_boundary_coverage.tex
  - discovery/solve_thm_termination_and_exact_bounds.tex
  - discovery/solve_thm_separated_wald.tex
  - discovery/vcs/
  - orchestrator/decision_log.jsonl
seeds_burned: []
proof_attempt_summary: |
  The derivation built a normalized SCM fiber, structural support charts, a direct raw-fiber exact decision procedure, legal witness extraction, fixed-alphabet bounds, and separated-stratum inference. It did not complete the advertised explicit target elimination and agreement theorem across every mixed-support component; the unrestricted experimental-design transfer, three quantitative source matches, and the GEUVADIS application also remain incomplete. The surviving package is a reusable incremental decidability-and-atlas note, while a future field-level re-raise needs a genuinely new mixed-support elimination theorem and the missing empirical inputs.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 57544365
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 57544365
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# scm_proxycycle_target_rigidity / v1 — Downgraded

**Topic.** Boundary-complete proxy-cycle target rigidity for selected probabilities of causation. In the exact finite Shingaki--Yoshida--Kuroki four-response-type model with binary treatment and outcome, finite proxies, latent confounding, outcome-dependent selection, positive observed selected tables, and nonnegative latent proxy mechanisms, define the full normalized response-cycle factorization fiber. Treat separately the two-proxy design with supplied positive population cell margins and the relevant-IV design with unknown margins and shared-Z equations. Prove an observable rank/support/cycle criterion that is necessary and sufficient for PN/PS constancy on every nonempty mixed-rank and boundary fiber. Emit rational formulas where possible and exact algebraic certificates otherwise; on every nonrigid stratum emit two legal full SCMs with identical observables and margins but different targets, requiring strict-positive twins only in interior strata. Prove termination and fixed-alphabet exact output bounds, stable Wald inference on separated rigid strata, and multinomial confidence-fiber inversion near rank/support transitions. Apply the atlas to the GEUVADIS SWAP70-to-SBF2-AS1 selected-expression analysis. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The score-blind presolve derived the full nonnegative cycle-to-SCM lift, a complete all-rank-two orientation-box atlas including an identified assignment boundary, the stacked-rank-four affine-annihilation branch, and an exact relevant-IV residual-ratio/forest reduction with one cycle-product constraint. A complete mixed chart yields a cubic nuisance root and legal target-changing completions; fourteen mixed two-proxy and eight unknown-margin IV instances were checked exactly. Forced-zero boundaries, coincident lines, inactive rows, hidden Z splits, cross-face comparisons, and current NMF/counterfactual collisions were tested. UNRESOLVED BOTTLENECK: Prove explicit mixed-support cycle target elimination across every real component and support face, with target agreement tests or legal twin extraction, without reducing the classification to generic two-copy quantifier elimination. EARLY KILL TEST: Compile the residual-ratio/forest rules for ternary inactive-row and coincident-endpoint patterns and compare them with exact full-fiber elimination on independently sampled rational observable tables; any missed target-varying component kills the classifier, while an irrational singleton must use the authorized exact-algebraic branch. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_proxycycle_target_rigidity.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** D0.5 confirms a sound incremental decidability-and-atlas note, but explicit mixed-support target elimination, unrestricted design-A transfer, and the GEUVADIS audit remain undelivered, capping the package below the field floor.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

The D0.5 panel scored the delivered package at 5.3 against the 7.4 field floor and found no bounded repair capable of closing that gap. The independent terminal gate confirmed `terminal:below-floor` and recommended `reraise_status: re-raise`; no formalization stage was launched under the September 2026 library-refactor freeze.

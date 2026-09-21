---
qid: exp_rarearm_levy_frontier
spec: v1
topic: "Atom-safe critical inference for rare-arm adaptive experiments. Fix binary-arm finite populations with bounded potential outcomes, logged predictable assignment probabilities, deterministic bounded Lipschitz critical intensity and signed-residual profiles with supplied uniform moduli, and an explicit early quadratic-variation envelope. Construct a computable stopped adaptive-to-Bernoulli-to-Poisson finite-transfer bound and logged-profile enclosure; use certified profile nets and signed-mark convolution to return confidence intervals with uniform finite-experiment coverage and oracle alpha/radius slack, including atomic laws. Prove that the exact late-ramp pair forces every 95%-honest confidence set to have diameter at least 1/8 with limiting probability at least 0.60710678, while a declared high-hazard subfamily admits robust radius at most 0.442M plus arbitrarily small certification slack. Keep HT distributional limits distinct from all-estimator information bounds. Consumer: Liberali et al.'s GUSTO-1/EUROPA adaptive-randomization analysis, conditional on a prespecified expected-endpoint profile bridge. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A stopped coupling, Bernoulli-to-Poisson comparison, Riemann-grid error, random-residual mark bound, and deterministic log-enclosure contraction were derived. The transfer chain uses a predictable stopping rule, summed propensity-probability errors, a Le Cam Bernoulli-to-Poisson step, and Lipschitz Riemann control. Campbell/isometry bounds control random residual marks and early quadratic variation. Rational profile nets, interval elementary functions, and deterministic threshold monotonicity make calibration effective rather than existential. A selection-safe monotone-threshold lemma handles calibration from the same propensity log. Directed BigInt convolution on a 16-bin envelope certified the two-sign ramp expectation below 0.037934 at radius 13/32, while the common void event tends to 0.70710678; a full signed-mark tail calculation gives 0.049830 at radius 0.442M on the high-hazard family. Checks covered completed-log conditioning, pathwise selection, early exceptional propensities, finite-activity atoms, quantile discontinuities, zero and signed profiles, finite-n normalization, and legal high-hazard membership. The constant-profile law was identified as generalized Dickman rather than a new obstruction, so the proposed contribution is the uniform finite-transfer and profile-adaptive interval theorem. UNRESOLVED BOTTLENECK: Independently implement and prove the end-to-end logged-profile-net convolution certificate, including stopped-coupling and deterministic-threshold error allocation, uniformly over the declared adaptive class. EARLY KILL TEST: Reproduce the exact c=a=1/2, delta=1/4 ramp certificate and preserve both the 0.60710678 diameter lower bound and the 0.442M high-hazard radius; any violation stops the calibration route. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_rarearm_levy_frontier.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  - "The delivered core is a uniform finite-transfer and atom-safe coverage theorem for a tightly structured deterministic-profile subclass, not inference over general rare-arm adaptive experiments."
  - "The exact diameter frontiers are proved and attained only within selected two-sign late-void experiments; on Li and Zhao's broader class only the converses transfer, with no globally matching confidence procedure."
  - "The exhaustive certificate is justified through a net, truncation, and convolution construction but has neither a complexity guarantee nor an end-to-end implementation."
  - "Publication cleanup: replace the generalized-Dickman Poisson representation's Bhattacharjee--Goldstein 2019 attribution with the attested Bhattacharjee--Molchanov 2020 source."
  - "Publication cleanup: position Barbour--Utev 1999 substantively against the finite stopped signed-mark transfer, or remove it."
reusable_artifacts:
  - "discovery/core.json — maximized theorem graph with finite transfer, atom-safe calibration, clipped-ramp, and joint intensity/residual frontiers"
  - "discovery/writeup.tex — fully discharged 23-proved/3-cited derivation note with one explicit polynomial-complexity OEQ"
  - "discovery/solve_thm_certified_coverage_oracle.json — finite adaptive-to-Poisson transfer and certified coverage construction"
  - "discovery/solve_thm_joint_intensity_residual_clipped_ramp_frontier.json — optimized q-star/H two-elbow converse construction"
seeds_burned:
  - index: 0
    one_liner: "seed:joint-critical-transfer-frontier"
    reason: "The sole field-target proposal angle was fully derived and maximized but graded subfield because its positive procedure remains on a supplied structured profile class and its matching attainment is pair-specific."
proof_attempt_summary: |
  The run proved a computable finite adaptive-to-signed-compound-Poisson transfer,
  atom-safe coverage with oracle slack, and exact pairwise late-void frontiers,
  including clipped residual and intensity optimization. The field claim collapsed
  because the positive procedure still assumes an every-n structured profile and
  early-QV contract, while matching attainment is pair-specific and the practical
  certificate lacks polynomial complexity or an end-to-end implementation. A field
  re-raise needs a new larger-class kernel or a genuine consumer bridge, not another
  bounded revision of this note.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 30839121
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 30839121
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# exp_rarearm_levy_frontier / v1 — Downgraded

**Topic.** Atom-safe critical inference for rare-arm adaptive experiments. Fix binary-arm finite populations with bounded potential outcomes, logged predictable assignment probabilities, deterministic bounded Lipschitz critical intensity and signed-residual profiles with supplied uniform moduli, and an explicit early quadratic-variation envelope. Construct a computable stopped adaptive-to-Bernoulli-to-Poisson finite-transfer bound and logged-profile enclosure; use certified profile nets and signed-mark convolution to return confidence intervals with uniform finite-experiment coverage and oracle alpha/radius slack, including atomic laws. Prove that the exact late-ramp pair forces every 95%-honest confidence set to have diameter at least 1/8 with limiting probability at least 0.60710678, while a declared high-hazard subfamily admits robust radius at most 0.442M plus arbitrarily small certification slack. Keep HT distributional limits distinct from all-estimator information bounds. Consumer: Liberali et al.'s GUSTO-1/EUROPA adaptive-randomization analysis, conditional on a prespecified expected-endpoint profile bridge. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A stopped coupling, Bernoulli-to-Poisson comparison, Riemann-grid error, random-residual mark bound, and deterministic log-enclosure contraction were derived. The transfer chain uses a predictable stopping rule, summed propensity-probability errors, a Le Cam Bernoulli-to-Poisson step, and Lipschitz Riemann control. Campbell/isometry bounds control random residual marks and early quadratic variation. Rational profile nets, interval elementary functions, and deterministic threshold monotonicity make calibration effective rather than existential. A selection-safe monotone-threshold lemma handles calibration from the same propensity log. Directed BigInt convolution on a 16-bin envelope certified the two-sign ramp expectation below 0.037934 at radius 13/32, while the common void event tends to 0.70710678; a full signed-mark tail calculation gives 0.049830 at radius 0.442M on the high-hazard family. Checks covered completed-log conditioning, pathwise selection, early exceptional propensities, finite-activity atoms, quantile discontinuities, zero and signed profiles, finite-n normalization, and legal high-hazard membership. The constant-profile law was identified as generalized Dickman rather than a new obstruction, so the proposed contribution is the uniform finite-transfer and profile-adaptive interval theorem. UNRESOLVED BOTTLENECK: Independently implement and prove the end-to-end logged-profile-net convolution certificate, including stopped-coupling and deterministic-threshold error allocation, uniformly over the declared adaptive class. EARLY KILL TEST: Reproduce the exact c=a=1/2, delta=1/4 ramp certificate and preserve both the 0.60710678 diameter lower bound and the 0.442M high-hazard radius; any violation stops the calibration route. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_rarearm_levy_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G tier=subfield < floor=field and NOT salvageable in scope; field lift requires a new kernel or application, not a bounded repair.

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

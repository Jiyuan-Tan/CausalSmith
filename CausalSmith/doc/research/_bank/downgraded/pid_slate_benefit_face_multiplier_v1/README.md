---
qid: pid_slate_benefit_face_multiplier
spec: v1
topic: "Least-favourable face-multiplier inference for sharp survivor-complier benefit bounds. Fix finite covariate support J>=2 and ordered outcome support K>=3 in the conditional-IV model with consistency, exclusion, no defiers, weak cellwise selection monotonicity, fixed covariate and instrument-overlap lower bounds, aggregate survivor-complier mass bounded away from zero, and a nonredundant raw-capacity covariance eigenvalue band; impose no lower bound on individual cell survivor masses, no sign margin on the survivor-mass gap, and no Ferrers-cut separation. Starting from the banked exact selected-complier partial-transport capacities and closed sharp benefit endpoints, use the unscreened nonnegative-projection plug-in and define the least-favourable survivor-support face envelope by retaining every capacity, zero-gap, survivor-minimum, lower-cut, upper-cut, and mass-cap branch within a_n, where a_n tends to zero and sqrt(n)a_n tends to infinity. Prove that the conditional multiplier quantile of the finite retained-gradient maximum gives uniform root-n coverage of the entire sharp identified interval over triangular arrays with simultaneous ties and changing survivor support, without deterministic padding; prove oracle face-envelope equivalence on separated faces; and prove strict asymptotic undercoverage of calibration that keeps only the empirical maximizing/minimizing branches and empirically positive survivor cells on the specified two-covariate, three-outcome contiguous witness. Computation must use the explicit finite min-cut branch gradients and no latent LP. Consumer: the Chen-Flores Job Corps principal-stratification wage analysis, which could report honest uncertainty for the fraction of always-employed compliers whose ordered wage improves. PRESOLVE EVIDENCE REQUIRING VERIFICATION: an unconditional-capacity reparameterization makes both endpoints finite piecewise linear-fractional maps; a finite pathwise secant-gradient argument dominates both signed endpoint errors by retained gradients. The legal changing-support witness keeps raw-capacity contrast covariance eigenvalues in [1/4,1], and direct Gaussian-limit diagnostics show material single-face undercoverage; checks covered the active upper mass cap, denominator derivatives, projection-release directions, screening bias, zero-gradient calibration, and generic directional-inference collisions. UNRESOLVED BOTTLENECK: certify that the explicit Gaussian witness has rejection probability above 0.4 at nominal alpha=0.4; the derived finite branch decomposition reduces this to Gaussian polyhedral probabilities. EARLY KILL TEST: independently implement and certify a lower bound exceeding 0.4 for the conservative Gaussian rejection event at kappa=1; failure after correcting the implementation should pivot the witness claim or stop the kernel. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/mill/scratch/mill-w10/presolve_pid_slate_benefit_face_multiplier.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "Complete the explicit Gaussian polyhedral calculation and prove strict undercoverage above 0.4 at nominal alpha 0.4 for the precisely defined optimizer-only positive-survivor shortcut; also make localization constants explicit and position the automatic face rule theorem-by-theorem."
reusable: unknown
reraise_status: retry
gap_reasons:
  - "The note proves a fixed-dimensional face-envelope coverage theorem and oracle equivalence for one imported piecewise linear-fractional endpoint map, but this remains a narrow application of directional inference and generalized moment selection rather than a field-level framework."
  - "The research brief's strict undercoverage result is not delivered: the witness proposition proves only legality, endpoint geometry, and covariance bounds, while the limitation section expressly withdraws every undercoverage claim."
  - "The population inner-face family also depends on unspecified deterministic localization constants, which must be made explicit for the uniform theorem to be fully reproducible."
reusable_artifacts:
  - "discovery/core.json — proved finite face-envelope graph, corrected strict-benefit cut orientation, automatic studentized retention rule, and complete boundary witness."
  - "discovery/writeup.tex — derivation note with the finite secant-gradient and Gaussian multiplier arguments."
  - "discovery/gaps.json — bounded literature map and open-problem harvest."
  - "reviews/review_math.json — clean soundness verdict and verified Lu–Ding–Dasgupta citation match."
seeds_burned: []
proof_attempt_summary: |
  D0 proved the finite-dimensional no-padding whole-set coverage theorem, oracle face equivalence,
  an automatic studentized face-retention rule, the ordinary ordinal-benefit reduction, and legality
  of the changing-support witness after correcting the benefit/harm cut orientation. The math referee
  passed, but the promised strict undercoverage calculation for the optimizer-only shortcut was not
  delivered; a retry must certify its explicit Gaussian polyhedral probability and make the remaining
  localization constants and theorem-level positioning fully explicit.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 21550410
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 21550410
  total_tokens_consumed: null
banked_on: "2026-09-10"
---

# pid_slate_benefit_face_multiplier / v1 — Downgraded

**Topic.** Least-favourable face-multiplier inference for sharp survivor-complier benefit bounds. Fix finite covariate support J>=2 and ordered outcome support K>=3 in the conditional-IV model with consistency, exclusion, no defiers, weak cellwise selection monotonicity, fixed covariate and instrument-overlap lower bounds, aggregate survivor-complier mass bounded away from zero, and a nonredundant raw-capacity covariance eigenvalue band; impose no lower bound on individual cell survivor masses, no sign margin on the survivor-mass gap, and no Ferrers-cut separation. Starting from the banked exact selected-complier partial-transport capacities and closed sharp benefit endpoints, use the unscreened nonnegative-projection plug-in and define the least-favourable survivor-support face envelope by retaining every capacity, zero-gap, survivor-minimum, lower-cut, upper-cut, and mass-cap branch within a_n, where a_n tends to zero and sqrt(n)a_n tends to infinity. Prove that the conditional multiplier quantile of the finite retained-gradient maximum gives uniform root-n coverage of the entire sharp identified interval over triangular arrays with simultaneous ties and changing survivor support, without deterministic padding; prove oracle face-envelope equivalence on separated faces; and prove strict asymptotic undercoverage of calibration that keeps only the empirical maximizing/minimizing branches and empirically positive survivor cells on the specified two-covariate, three-outcome contiguous witness. Computation must use the explicit finite min-cut branch gradients and no latent LP. Consumer: the Chen-Flores Job Corps principal-stratification wage analysis, which could report honest uncertainty for the fraction of always-employed compliers whose ordered wage improves. PRESOLVE EVIDENCE REQUIRING VERIFICATION: an unconditional-capacity reparameterization makes both endpoints finite piecewise linear-fractional maps; a finite pathwise secant-gradient argument dominates both signed endpoint errors by retained gradients. The legal changing-support witness keeps raw-capacity contrast covariance eigenvalues in [1/4,1], and direct Gaussian-limit diagnostics show material single-face undercoverage; checks covered the active upper mass cap, denominator derivatives, projection-release directions, screening bias, zero-gradient calibration, and generic directional-inference collisions. UNRESOLVED BOTTLENECK: certify that the explicit Gaussian witness has rejection probability above 0.4 at nominal alpha=0.4; the derived finite branch decomposition reduces this to Gaussian polyhedral probabilities. EARLY KILL TEST: independently implement and certify a lower bound exceeding 0.4 for the conservative Gaussian rejection event at kappa=1; failure after correcting the implementation should pivot the witness claim or stop the kernel. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/mill/scratch/mill-w10/presolve_pid_slate_benefit_face_multiplier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G graded the delivered fixed-dimensional face-envelope paper incremental below the field floor: the strict shortcut-undercoverage theorem was not delivered, so the retention rule lacks a rigorously demonstrated failure target.

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

The sound inference spine and corrected capacity orientation should be reused. A future retry should
start from the explicit witness and attack the Gaussian polyhedral probability certificate first;
without that negative theorem, the package remains below the field novelty floor.

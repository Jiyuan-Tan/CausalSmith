---
qid: pid_nested_tvsace_capacity
spec: v1
topic: "Sharp nested-survivor capacity for simultaneous TV-SACE and RM-SACE surfaces. Fix finite X, conditional exchangeability with treatment overlap, independent administrative censoring with at-risk probability bounded below through the full analysis horizon tau, semicompeting-risk order R(z)<D(z) for finite R(z), terminal-survival monotonicity D(1)>=D(0), bounded-Lipschitz finite-part event densities, and positive always-survivor mass on the target index set. Prove that the standardized compatible surface is exactly the image of conditional couplings nu_x=law(D(0),R(1)|X=x) satisfying all readmission-specific survivor-dominance inequalities. Give measurable full-law lifts, O(m^2) finite-grid chain flows and support duals, fixed-cohort cut formulas with common CDF extremizers and sharp RM integration, strict cross-cohort support examples, continuous support convergence, observable censoring-moment finite-sample outer sets, and multiplier bands on regular compact regions. Consumer: Comment et al., Biometrical Journal 2025, subject to follow-up, coding, monotonicity and covariate audits. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Conditional stochastic-order and quantile-lift derivations yield the iff projection; integer matching and suffix cuts yield the chain flow and common fixed-cohort extrema. A smooth three-horizon law has signed support [-1/20,1/4] versus rectangular [-3/20,7/20]; a five-level case has jointly attained prefix intervals [0,.09], [0,.19], [.11,.31]. Full-versus-projected LP checks agreed numerically, and full-horizon follow-up distinguishes the prior 0.6-versus-1 censoring counterexample. Observable at-risk/completion moment brackets plus Hoeffding regions give outer containment at changing faces. UNRESOLVED BOTTLENECK: Prove the joint marked-product-limit/IPCW functional CLT and estimated-censoring expansion through tau, then compose it with the unique-cut derivative for consistent simultaneous multiplier bands with negligible grid bias. EARLY KILL TEST: Recompute the five-level full-law and projected-flow problem at gamma=.4, requiring all event-set cuts, prefix extrema [0,.09], [0,.19], [.11,.31], guard containment, and distinct .2-versus-0 observed death cells; any failure stops continuous inference. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_nested_tvsace_capacity.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "The terminal-monotonicity-restricted population characterization is sound, but shrinking outer-set rates, simultaneous endpoint inference, the marked-process CLT, multiplier validity, and an applied demonstration remain open."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The exact identified-set characterization applies only after adding terminal monotonicity D(0) ≤ D(1), and does not characterize Comment et al.'s unrestricted class."
  - "The note proves population sharpness, common fixed-cohort extrema, exact grid computation, continuous-grid convergence, and finite-sample outer containment, but proves neither shrinking outer sets nor simultaneous endpoint inference."
  - "The marked-process functional CLT, estimated-censoring expansion, root-n grid-bias control, and multiplier validity remain open, so the advertised clinical consumer lacks a usable simultaneous inferential procedure or applied demonstration."
reusable_artifacts:
  - discovery/core.json
  - discovery/solve_thm_iff_capacity_projection.tex
  - discovery/solve_prop_strict_cross_cohort_support.tex
  - discovery/solve_thm_continuous_grid_convergence.tex
  - discovery/solve_thm_finite_sample_outer_set.tex
seeds_burned: []
proof_attempt_summary: |
  Discovery established a sound terminal-monotonicity-restricted marked-capacity characterization, measurable full-law lifts, common fixed-cohort extremizers, quadratic finite-grid computation, bounded-density grid convergence, and finite-sample outer containment; the math panel passed after all cited lemmas were verified. The field-level promise collapsed because the result does not cover the motivating unrestricted class and the simultaneous inference route, shrinking-rate theorem, and applied demonstration remained open. A future re-raise should reuse the capacity graph and exact witnesses but re-anchor the proposal or supply the missing marked-process CLT, grid-bias control, multiplier validity, and application.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 32748327
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 32748327
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# pid_nested_tvsace_capacity / v1 — Downgraded

**Topic.** Sharp nested-survivor capacity for simultaneous TV-SACE and RM-SACE surfaces. Fix finite X, conditional exchangeability with treatment overlap, independent administrative censoring with at-risk probability bounded below through the full analysis horizon tau, semicompeting-risk order R(z)<D(z) for finite R(z), terminal-survival monotonicity D(1)>=D(0), bounded-Lipschitz finite-part event densities, and positive always-survivor mass on the target index set. Prove that the standardized compatible surface is exactly the image of conditional couplings nu_x=law(D(0),R(1)|X=x) satisfying all readmission-specific survivor-dominance inequalities. Give measurable full-law lifts, O(m^2) finite-grid chain flows and support duals, fixed-cohort cut formulas with common CDF extremizers and sharp RM integration, strict cross-cohort support examples, continuous support convergence, observable censoring-moment finite-sample outer sets, and multiplier bands on regular compact regions. Consumer: Comment et al., Biometrical Journal 2025, subject to follow-up, coding, monotonicity and covariate audits. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Conditional stochastic-order and quantile-lift derivations yield the iff projection; integer matching and suffix cuts yield the chain flow and common fixed-cohort extrema. A smooth three-horizon law has signed support [-1/20,1/4] versus rectangular [-3/20,7/20]; a five-level case has jointly attained prefix intervals [0,.09], [0,.19], [.11,.31]. Full-versus-projected LP checks agreed numerically, and full-horizon follow-up distinguishes the prior 0.6-versus-1 censoring counterexample. Observable at-risk/completion moment brackets plus Hoeffding regions give outer containment at changing faces. UNRESOLVED BOTTLENECK: Prove the joint marked-product-limit/IPCW functional CLT and estimated-censoring expansion through tau, then compose it with the unique-cut derivative for consistent simultaneous multiplier bands with negligible grid bias. EARLY KILL TEST: Recompute the five-level full-law and projected-flow problem at gamma=.4, requiring all event-set cuts, prefix extrema [0,.09], [0,.19], [.11,.31], guard containment, and distinct .2-versus-0 observed death cells; any failure stops continuous inference. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_nested_tvsace_capacity.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** Not salvageable within scope — bank downgraded, or re-anchor the proposal; paper_score_ceiling 6.5 < 7.4 despite a passing math panel.

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

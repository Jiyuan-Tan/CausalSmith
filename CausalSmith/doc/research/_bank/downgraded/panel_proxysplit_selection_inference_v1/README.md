---
qid: panel_proxysplit_selection_inference
spec: v1
topic: "Wald-symmetry frontier for outcome-selected proximal synthetic-control roles. Fix two predeclared square donor/proxy partitions in a stationary geometrically beta-mixing panel with fixed moment, bridge-rank, positive ATT influence-variance, and nondegenerate ridge-loss-contrast margins. The treated unit has post outcome Y(0)+Delta and target tau=E Delta; every partition is a valid proximal bridge. Select between the roles using the same pre-period lambda=1 ridge loss and estimate the conventional proximal ATT. Under every bounded root-T selector gap, derive its selected-Gaussian limit and the exact symmetric-Wald coverage functional. Prove: exact selector ties protect every symmetric Wald level; coverage is nominal for every local gap iff the two standardized ATT statistics have equal squared correlations with the selector contrast; otherwise the strict coverage-error sign equals the gap sign times the squared-correlation difference. Realize both sides inside legal primitive proximal panels, including an open asymmetric family with strict undercoverage. Construct a corrected estimator using an early selector, a log-squared mixing gap, late bridge estimation, post residual averaging, and Bartlett HAC bandwidth N^(1/5); prove uniform selector-conditional studentized normality on the declared positive-variance class. Generic time splitting is supporting machinery, not novelty. Consumer: redesign the Shi et al. 2026 West-German proximal-SC role analysis as a predeclared two-candidate robustness analysis before retaining its negative GDP conclusion. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Independent derivation gives the binary selected-Gaussian coverage formula, exact nominal symmetric coverage at a zero selector gap, and all-gap validity iff the two standardized ATT statistics have equal squared correlations with the selector contrast. Exact Gaussian polynomial calculations reproduce both primitive covariance tables; the asymmetric legal proximal model yields 0.8858209104904335 coverage for a nominal 90 percent interval at standardized gap minus one, while the symmetric model has nonzero selected mean but exact two-sided coverage. A primitive local-array chart makes strict miscoverage open, and big-block Lyapunov plus Bartlett bounds vanish at the declared block and bandwidth rates. UNRESOLVED BOTTLENECK: Assemble the joint uniform Gaussian/HAC mapping lemma through singular joint covariances whose selector contrast and ATT marginals retain the stated positive variance margins. EARLY KILL TEST: Reproduce both exact covariance tables, exact tie coverage, and the 0.8858209105 asymmetric integral; pivot if the uniform mapping requires another model restriction or exact prior art contains the same proximal-role frontier. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/panel_proxysplit_selection_inference.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The corrected uniform result holds only after imposing common finite-row oracle-variance and horizon bounds, and the note supplies no observable procedure for verifying those oracle bounds in the intended application."
  - "The West-German redesign is not executed and the actual rectangular simplex-constrained rule is outside the theorem, leaving the practical significance supported only by a narrow two-role square-bridge construction and its synthetic witnesses."
  - "The note is mathematically repairable, but another D0 return would only repair correctness and disclosure; it would not cure the round-2 field-tier judgment."
reusable_artifacts:
  - discovery/core.json
  - discovery/solve_prop_primitive_realizations.tex
  - discovery/solve_thm_maximal_uniform_singular_mapping_failure.tex
  - discovery/solve_thm_uniform_singular_mapping_fails.tex
  - discovery/solve_lem_conventional_hac_consistency.tex
seeds_burned: []
proof_attempt_summary: |
  Discovery derived the selected-Gaussian coverage algebra, exact tie protection,
  an asymmetric primitive Gaussian undercoverage witness, and a maximal broad-class
  uniform-failure construction. The proposed positive uniform correction survived
  only on a class with oracle finite-row stabilization, while the six-coordinate
  joint CLT and exact Shi-class transfer remained undischarged. Reaching field tier
  would require observable stabilization theory or a genuine rectangular
  West-German application, not another bounded correctness pass.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 40247511
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 40247511
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# panel_proxysplit_selection_inference / v1 — Downgraded

**Topic.** Wald-symmetry frontier for outcome-selected proximal synthetic-control roles. Fix two predeclared square donor/proxy partitions in a stationary geometrically beta-mixing panel with fixed moment, bridge-rank, positive ATT influence-variance, and nondegenerate ridge-loss-contrast margins. The treated unit has post outcome Y(0)+Delta and target tau=E Delta; every partition is a valid proximal bridge. Select between the roles using the same pre-period lambda=1 ridge loss and estimate the conventional proximal ATT. Under every bounded root-T selector gap, derive its selected-Gaussian limit and the exact symmetric-Wald coverage functional. Prove: exact selector ties protect every symmetric Wald level; coverage is nominal for every local gap iff the two standardized ATT statistics have equal squared correlations with the selector contrast; otherwise the strict coverage-error sign equals the gap sign times the squared-correlation difference. Realize both sides inside legal primitive proximal panels, including an open asymmetric family with strict undercoverage. Construct a corrected estimator using an early selector, a log-squared mixing gap, late bridge estimation, post residual averaging, and Bartlett HAC bandwidth N^(1/5); prove uniform selector-conditional studentized normality on the declared positive-variance class. Generic time splitting is supporting machinery, not novelty. Consumer: redesign the Shi et al. 2026 West-German proximal-SC role analysis as a predeclared two-candidate robustness analysis before retaining its negative GDP conclusion. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Independent derivation gives the binary selected-Gaussian coverage formula, exact nominal symmetric coverage at a zero selector gap, and all-gap validity iff the two standardized ATT statistics have equal squared correlations with the selector contrast. Exact Gaussian polynomial calculations reproduce both primitive covariance tables; the asymmetric legal proximal model yields 0.8858209104904335 coverage for a nominal 90 percent interval at standardized gap minus one, while the symmetric model has nonzero selected mean but exact two-sided coverage. A primitive local-array chart makes strict miscoverage open, and big-block Lyapunov plus Bartlett bounds vanish at the declared block and bandwidth rates. UNRESOLVED BOTTLENECK: Assemble the joint uniform Gaussian/HAC mapping lemma through singular joint covariances whose selector contrast and ATT marginals retain the stated positive variance margins. EARLY KILL TEST: Reproduce both exact covariance tables, exact tie coverage, and the 0.8858209105 asymmetric integral; pivot if the uniform mapping requires another model restriction or exact prior art contains the same proximal-role frontier. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/panel_proxysplit_selection_inference.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** D0.5.G: meets_floor=false, tier=incremental, paper_score_ceiling=6.4<7.4, salvageable=false; the corrected uniform result requires oracle stabilization and the advertised West-German rectangular rule remains outside the theorem.

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

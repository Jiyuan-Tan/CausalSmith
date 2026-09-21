---
qid: pid_selectionminority_benefit_breakdown
spec: v1
topic: "Disjunctive threshold-cut sensitivity analysis for ordinal survivor-complier benefit under joint relaxations of treatment and selection monotonicity. With randomized binary assignment Z, binary received treatment D, exclusion and consistency, finite-support X, and finite ordinal Y observed only when S=1, allow all four compliance types. Bound aggregate defier mass by delta_D and, among compliers, bound the covariate-aggregated minority of the two opposing selection-response types by delta_S. Target the sharp set of P(Y(1)>Y(0) | D(0)=0,D(1)=1,S(0)=S(1)=1). PROVED SUBFIELD SCOPE: Compatible full laws project exactly onto a finite union of orientation-specific rational threshold-cut polytopes, and every complete reduced point lifts to a compatible full response law. Each fixed orientation branch has O(|X|K) extended size; the full union may contain up to 2^|X| branches, so no branch-free scalable positive-budget algorithm is claimed. Whenever the positive-denominator target exists, its sharp set is an attained interval with bounded-support endpoint laws. Observable orientation screening yields exact pointwise endpoint computation by at most 2^(r_amb+1) rational linear programs for r_amb ambiguous cells. For rational observed masses, exhaustive enumeration of all orientations and full-rank active bases gives a finite exact semialgebraic stratification, including singular and lower-dimensional strata, with separate model-infeasible, model-feasible/target-empty, and target-nonempty labels and rational endpoint formulas only on target-nonempty strata. The stratification also supports pointwise-relative conclusion-boundary labels and, for rational q, radial direction, and threshold, exact feasibility-entry, target-entry, and critical-budget reports by finite univariate root isolation. A simultaneous finite-sample outer confidence surface follows by projection of a multinomial primitive region. ACCEPTED-BOUNDARY POSITIONING: At delta_D=delta_S=0, the construction recovers the branch-free no-defier, covariate-wise one-sided-selection partial-transport projection, ordinal cuts, full-law lifting, sharp endpoints, and sparse O(|X|K) threshold-flow computation already proved in accepted-bank pid_slate_benefit_partialtransport_v1. The present contribution is the positive-budget disjunctive extension with unknown diagonal residuals and defiers, possible coexistence of opposing selection responses within cells, and aggregate-budget coupling of survivor mass. OPEN QUESTION, NOT A BANKED RESULT OR PRACTICAL DELIVERABLE: A degeneracy-safe output-sensitive symbolic endpoint-chart enumerator remains unproved. The available all-bases construction proves finite exact existence but may inspect exponentially many infeasible, singular, duplicate, or nonoptimal bases that emit no chart. No complexity bound charged only to emitted charts and certificates, no rejected-basis audit, and no scalable component-discovery guarantee is claimed. The earlier proposed early-kill test for that practical enumerator is undischarged and remains part of the open question, not evidence for a completed algorithm. The Job Corps and Oregon encouragement designs provide variable-level motivation only; no empirical reanalysis or transfer of published numerical bounds is claimed."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "tier_genuinely_below"
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "It does not prove the output-sensitive chart enumerator, so the framing that whole-budget charts are available is accurate only in the impractical all-bases existence sense, not as a scalable delivered procedure."
  - "The claimed Job Corps and Oregon relevance is unsupported by an implemented chart, empirical reanalysis, or even a fully worked full-law example, while the finite-sample contribution is only a conservative Hoeffding-box outer projection with no evidence on informativeness."
reusable_artifacts:
  - discovery/core.json
  - discovery/solve_thm_projection_lifting.tex
  - discovery/solve_thm_attained_connected_endpoints.tex
  - discovery/solve_thm_finite_rational_charts.tex
  - discovery/solve_prop_breakdown_frontier.tex
  - discovery/solve_prop_standard_reductions.tex
  - discovery/solve_lem_finite_frontier_compatible_sign_refinement.tex
seeds_burned:
  - index: 0
    one_liner: "seed:joint-sharp-surface"
    reason: "The sole selected angle was mathematically sound after repair but could not clear the field novelty floor without a new scalable computation, applied analysis, or stronger inference contribution."
proof_attempt_summary: |
  The D stages derived and adversarially rechecked the sharp finite-union projection/lifting result,
  attained connected endpoints, bounded-support witnesses, exact exhaustive semialgebraic charts,
  and radial critical-budget reports. The original field-level promise collapsed because the
  degeneracy-safe output-sensitive chart enumerator remained open; the surviving all-bases method
  may perform exponential rejected or duplicate work, and no empirical application or informative
  finite-sample assessment was delivered. After localized statement and positioning repairs, both
  final referees passed the subfield package with empty findings.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 24094362
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 24094362
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# pid_selectionminority_benefit_breakdown / v1 — Downgraded

**Topic.** Disjunctive threshold-cut sensitivity analysis for ordinal survivor-complier benefit under joint relaxations of treatment and selection monotonicity. With randomized binary assignment Z, binary received treatment D, exclusion and consistency, finite-support X, and finite ordinal Y observed only when S=1, allow all four compliance types. Bound aggregate defier mass by delta_D and, among compliers, bound the covariate-aggregated minority of the two opposing selection-response types by delta_S. Target the sharp set of P(Y(1)>Y(0) | D(0)=0,D(1)=1,S(0)=S(1)=1). PROVED SUBFIELD SCOPE: Compatible full laws project exactly onto a finite union of orientation-specific rational threshold-cut polytopes, and every complete reduced point lifts to a compatible full response law. Each fixed orientation branch has O(|X|K) extended size; the full union may contain up to 2^|X| branches, so no branch-free scalable positive-budget algorithm is claimed. Whenever the positive-denominator target exists, its sharp set is an attained interval with bounded-support endpoint laws. Observable orientation screening yields exact pointwise endpoint computation by at most 2^(r_amb+1) rational linear programs for r_amb ambiguous cells. For rational observed masses, exhaustive enumeration of all orientations and full-rank active bases gives a finite exact semialgebraic stratification, including singular and lower-dimensional strata, with separate model-infeasible, model-feasible/target-empty, and target-nonempty labels and rational endpoint formulas only on target-nonempty strata. The stratification also supports pointwise-relative conclusion-boundary labels and, for rational q, radial direction, and threshold, exact feasibility-entry, target-entry, and critical-budget reports by finite univariate root isolation. A simultaneous finite-sample outer confidence surface follows by projection of a multinomial primitive region. ACCEPTED-BOUNDARY POSITIONING: At delta_D=delta_S=0, the construction recovers the branch-free no-defier, covariate-wise one-sided-selection partial-transport projection, ordinal cuts, full-law lifting, sharp endpoints, and sparse O(|X|K) threshold-flow computation already proved in accepted-bank pid_slate_benefit_partialtransport_v1. The present contribution is the positive-budget disjunctive extension with unknown diagonal residuals and defiers, possible coexistence of opposing selection responses within cells, and aggregate-budget coupling of survivor mass. OPEN QUESTION, NOT A BANKED RESULT OR PRACTICAL DELIVERABLE: A degeneracy-safe output-sensitive symbolic endpoint-chart enumerator remains unproved. The available all-bases construction proves finite exact existence but may inspect exponentially many infeasible, singular, duplicate, or nonoptimal bases that emit no chart. No complexity bound charged only to emitted charts and certificates, no rejected-basis audit, and no scalable component-discovery guarantee is claimed. The earlier proposed early-kill test for that practical enumerator is undischarged and remains part of the open question, not evidence for a completed algorithm. The Job Corps and Oregon encouragement designs provide variable-level motivation only; no empirical reanalysis or transfer of published numerical bounds is claimed.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G: tier=subfield below floor=field; paper_score_ceiling 7 < 7.4, with the output-sensitive enumerator still open and no bounded same-scope field salvage.

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

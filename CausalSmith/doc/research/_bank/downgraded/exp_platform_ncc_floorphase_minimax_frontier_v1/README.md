---
qid: exp_platform_ncc_floorphase_minimax_frontier
spec: v1
topic: "Revive parent exp_platform_ncc_drift_minimax_frontier with a phase-correct all-kernel comparison rather than its refuted all-positive-floor claim. In the unchanged bounded finite-population adaptive platform model, prove that the optimized clipped predictable-AIPW radius R* and unrestricted uniformly honest variable-length minimax expected length L* are uniformly comparable iff the common available-arm floor p_floor exceeds alpha. For p_floor>alpha, establish M(p_floor-alpha)s <= L* <= 2R* <= [8 sqrt((1-p_floor)/(alpha p_floor))/(p_floor-alpha)]L*, s^2=sum_{b in W}q_b^2/n_b, under arbitrary outcome-adaptive propensities. For p_floor<=alpha, prove no finite uniform comparison and solve the one-window-unit boundary exactly. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A product-uniform prior on focal potential outcomes with all controls zero stays in every TV budget pathwise. Conditional on the actual adaptive record, unseen focal coordinates remain independent uniforms. A weighted-uniform density lemma and missing squared-weight mass Q yield E(Qc)>=(p_floor-alpha)s^2 and hence L*>=M(p_floor-alpha)s. Concurrent weights give the displayed upper constant. The continuous one-unit experiment has L*=2M[p_floor-alpha]_+ and R*=2M above the boundary, proving sharp 1/(p_floor-alpha) blow-up. In the nonadaptive one-unit three-block family, L*=(1-alpha)D+(2M-D)[p_floor-alpha]_+, D=min(Gamma,2M), so strict all-kernel NCC gain holds iff Gamma<2M. UNRESOLVED BOTTLENECK: Independently audit the posterior factorization, density lemma, and inherited radius constants; obtain an intrinsic strict-NCC-gain criterion for general continuous outcome-adaptive designs or state its impossibility boundary without substituting an AIPW KKT result. EARLY KILL TEST: Reconstruct the one-unit continuum proof, then condition the product prior through an outcome-adaptive two-unit assignment tree and verify that no missing focal coordinate enters the record likelihood; any failure, or any compatible design violating the Q coverage-budget inequality, kills the positive theorem. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_platform_ncc_floorphase_minimax_frontier.md"
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "tier_genuinely_below"
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The central theorem proves an exact positivity-versus-miscoverage phase boundary for uniform comparability, but it does not determine the general minimax length or the optimal comparison constant; only the boundary-order blow-up is matched."
  - "The exact strict nonconcurrent-control gain characterization is confined to the three-block one-window-unit experiment, while the general continuous outcome-adaptive criterion remains open, and the four-scalar impossibility theorem does not replace that characterization."
  - "The projected-AIPW upper bound is driven by a conservative Chebyshev envelope whose constants are explicitly not claimed optimal, limiting the strength of the practical competitiveness conclusion away from the boundary."
  - "The package therefore supports a genuine field-level theoretical contribution, but its stylized fixed-population scope, absence of a general NCC-gain characterization, and lack of a substantive multiunit application or computation constrain its leading-journal score."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_tex/solve_thm_floor_phase_frontier.tex
  - discovery/solve_thm_floor_phase_frontier.json
seeds_burned: []
proof_attempt_summary: |
  D0 discharged the full graph, including the exact p_floor = alpha all-kernel comparability
  boundary, sharp boundary-order blow-up, the exact one-unit Gamma = 2M NCC elbow, and a
  no-four-scalar strict-NCC criterion theorem. Both specialist reviews passed, but D0.5 capped the
  package at 7.1 because the general minimax-length formula, optimal comparison constant, intrinsic
  adaptive-design NCC criterion, and a substantive multiunit application remain unavailable.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 13615569
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 13615569
  total_tokens_consumed: null
banked_on: "2026-09-10"
---

# exp_platform_ncc_floorphase_minimax_frontier / v1 — Downgraded

**Topic.** Revive parent exp_platform_ncc_drift_minimax_frontier with a phase-correct all-kernel comparison rather than its refuted all-positive-floor claim. In the unchanged bounded finite-population adaptive platform model, prove that the optimized clipped predictable-AIPW radius R* and unrestricted uniformly honest variable-length minimax expected length L* are uniformly comparable iff the common available-arm floor p_floor exceeds alpha. For p_floor>alpha, establish M(p_floor-alpha)s <= L* <= 2R* <= [8 sqrt((1-p_floor)/(alpha p_floor))/(p_floor-alpha)]L*, s^2=sum_{b in W}q_b^2/n_b, under arbitrary outcome-adaptive propensities. For p_floor<=alpha, prove no finite uniform comparison and solve the one-window-unit boundary exactly. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A product-uniform prior on focal potential outcomes with all controls zero stays in every TV budget pathwise. Conditional on the actual adaptive record, unseen focal coordinates remain independent uniforms. A weighted-uniform density lemma and missing squared-weight mass Q yield E(Qc)>=(p_floor-alpha)s^2 and hence L*>=M(p_floor-alpha)s. Concurrent weights give the displayed upper constant. The continuous one-unit experiment has L*=2M[p_floor-alpha]_+ and R*=2M above the boundary, proving sharp 1/(p_floor-alpha) blow-up. In the nonadaptive one-unit three-block family, L*=(1-alpha)D+(2M-D)[p_floor-alpha]_+, D=min(Gamma,2M), so strict all-kernel NCC gain holds iff Gamma<2M. UNRESOLVED BOTTLENECK: Independently audit the posterior factorization, density lemma, and inherited radius constants; obtain an intrinsic strict-NCC-gain criterion for general continuous outcome-adaptive designs or state its impossibility boundary without substituting an AIPW KKT result. EARLY KILL TEST: Reconstruct the one-unit continuum proof, then condition the product prior through an outcome-adaptive two-unit assignment tree and verify that no missing focal coordinate enters the record likelihood; any failure, or any compatible design violating the Q coverage-budget inequality, kills the positive theorem. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_platform_ncc_floorphase_minimax_frontier.md

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G cold referee: delivered tier=subfield below novelty floor=field; projected paper_score_ceiling 7.1 < 7.2, and not salvageable within the same topic, assumptions, and scope.

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

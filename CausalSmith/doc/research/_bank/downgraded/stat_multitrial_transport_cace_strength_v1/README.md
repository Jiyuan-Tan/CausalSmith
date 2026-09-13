---
qid: stat_multitrial_transport_cace_strength
spec: v1
topic: "Collection-overlap weak-identification frontier for multi-trial transported complier effects. Observe K>=2 independent randomized encouragement trials over a fixed finite X, with known propensities, exclusion, monotonicity, bounded outcomes, transportable trial-cell ITT outcome and receipt contrasts, and target support covered by the union of source supports although no single source need cover it. For r_theta=Y-theta D define q_sx(theta)=Var(r_theta|s,x,Z=1)/e_s(x)+Var(r_theta|s,x,Z=0)/(1-e_s(x)); minimize sum a_sx^2 q_sx(theta)/[n_s p_s(x)] subject to source-support constraints and sum_s a_sx=p_T(x), calling the optimum V_coll(P,theta), and set T_coll=mu_T^2/V_coll(P,theta_T). Prove that over laws with T_coll>=u the all-procedure minimax worst expected length of uniformly honest 1-alpha confidence intervals is Theta_alpha(min{1,u^(-1/2)}), uniformly through weak compliance and collection-only overlap. Construct a fully data-computable profiled multi-source Anderson-Rubin inversion attaining the bound, and prove a matching continuum lower bound that makes the collection quadratic program necessary. Recover the accepted single-source theorem when K=1. Use the two-cell split-support Rademacher-noise witness and Rudolph--van der Laan's published five-site Moving to Opportunity transported-CACE analysis as the principal consumer, with Dahabreh et al.'s collection-overlap meta-analysis as workflow grounding. Regular Wald/GMM asymptotics and oracle weights do not satisfy the kernel."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "The proposed V_coll program is uniformly honest and worst-case rate-sharp, but it is not the unrestricted pointwise multi-source information bound; no boundary-safe vector-profile attaining procedure or worked consumer reanalysis was delivered."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "For multiple trials, however, the procedure is deliberately tied to the scalar residual program even though the maintained model permits the strictly more informative vector program, so the result is a worst-case frontier rather than a pointwise optimal multi-source procedure."
  - "The claimed practical importance is supported only by stylized constructions: the cited Moving to Opportunity analysis is presented as a consumer without a worked reanalysis or quantitative demonstration of how collection allocation changes inference."
  - "The TL;DR's statement that the boundary factor vanishes exactly when every identified outcome ITT is zero overstates the proved implication: the theorem shows that the maximal-variance boundary forces all such ITTs to zero, not that zero ITTs imply that boundary."
  - "D0.5.G projected paper-score gate: paper_score_ceiling 7.2 < 7.4, so the graded tier 'field' is capped at 'subfield'."
reusable_artifacts:
  - "discovery/core.json — final graph containing the scalar and unrestricted vector allocation programs and all proved statements."
  - "discovery/writeup.tex — complete derivation note, including the boundary-factor minimax lower family."
  - "discovery/solve_tex/solve_thm_continuum_lower_bound.tex — Bernoulli least-favorable construction, KL calculation, vector-information comparison, and covariance-singularity witness."
  - "discovery/solve_tex/solve_prop_single_source_sanity_check.tex — exact K=1 reduction and support-safe variance formula."
  - "reviews/stage_0.5.G_attempt2.json — final subfield-tier novelty and impact assessment."
seeds_burned:
  - index: 0
    one_liner: "collection-information minimax confidence-length frontier"
    reason: "The only angle was maximized and proved, but D0.5.G capped it below field after the scalar-versus-vector information audit."
proof_attempt_summary: |
  The run proved a data-total scalar-profiled Anderson--Rubin upper bound and an all-procedure
  collection-only lower family, including an explicit boundary factor and the exact degenerate edge.
  The original pointwise-information claim collapsed because separate outcome and receipt transport
  permits a strictly better vector-GMM allocation; the repaired paper records that vector program but
  does not construct a boundary-safe uniformly attaining vector-profile procedure or a worked consumer
  reanalysis, leaving the package below the field floor.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 28274165
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 28274165
  total_tokens_consumed: null
banked_on: "2026-09-12"
---

# stat_multitrial_transport_cace_strength / v1 — Downgraded

**Topic.** Collection-overlap weak-identification frontier for multi-trial transported complier effects. Observe K>=2 independent randomized encouragement trials over a fixed finite X, with known propensities, exclusion, monotonicity, bounded outcomes, transportable trial-cell ITT outcome and receipt contrasts, and target support covered by the union of source supports although no single source need cover it. For r_theta=Y-theta D define q_sx(theta)=Var(r_theta|s,x,Z=1)/e_s(x)+Var(r_theta|s,x,Z=0)/(1-e_s(x)); minimize sum a_sx^2 q_sx(theta)/[n_s p_s(x)] subject to source-support constraints and sum_s a_sx=p_T(x), calling the optimum V_coll(P,theta), and set T_coll=mu_T^2/V_coll(P,theta_T). Prove that over laws with T_coll>=u the all-procedure minimax worst expected length of uniformly honest 1-alpha confidence intervals is Theta_alpha(min{1,u^(-1/2)}), uniformly through weak compliance and collection-only overlap. Construct a fully data-computable profiled multi-source Anderson-Rubin inversion attaining the bound, and prove a matching continuum lower bound that makes the collection quadratic program necessary. Recover the accepted single-source theorem when K=1. Use the two-cell split-support Rademacher-noise witness and Rudolph--van der Laan's published five-site Moving to Opportunity transported-CACE analysis as the principal consumer, with Dahabreh et al.'s collection-overlap meta-analysis as workflow grounding. Regular Wald/GMM asymptotics and oracle weights do not satisfy the kernel.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G tier=subfield < floor=field: the result is a worst-case scalar-profile frontier rather than a pointwise optimal multi-source procedure, and the practical consumer remains stylized.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

The most promising re-raise is to retain the proved scalar worst-case frontier and add a total,
uniformly valid regularized vector-profile inversion under the original covariance-boundary class.
The final D0.5 wording correction should also state only the proved direction: maximal residual
variance forces zero transported outcome ITTs.

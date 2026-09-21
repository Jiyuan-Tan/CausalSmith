---
qid: stat_policy_disagreement_annotation
spec: v1
topic: "Nuisance-uniform minimax outcome annotation for an overlapping finite causal-policy menu. In a finite-stratum binary-treatment model with known propensities, a frozen rank-full menu of at least three overlapping policies, budgeted outcome-acquisition rates bounded away from zero, and unrestricted eta-positive probabilities on a fixed finite outcome support, derive the local Gaussian policy-contrast experiment uniformly over the full Qh+Nu treatment-effect fiber and every outcome-shape nuisance tangent. Characterize the minimax welfare-regret value V* over deterministic limiting annotation designs; give certified finite-grid upper and lower computation; and construct a vanishing-pilot, stabilized design selector, joint AIPW contrast estimator, and Gaussian minimax rule attaining V*. For the stated rational three-policy witness with H=[-1,1]^2, prove that the unique minimizer of maximum pairwise contrast variance has regret above 0.1965 while a feasible design has regret below 0.18453, and extend the strict separation to an explicit open parameter neighborhood. Consumer: prospective independent validation of the eight azithromycin rules in the ABCD trial, where targeted follow-up replaces uniform or exogenous outcome collection. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A saturated mean/shape decomposition gives orthogonal Fisher information and T_r' I_r T_r=Sigma(r)^(-1); bounded likelihood-ratio arguments support the full-nuisance lower-risk transfer. A projected nested-cell selector handles nonunique optima, and exact conditional AIPW covariance plus rectangle-risk transfer support attainment. Outward-rounded Arb certificates verify L(r_alt)<0.18453, L(r_G)>0.1965 and separation on a radius-10^-6 neighborhood. Tests covered shape nuisances, pilot information, discontinuous selectors, boundary minima, zero-regret sets, variance degeneracy, and current policy-design collisions. UNRESOLVED BOTTLENECK: Complete a measurable implementation theorem coupling the certified nested-cell design sieve and Gaussian observation-grid selector, with locally uniform risk attainment and deterministic optimal-rate convergence at every nonunique optimum. EARLY KILL TEST: Verify nested-cell stabilization at separated tied minima and a dyadic-boundary minimum under uniform approximation errors; failure to stabilize every fixed tree prefix stops universal attainment. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_policy_disagreement_annotation.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: null
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The delivered minimax equality is confined to a local tied-baseline experiment and to procedures whose annotation rates converge to deterministic limits; it does not cover random limiting designs, fully sequential acquisition, continuous outcomes, or global regret."
  - "The three-policy separation is against the note's internally constructed maximum-pairwise-variance probe, so it establishes a real geometric distinction but does not refute a standard published design criterion."
  - "The claimed ABCD relevance remains prospective: no eight-rule design, attainable regret gain, or sensitivity calculation for that application is delivered."
  - "The decisive numerical inequalities are reported as products of outward-rounded computations without an accompanying certificate artifact or executable reproduction record, limiting independent verification and the projected journal score."
reusable_artifacts:
  - "discovery/core.json — fully discharged theorem graph, including the exact local minimax characterization and verified cited leaves."
  - "discovery/solve_thm_certified_computation.json — finite-grid Gaussian-game certification construction."
  - "discovery/solve_thm_coupled_measurable_attainment.json — nested-cell measurable selector and locally uniform attainment argument."
  - "discovery/solve_thm_open_neighborhood_separation.json — explicit three-policy witness and open-neighborhood separation proof."
  - "discovery/writeup.tex — synchronized derivation note with binary-outcome scope and minimal diverging pilot condition."
seeds_burned: []
proof_attempt_summary: |
  The run completed and revalidated a no-open-statement D0 graph for the local Gaussian policy-contrast experiment, exact deterministic-limit minimax value, certified finite-grid computation, coupled measurable selector/AIPW attainment, and the explicit three-policy separation; it also weakened the pilot requirement to arbitrary divergence with vanishing share and extended the general theory to binary outcomes. D0.5's math panel passed after source-of-record correction and attestation of all four cited leaves. The result was downgraded because the field-tier novelty case, not the mathematics, failed: reaching field would require a materially broader experiment, separation from a published practical design criterion, or a substantive eight-rule ABCD application with executable certificates.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 49132435
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 49132435
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# stat_policy_disagreement_annotation / v1 — Downgraded

**Topic.** Nuisance-uniform minimax outcome annotation for an overlapping finite causal-policy menu. In a finite-stratum binary-treatment model with known propensities, a frozen rank-full menu of at least three overlapping policies, budgeted outcome-acquisition rates bounded away from zero, and unrestricted eta-positive probabilities on a fixed finite outcome support, derive the local Gaussian policy-contrast experiment uniformly over the full Qh+Nu treatment-effect fiber and every outcome-shape nuisance tangent. Characterize the minimax welfare-regret value V* over deterministic limiting annotation designs; give certified finite-grid upper and lower computation; and construct a vanishing-pilot, stabilized design selector, joint AIPW contrast estimator, and Gaussian minimax rule attaining V*. For the stated rational three-policy witness with H=[-1,1]^2, prove that the unique minimizer of maximum pairwise contrast variance has regret above 0.1965 while a feasible design has regret below 0.18453, and extend the strict separation to an explicit open parameter neighborhood. Consumer: prospective independent validation of the eight azithromycin rules in the ABCD trial, where targeted follow-up replaces uniform or exogenous outcome collection. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A saturated mean/shape decomposition gives orthogonal Fisher information and T_r' I_r T_r=Sigma(r)^(-1); bounded likelihood-ratio arguments support the full-nuisance lower-risk transfer. A projected nested-cell selector handles nonunique optima, and exact conditional AIPW covariance plus rectangle-risk transfer support attainment. Outward-rounded Arb certificates verify L(r_alt)<0.18453, L(r_G)>0.1965 and separation on a radius-10^-6 neighborhood. Tests covered shape nuisances, pilot information, discontinuous selectors, boundary minima, zero-regret sets, variance degeneracy, and current policy-design collisions. UNRESOLVED BOTTLENECK: Complete a measurable implementation theorem coupling the certified nested-cell design sieve and Gaussian observation-grid selector, with locally uniform risk attainment and deterministic optimal-rate convergence at every nonunique optimum. EARLY KILL TEST: Verify nested-cell stabilization at separated tied minima and a dyadic-boundary minimum under uniform approximation errors; failure to stabilize every fixed tree prefix stops universal attainment. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_policy_disagreement_annotation.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G tier=subfield < floor=field with paper_score_ceiling 7.2 < 7.4 and NOT salvageable in scope; review_math passes after all four cited leaves were verified.

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

---
qid: panel_mnar_eventtime_uniform_band
spec: v1
topic: "Adoption-aligned uniform event-curve inference for staggered MNAR low-rank panels. Fix the eligible-cohort unit-share event estimand and use the exact Choi--Yuan Proposition A.4 block influence coefficients. Derive a uniform growing-dimensional influence representation, the full staircase-overlap covariance including shared donor-cell terms, a consistent heteroskedastic plug-in covariance, and honest studentized Gaussian-multiplier bands. Determine the weakest primitive uniform remainder envelope built from the published Choi--Yuan block ratios and prove a legal counterarray for every strictly weaker envelope claimed sharp. Use the rank-one two-horizon witness whose shared pre-treatment cell has coefficient 1/4 in each expansion and covariance product 1/16; apply the result to the Ben-Michael--Feller RTC-law event curve. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Cohort aggregation of Proposition A.4 yields the standardized array D_n^-1(tau_hat-tau)=-sum_q a_.q e_q+rho_n with unit marginal variances and maximum coefficient L_n(K). Standard high-dimensional approximation applies under the stated leverage condition. The presolve derived a sufficient primitive envelope Delta_CY,n(K)sqrt(log(K vee 2))->0 by combining the joint remainder bound with Gaussian anti-concentration. In the balanced rank-one instance, each horizon has variance 3/4; four shared pre-treatment cells contribute covariance 1/4, hence correlation 1/3. Focused checks found only scalar or fixed-functional inference, not growing event-curve coverage. UNRESOLVED BOTTLENECK: Construct Choi--Yuan-legal triangular arrays whose standardized nonlinear remainder attains the Delta_CY scale strongly enough to prove that every strictly weaker simultaneous-band envelope fails. EARLY KILL TEST: Compute the exact second-order remainder in a balanced strong-factor rank-one panel with equally split cohorts and growing K; pivot the sharp-envelope claim if it is uniformly little-o of Delta_CY for every legal split, because the required converse family would then lack an attainable witness."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The advertised honest feasible growing-event-curve band and sharp attainable envelope/counterarray remain undelivered; only a conditional finite-error Gaussian transfer is established."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The note does not prove honest feasible growing-event-curve inference: its coverage theorem assumes vanishing nonlinear-remainder and feasible-score failure probabilities, while neither probability control follows from the stated event-transfer class."
  - "Covariance consistency is likewise not established, because the theorem stops at a deterministic implication from an unproved score-discrepancy rate."
  - "The sharp primitive remainder envelope, its counterarray, and the feasible-score stability needed for actual bands are all deferred to oeq:attainable-remainder-frontier."
reusable_artifacts:
  - "discovery/core.json — source-attested theorem graph with the conditional transfer, log^5 CCKK approximation, class comparison, and open frontier node."
  - "discovery/writeup.tex — derivations for eventwise influence aggregation, staircase covariance, score-stability decomposition, and the balanced rank-one witness."
  - "discovery/solve_thm_uniform_influence.json — checked proof packet for the exact aggregation and Choi--Yuan remainder-event implication."
  - "discovery/solve_thm_heteroskedastic_covariance.json — checked proof packet for oracle variance concentration and deterministic plug-in contamination/stability."
seeds_burned: []
proof_attempt_summary: |
  The run derived exact eventwise aggregation, overlap-aware covariance bookkeeping, a singular-covariance-safe log^5 Gaussian approximation, and a generic finite-error multiplier transfer, with all five cited inputs verified from official source text. The promised feasible field-tier band collapsed because the frozen event-transfer class supplies neither a vanishing simultaneous block-remainder failure probability nor stochastic feasible-score stability. A future re-raise must prove those rates—likely through signed second-order KKT and counterarray analysis—or openly add primitive assumptions; editorial wording and panel-sanity repairs alone cannot lift the result.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 73461060
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-07"
---

# panel_mnar_eventtime_uniform_band / v1 — Downgraded

**Topic.** Adoption-aligned uniform event-curve inference for staggered MNAR low-rank panels. Fix the eligible-cohort unit-share event estimand and use the exact Choi--Yuan Proposition A.4 block influence coefficients. Derive a uniform growing-dimensional influence representation, the full staircase-overlap covariance including shared donor-cell terms, a consistent heteroskedastic plug-in covariance, and honest studentized Gaussian-multiplier bands. Determine the weakest primitive uniform remainder envelope built from the published Choi--Yuan block ratios and prove a legal counterarray for every strictly weaker envelope claimed sharp. Use the rank-one two-horizon witness whose shared pre-treatment cell has coefficient 1/4 in each expansion and covariance product 1/16; apply the result to the Ben-Michael--Feller RTC-law event curve. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Cohort aggregation of Proposition A.4 yields the standardized array D_n^-1(tau_hat-tau)=-sum_q a_.q e_q+rho_n with unit marginal variances and maximum coefficient L_n(K). Standard high-dimensional approximation applies under the stated leverage condition. The presolve derived a sufficient primitive envelope Delta_CY,n(K)sqrt(log(K vee 2))->0 by combining the joint remainder bound with Gaussian anti-concentration. In the balanced rank-one instance, each horizon has variance 3/4; four shared pre-treatment cells contribute covariance 1/4, hence correlation 1/3. Focused checks found only scalar or fixed-functional inference, not growing event-curve coverage. UNRESOLVED BOTTLENECK: Construct Choi--Yuan-legal triangular arrays whose standardized nonlinear remainder attains the Delta_CY scale strongly enough to prove that every strictly weaker simultaneous-band envelope fails. EARLY KILL TEST: Compute the exact second-order remainder in a balanced strong-factor rank-one panel with equally split cohorts and growing K; pivot the sharp-envelope claim if it is uniformly little-o of Delta_CY for every legal split, because the required converse family would then lack an attainable witness.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The headline proves a valid generic conditional transfer, but the event-transfer class does not imply the required high-probability nonlinear-remainder or feasible-score events.

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

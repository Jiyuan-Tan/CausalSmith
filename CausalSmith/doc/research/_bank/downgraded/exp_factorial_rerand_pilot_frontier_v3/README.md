---
qid: exp_factorial_rerand_pilot_frontier
spec: v3
topic: "Sharp pilot sizing for factorial rerandomization on a locally rich fixed-baseline domain. Condition on a deterministic complete baseline array known before assignment; all oracle-relevant uncertainty enters through a stable bounded conditional potential-outcome family whose global parameter set is the closure of a full-dimensional connected product of oracle and nuisance balls inside one regular identifiable chart. In a balanced two-wave 2^K factorial experiment, use complete randomization in an m-unit pilot, a pilot-measurable centered positive-support exact-alpha ellipsoidal rerandomization mixture in the main wave, and exact-inclusion pooled Horvitz-Thompson for the realized finite-population factorial vector. Relative to the matching full-n empirical raw-MSE oracle, prove the uniform second-order risk contrast A(beta)m/n^2+B(beta)/(nm)+o(m/n^2+1/(nm)), B=tr(Gamma I_eff^-1), and the global sharp envelope with unique m/sqrt(n) limit. Consumer: stable-batch replications of Menon et al.'s sequential factorial-cycle design with preregistered future baselines and continuously rich uncertainty. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The outcome-only likelihood, nuisance-efficient Gaussian boundary covariance, and exact pooled-HT contrast were derived. Every permitted single-wave HT risk is O(1/N). The global constant equals max over conv{(A,B)} of 2sqrt(AB), has a unique pilot fraction, and needs at most two active parameter values. Corrected disk information and exact rational enumeration verify acceptance 137/1000, minimum assignment probability 1/96, unequal inclusions 1/16 and 7/16, and zero HT bias. Baseline-leakage, finite-catalogue, endpoint, tie, lattice, and current-prior-art checks found no fatal defect in the final domain. UNRESOLVED BOTTLENECK: Prove uniformly that full-oracle gain minus weighted subset-oracle gain contributes A m/n^2 and empirical-oracle-centered finite HT action regret contributes B/(nm), with little-o remainder under exact ties, splitting, unequal inclusions, nuisance estimation, and arbitrary measurable actions. EARLY KILL TEST: On increasing cross-character arrays with m rounded from t sqrt(n), certify the scaled exact-HT contrast and localized action regret; any nonzero limiting lattice or unequal-inclusion correction not absorbed into A,B forces revision. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_factorial_rerand_pilot_frontier.md"
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The advertised sharp square-root pilot frontier was replaced by a conditional deterministic transfer plus three open statistical cruxes; covariance-standardization defects also leave dependent endpoint claims uncertified."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The advertised sharp square-root pilot frontier is not proved: A is unidentified, B is not transferred to exact finite risk, and the compact-window expansion and three essential boundary regimes remain open."
  - "D0.5 decision verdict: kernel_substituted at oeq:global-sharp-pilot; the promised sharp square-root pilot rule is replaced by a conditional deterministic transfer plus three open statistical cruxes."
  - "D0.5 typed verdict: FAIL round 0. Math findings: omitted-standardization-congruence at thm:oracle-deletion-loss and prop:first-order-arbitrary-action-optimality; the raw-coordinate a(beta) formula and raw Gaussian lower-tail optimization are false unless the imbalance covariance is identity-scaled."
  - "Cold-tier verdict: incremental; paper_score_ceiling 4.6 < field floor 7.4; meets_floor=false; salvageable=false; flagship_potential=false."
reusable_artifacts:
  - discovery/core.json
  - discovery/solve_thm_exact_ht_accounting.tex
  - discovery/solve_lem_deterministic_envelope_certificate.tex
  - discovery/solve_thm_oracle_deletion_loss.tex
  - discovery/solve_lem_pilot_endpoint_exclusion.tex
  - orchestrator/decision_log.jsonl
seeds_burned: []
proof_attempt_summary: |
  The D-stage derived exact pooled-HT risk accounting, a deterministic envelope certificate,
  first-order oracle-gain and arbitrary-action comparisons, and partial endpoint exclusions while
  explicitly demoting the sharp global sizing rule to an open question. D0.5 then found that the
  Gaussian gain and action arguments omitted the imbalance-covariance congruence, leaving their
  endpoint consumers uncertified. Repairing that coordinate defect would not identify A, transfer B,
  establish the compact second-order expansion, close the three remaining pilot regimes, or yield an
  unconditional pilot rule, so the independent validity gate confirmed an incremental true negative.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 54371848
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 54371848
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# exp_factorial_rerand_pilot_frontier / v3 — Downgraded

**Topic.** Sharp pilot sizing for factorial rerandomization on a locally rich fixed-baseline domain. Condition on a deterministic complete baseline array known before assignment; all oracle-relevant uncertainty enters through a stable bounded conditional potential-outcome family whose global parameter set is the closure of a full-dimensional connected product of oracle and nuisance balls inside one regular identifiable chart. In a balanced two-wave 2^K factorial experiment, use complete randomization in an m-unit pilot, a pilot-measurable centered positive-support exact-alpha ellipsoidal rerandomization mixture in the main wave, and exact-inclusion pooled Horvitz-Thompson for the realized finite-population factorial vector. Relative to the matching full-n empirical raw-MSE oracle, prove the uniform second-order risk contrast A(beta)m/n^2+B(beta)/(nm)+o(m/n^2+1/(nm)), B=tr(Gamma I_eff^-1), and the global sharp envelope with unique m/sqrt(n) limit. Consumer: stable-batch replications of Menon et al.'s sequential factorial-cycle design with preregistered future baselines and continuously rich uncertainty. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The outcome-only likelihood, nuisance-efficient Gaussian boundary covariance, and exact pooled-HT contrast were derived. Every permitted single-wave HT risk is O(1/N). The global constant equals max over conv{(A,B)} of 2sqrt(AB), has a unique pilot fraction, and needs at most two active parameter values. Corrected disk information and exact rational enumeration verify acceptance 137/1000, minimum assignment probability 1/96, unequal inclusions 1/16 and 7/16, and zero HT bias. Baseline-leakage, finite-catalogue, endpoint, tie, lattice, and current-prior-art checks found no fatal defect in the final domain. UNRESOLVED BOTTLENECK: Prove uniformly that full-oracle gain minus weighted subset-oracle gain contributes A m/n^2 and empirical-oracle-centered finite HT action regret contributes B/(nm), with little-o remainder under exact ties, splitting, unequal inclusions, nuisance estimation, and arbitrary measurable actions. EARLY KILL TEST: On increasing cross-character arrays with m rounded from t sqrt(n), certify the scaled exact-HT contrast and localized action regret; any nonzero limiting lattice or unequal-inclusion correction not absorbed into A,B forces revision. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_factorial_rerand_pilot_frontier.md

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** Cold-tier verdict: incremental; paper_score_ceiling 4.6 < field floor 7.4; meets_floor=false; salvageable=false; flagship_potential=false.

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

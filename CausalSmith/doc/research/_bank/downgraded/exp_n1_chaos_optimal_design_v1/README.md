---
qid: exp_n1_chaos_optimal_design
spec: v1
topic: "Fourth-order minimax randomization for a single fixed impulse-response path. For Y_t=sum_{l=0}^{K-1}g_l x_{t-l}+e_t, globally sign-symmetric pairwise-orthogonal binary assignment, and the joint ellipsoid ||g||^2/R_g^2+||e||^2/(T R_e^2)<=1, characterize the exact design-based minimax MSE of the unbiased moment estimator. Prove for K=2 and q=e_0 that V_{T,2}=max{R_e^2,a_T R_g^2/T}, a_T=1 for even T and 2 for odd T, with all optimizer membership conditions, explicit mirrored-edge-sign attaining laws, and matching algebraic dual/parity certificates. For fixed K,q, prove equality of finite-horizon and stationary limits and construct pairwise-orthogonal finite-state randomized Golay-block laws attaining R_e^2 max_{|z|=1}|sum_l q_l z^l|^2; report exact fourth-moment tensor certificates and comparisons for N-of-1 carryover designs. Do not claim Wald inference, fixed treatment counts, or multi-arm applicability. PRESOLVE EVIDENCE REQUIRING VERIFICATION: exact LP enumeration for T=4–13 and construction checks through T=16 support the all-horizon parity formula; mirrored independent edge signs attain it; Golay covariance checks through length 256 support the stationary spectral limit. A disturbance spike refutes uniform Wald inference, and fixed counts violate the design class. UNRESOLVED BOTTLENECK: prove the coefficient-level stationary Golay-block covariance with random-phase endpoints and the actual zero-prehistory estimator denominators, including the finite-state complexity bound. EARLY KILL TEST: exactly enumerate Golay blocks at lengths 8 and 16 for K=3,4, verify the boundary covariance/normalization identities, and reproduce the T=5 parity certificate; any failure stops the stationary theorem. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_n1_chaos_optimal_design.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "Field scope would require solving the open lag-sized fourth-moment realizability body or adding a new estimator-wide, inference, design-class, or applied program."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The note proves an exact finite-horizon minimax value and optimizer characterization only for the displayed moment estimator in the one-lag case, while its general fixed-K result is an asymptotic disturbance-floor characterization with an O(T^{-1}) bracket rather than an exact finite-horizon solution."
  - "The general finite fourth-moment realizability problem remains exponential through the orbit SDP, and the advertised lag-sized characterization is explicitly left open."
  - "The contribution is further confined to binary, pairwise-orthogonal randomization with random treatment counts, a fixed LTI path, and the chosen joint energy ellipsoid, so it does not establish estimator-wide minimaxity or inference guarantees."
reusable_artifacts:
  - "discovery/core.json — maximized theorem graph and exact exponential orbit-SDP formulation."
  - "discovery/solve_thm_lag_one_minimax.{json,tex} — exact all-horizon K=2 parity minimax proof and optimizer face."
  - "discovery/solve_thm_balanced_stationary_golay_optimum.{json,tex} — stationary Golay construction, spectral optimum, and finite-horizon rate argument."
  - "discovery/solve_lem_l8_golay_audit.{json,tex} — concrete Golay tensor/boundary audit."
  - "discovery/solve_lem_mirrored_law_membership.{json,tex} and solve_lem_t4_mirrored_audit.{json,tex} — mirrored-law membership and small-horizon certificates."
seeds_burned: []
proof_attempt_summary: |
  Discovery proved the exact K=2 even/odd minimax value and optimizer face over balanced pairwise-orthogonal laws, established sign symmetrization without loss, and derived a finite-state Golay stationary optimum with a two-sided O(T^{-1}) finite-horizon bound. The D0.5 math and decision referees accepted the mathematics, but the cold general referee capped the package at subfield because general finite-K realizability is still available only through an exponential orbit SDP and the result remains estimator-specific without inference. Reaching field scope would require solving the lag-sized fourth-moment body or beginning a materially new estimator, inference, design-class, or applied program.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 24099156
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 24099156
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# exp_n1_chaos_optimal_design / v1 — Downgraded

**Topic.** Fourth-order minimax randomization for a single fixed impulse-response path. For Y_t=sum_{l=0}^{K-1}g_l x_{t-l}+e_t, globally sign-symmetric pairwise-orthogonal binary assignment, and the joint ellipsoid ||g||^2/R_g^2+||e||^2/(T R_e^2)<=1, characterize the exact design-based minimax MSE of the unbiased moment estimator. Prove for K=2 and q=e_0 that V_{T,2}=max{R_e^2,a_T R_g^2/T}, a_T=1 for even T and 2 for odd T, with all optimizer membership conditions, explicit mirrored-edge-sign attaining laws, and matching algebraic dual/parity certificates. For fixed K,q, prove equality of finite-horizon and stationary limits and construct pairwise-orthogonal finite-state randomized Golay-block laws attaining R_e^2 max_{|z|=1}|sum_l q_l z^l|^2; report exact fourth-moment tensor certificates and comparisons for N-of-1 carryover designs. Do not claim Wald inference, fixed treatment counts, or multi-arm applicability. PRESOLVE EVIDENCE REQUIRING VERIFICATION: exact LP enumeration for T=4–13 and construction checks through T=16 support the all-horizon parity formula; mirrored independent edge signs attain it; Golay covariance checks through length 256 support the stationary spectral limit. A disturbance spike refutes uniform Wald inference, and fixed counts violate the design class. UNRESOLVED BOTTLENECK: prove the coefficient-level stationary Golay-block covariance with random-phase endpoints and the actual zero-prehistory estimator denominators, including the finite-state complexity bound. EARLY KILL TEST: exactly enumerate Golay blocks at lengths 8 and 16 for K=3,4, verify the boundary covariance/normalization identities, and reproduce the T=5 parity certificate; any failure stops the stationary theorem. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_n1_chaos_optimal_design.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** The note proves an exact finite-horizon minimax value and optimizer characterization only for the displayed moment estimator in the one-lag case, while its general fixed-K result remains an asymptotic disturbance-floor characterization; paper_score_ceiling 7 < field gate 7.4.

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

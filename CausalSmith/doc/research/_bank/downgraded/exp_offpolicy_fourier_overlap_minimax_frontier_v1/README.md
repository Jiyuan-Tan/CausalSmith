---
qid: exp_offpolicy_fourier_overlap_minimax_frontier
spec: v1
topic: "Probability-weighted Fourier exposure-incidence risk certificates for off-policy causal estimation in networks. Fix a known graph, uniformly positive source and target product-Bernoulli policies, known finite downward-closed local Fourier supports, and bounded fixed schedules observed once under the source law. Define the exact assignment-indexed linear minimax risk F and prove F equals its covariance-moment dual, with minimizing weights, a clipped incidence estimator, computable primal and genuine-prior lower certificates, an instance-adaptive rank/fiber comparison to unrestricted all-Borel minimax risk, and complexity-calibrated consistency. Prove exact all-Borel equality on the one-nonconstant additive-l1 hub family, the broader additive-hub n^{-1} frontier and Loomba–Eckles envelope separation including the local-policy n^{-1/2} elbow, and disjoint-motif recovery under its explicit unbiased-witness premise. Give the exact fully expanded finite program and a width-one obstruction showing ordinary raw-incidence bag moments do not determine the squared target moment. The dimension-free universal comparison, unconditional reverse consistency over all admissible arrays, and exact compressed bounded-treewidth algorithm remain open. Crépon and Chin–Eckles–Ugander are prospective design-audit consumers after design-specific inputs are supplied; no empirical reanalysis is claimed."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REVISE
proposal_promise_gap: "kernel_substituted"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "Unrestricted all-Borel risk remains separated from F by rank or fiber factors that may grow exponentially."
  - "The exact all-Borel equality is proved only on the additive one-hub l1 family; the envelope separation is not a generic sharpness failure on the published class."
  - "The dimension-free universal comparison, unconditional reverse consistency, and compressed bounded-treewidth exact algorithm remain open."
reusable_artifacts:
  - "discovery/core.json — settled exact F=D geometry, expanded finite program, rank/fiber certificate, additive-hub witnesses, and open-question boundaries."
  - "discovery/writeup.tex — complete subfield derivation note with hub envelope and local-policy elbow calculations."
  - "discovery/proof_archive/index.jsonl — content-addressed proof history for the distinct prior-rounding and treewidth routes."
  - "reviews/reviews.jsonl — cold tier decisions, verified citation receipts, and convergence history."
seeds_burned: []
proof_attempt_summary: |
  The run proved the exact assignment-indexed linear minimax program and covariance-moment dual, an instance-adaptive rank/fiber comparison, exact additive one-hub all-Borel equality, and sharp additive-hub envelope separation. Distinct universal-prior routes failed for complementary reasons: atom labels are revealed, ellipsoid priors lose a rank factor, fiber priors lose effective assignment count, and local/product priors miss global correlations. After a final whole-core repair and clean mathematical/citation review, the cold panel still rated the result subfield because the universal comparison and compressed treewidth algorithm remain unresolved.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 82195467
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-05"
---

# exp_offpolicy_fourier_overlap_minimax_frontier / v1 — Downgraded

**Topic.** Probability-weighted Fourier exposure-incidence risk certificates for off-policy causal estimation in networks. Fix a known graph, uniformly positive source and target product-Bernoulli policies, known finite downward-closed local Fourier supports, and bounded fixed schedules observed once under the source law. Define the exact assignment-indexed linear minimax risk F and prove F equals its covariance-moment dual, with minimizing weights, a clipped incidence estimator, computable primal and genuine-prior lower certificates, an instance-adaptive rank/fiber comparison to unrestricted all-Borel minimax risk, and complexity-calibrated consistency. Prove exact all-Borel equality on the one-nonconstant additive-l1 hub family, the broader additive-hub n^{-1} frontier and Loomba–Eckles envelope separation including the local-policy n^{-1/2} elbow, and disjoint-motif recovery under its explicit unbiased-witness premise. Give the exact fully expanded finite program and a width-one obstruction showing ordinary raw-incidence bag moments do not determine the squared target moment. The dimension-free universal comparison, unconditional reverse consistency over all admissible arrays, and exact compressed bounded-treewidth algorithm remain open. Crépon and Chin–Eckles–Ugander are prospective design-audit consumers after design-specific inputs are supplied; no empirical reanalysis is claimed.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REVISE

**Banking reason.** Unrestricted all-Borel risk remains separated from F by rank or fiber factors that may grow exponentially; no non-identical bounded same-topic repair reaches the field floor.

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

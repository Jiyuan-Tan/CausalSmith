---
qid: exp_switchback_polynomial_decay_oracle_frontier
spec: v1
topic: "Polynomial-memory oracle frontier for sequential switchback experiments. Fix B>0, C>0 and known beta>0. In the banked parent's one-unit finite-population model, potential outcomes are fixed maps of binary treatment histories into [-B,B] and obey sum_l (1+l)^(1+beta)|Delta_l Y_t|<=C. Randomized assignments may depend on observed past assignments and outcomes. For the all-treated-versus-all-control GATE, prove over all sequential policies and estimators that minimax MSE is Theta(T^(-2beta/(2beta+1))), with explicit finite-horizon constants, while C=0 has the ordinary Theta(T^-1) frontier. Audit the parent's Markov/truncated-HT upper bound. For the converse, fix the adversarial prior before assignment, derive a policy-uniform multiscale occupancy/information inequality, and combine common-null block priors with arm-specific positive-part band bumps. Do not reuse the parent's invalid cadence dichotomy and do not claim unknown-beta adaptation. Connect the oracle block scale T^(1/(2beta+1)) to operational window choice in Statsig-style and marketplace switchbacks. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolver derived |hat theta_b-tilde theta_b|<=(2eC/beta)(b+1)^(-beta) and combined it with the parent's auxiliary variance bound, giving the corrected MSE exponent. It obtained exact posterior-variance components B^2/T and B^2 L^2 E[U_L]/T^2, and constructed arm-specific band-bump likelihoods whose assignment-kernel factors cancel under adaptive policies. Strict alternation, sparse minority pulses, constant paths, zero propensities, and small beta were stress-tested; no current theorem was found to subsume the result. UNRESOLVED BOTTLENECK: Prove the single sequential multiscale occupancy/information lemma showing that every adaptive assignment kernel leaves either blockwise counterfactual variance of order L/T or an arm-specific dyadic bump with bounded information and separation L^(-beta), for L around T^(1/(2beta+1)); remove or retain any unavoidable logarithm honestly. EARLY KILL TEST: Enumerate binary paths through T<=16 and test the deterministic dyadic occupancy inequality on sparse-switch, strict-alternation, unequal-periodic, one-switch, and concatenated-cadence paths. Any legal constant-order violation, or a required logarithmic loss, forces immediate revision of the headline. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_switchback_polynomial_decay_oracle_frontier.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "Prove a policy-uniform dyadic stopping/occupancy-information inequality and valid common-measure transfer that yields at least an unconditional logarithmic minimax lower bracket for arbitrary outcome-adaptive assignment policies."
reusable: unknown
reraise_status: retry
gap_reasons:
  - "The advertised polynomial-memory oracle frontier is not delivered: the note proves only the Markov truncated-HT upper bound, while its all-policy lower bound is assumed in a conditional theorem."
  - "The horizon-eight cancellation and endpoint calculations do not control general assignment paths and therefore contribute no asymptotic converse."
  - "Because the note supplies neither an unconditional logarithmic lower bracket nor policy-optimality evidence, its contribution and leading-journal significance remain well below the field-tier target."
reusable_artifacts:
  - "discovery/core.json: final graph with the radius-aware oracle upper certificate, structural likelihood cancellation, enumerated randomized-offset prior family, and exact multiscale payoff lemma."
  - "discovery/writeup.tex: rendered sound partial derivation, including the no-carryover boundary and operational window result."
  - "discovery/solve_tex/solve_thm_polynomial_oracle_frontier.tex: failed lower-bound attempt and the exact T=16 counterexample path 0000111001110101 to the naive single-threshold dichotomy."
seeds_burned: []
proof_attempt_summary: |
  The run audited and strengthened the constructive Markov/truncated-HT side, proving a radius-aware optimized upper certificate and preserving the ordinary no-carryover boundary. It repaired the adaptive-likelihood typing, built randomized-offset block and arm-specific band priors, and proved their local posterior-variance, endpoint-separation, and divergence calculations. The all-policy lower frontier nevertheless remained conditional: the attempted first-separating-node/dyadic charging argument did not yield a common-measure occupancy-information inequality, and an explicit T=16 path refuted its naive single-threshold form.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 14883564
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 14883564
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# exp_switchback_polynomial_decay_oracle_frontier / v1 — Downgraded

**Topic.** Polynomial-memory oracle frontier for sequential switchback experiments. Fix B>0, C>0 and known beta>0. In the banked parent's one-unit finite-population model, potential outcomes are fixed maps of binary treatment histories into [-B,B] and obey sum_l (1+l)^(1+beta)|Delta_l Y_t|<=C. Randomized assignments may depend on observed past assignments and outcomes. For the all-treated-versus-all-control GATE, prove over all sequential policies and estimators that minimax MSE is Theta(T^(-2beta/(2beta+1))), with explicit finite-horizon constants, while C=0 has the ordinary Theta(T^-1) frontier. Audit the parent's Markov/truncated-HT upper bound. For the converse, fix the adversarial prior before assignment, derive a policy-uniform multiscale occupancy/information inequality, and combine common-null block priors with arm-specific positive-part band bumps. Do not reuse the parent's invalid cadence dichotomy and do not claim unknown-beta adaptation. Connect the oracle block scale T^(1/(2beta+1)) to operational window choice in Statsig-style and marketplace switchbacks. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolver derived |hat theta_b-tilde theta_b|<=(2eC/beta)(b+1)^(-beta) and combined it with the parent's auxiliary variance bound, giving the corrected MSE exponent. It obtained exact posterior-variance components B^2/T and B^2 L^2 E[U_L]/T^2, and constructed arm-specific band-bump likelihoods whose assignment-kernel factors cancel under adaptive policies. Strict alternation, sparse minority pulses, constant paths, zero propensities, and small beta were stress-tested; no current theorem was found to subsume the result. UNRESOLVED BOTTLENECK: Prove the single sequential multiscale occupancy/information lemma showing that every adaptive assignment kernel leaves either blockwise counterfactual variance of order L/T or an arm-specific dyadic bump with bounded information and separation L^(-beta), for L around T^(1/(2beta+1)); remove or retain any unavoidable logarithm honestly. EARLY KILL TEST: Enumerate binary paths through T<=16 and test the deterministic dyadic occupancy inequality on sparse-switch, strict-alternation, unequal-periodic, one-switch, and concatenated-cadence paths. Any legal constant-order violation, or a required logarithmic loss, forces immediate revision of the headline. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_switchback_polynomial_decay_oracle_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The advertised all-policy frontier remains conditional on the unresolved sequential multiscale certificate; D0.5 graded the sound delivered package incremental with paper_score_ceiling 4.3 below the field floor 7.2.

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

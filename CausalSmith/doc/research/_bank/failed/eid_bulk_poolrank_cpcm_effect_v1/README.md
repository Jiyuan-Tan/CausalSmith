---
qid: eid_bulk_poolrank_cpcm_effect
spec: v1
topic: "Pool-rank recovery of cell-type Poisson-CPCM effects from designed bulk mixtures. For K invariant type-specific nonnegative-integer count vectors, observe replicate raw-count pools with known integer composition matrix M, independent cells, no cross-cell interaction, and no unknown thinning or normalization. Prove that full column rank of M is necessary and sufficient for uniform recovery of all unrestricted type joint laws, fully crediting Shih--Hero's log-transform inversion and using positive independent-Poisson aliases for the converse. On a declared compact, causally sufficient, pairwise-identifiable nonlinear Poisson-CPCM subclass, transfer recovery to labeled type DAGs and fixed truncated-factorization intervention contrasts. Give a normwise lower-envelope stability theorem involving ||M+||, and, on a prespecified finite PGF grid, derive replicate-well delta covariance, sample-split graph selection, and pointwise sandwich-Wald inference under certified graph-separation and Jacobian margins. Consumer: Luo--Sun--Zhang's empirical bulk-gene causal-recoverability workflow, prospectively redesigned with linearly independent known-composition replicate pools. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The score-blind presolve derived the full-rank inverse and positive-Poisson converse, verified a nonlinear three-node CPCM witness with intervention contrasts 3 and 25, established normwise stability and cross-type/grid covariance, and proved existence of a separating finite grid for compact positive-polynomial Poisson DAG families from score-information positivity, signed-PGF uniqueness, and compactness. A 27-point pilot had component-Jacobian singular values 0.00326480 and 0.00262027; Shih--Hero and transform-GMM collisions, rank-deficient graph aliases, finite-grid nonparametric aliases, unknown channels, vanishing edges, and pooling attenuation were checked. UNRESOLVED BOTTLENECK: Produce an explicit certified grid with a positive wrong-graph score gap, uniform within-graph Jacobian lower bound, controlled PGF truncation, and useful propagated contrast precision over the compact parameter boxes. EARLY KILL TEST: For p=3, M=[[1,1],[1,2]], coefficients in [1/2,3], and grid {0.8,0.9,0.97}^3, certify separation from all 24 incorrect single-type DAGs and both witness Jacobians by interval/global optimization; an exact collision kills that protocol, and failure of useful precision after one prespecified grid refinement stops the practical launch. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_bulk_poolrank_cpcm_effect.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "No certified wrong-graph, remote/local injectivity, uniform Jacobian, tail, covariance, or useful-precision proof object was produced for Xi0 or Xi1."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The proposal's concrete early-kill deliverable was a certified grid with positive global margins and useful precision, but the core delivers only an existence theorem and conditional certifier while the sole prescribed benchmark remains open."
  - "Neither prescribed run of \\(\\mathfrak C\\) has a supplied validated proof object."
  - "Stage 0.5 (typed) finding outside D0.R core-edit scope — kernel_substituted@oeq:three-node-benchmark."
reusable_artifacts:
  - "discovery/core.json: full-rank count-PGF inversion, positive-Poisson nullspace converse, stability, CPCM graph/effect transfer, finite-grid existence, and conditional certifier theorem graph."
  - "discovery/writeup.tex: derivations and the exact open Xi0/Xi1 benchmark specification."
  - "orchestrator/decision_log.jsonl: citation repairs, six primary-source attestations, D0 adjudication receipts, and both terminal validity-gate judgments."
seeds_burned:
  - index: 0
    one_liner: "finite-grid-certificate"
    reason: "The selected finite-grid-certificate seed required a complete outward-rounded Xi0/Xi1 proof object; no executable bounded certifier existed and D0.5 rejected substitution by conditional machinery."
proof_attempt_summary: |
  Discovery proved the unrestricted full-column-rank recovery frontier, a positive-Poisson converse, stability, causal transfer, finite-grid existence, and soundness of a conditional tri-valued certifier. The accepted focal contribution nevertheless required executing that certifier on Xi0 and, if needed, Xi1 with a complete outward-rounded proof object; no such executable bounded implementation or certificate was produced. D0.5 therefore rejected the conditional framework as a substitute for the promised concrete kernel.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 46287148
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 46287148
  total_tokens_consumed: null
banked_on: "2026-09-15"
---

# eid_bulk_poolrank_cpcm_effect / v1 — Failed

**Topic.** Pool-rank recovery of cell-type Poisson-CPCM effects from designed bulk mixtures. For K invariant type-specific nonnegative-integer count vectors, observe replicate raw-count pools with known integer composition matrix M, independent cells, no cross-cell interaction, and no unknown thinning or normalization. Prove that full column rank of M is necessary and sufficient for uniform recovery of all unrestricted type joint laws, fully crediting Shih--Hero's log-transform inversion and using positive independent-Poisson aliases for the converse. On a declared compact, causally sufficient, pairwise-identifiable nonlinear Poisson-CPCM subclass, transfer recovery to labeled type DAGs and fixed truncated-factorization intervention contrasts. Give a normwise lower-envelope stability theorem involving ||M+||, and, on a prespecified finite PGF grid, derive replicate-well delta covariance, sample-split graph selection, and pointwise sandwich-Wald inference under certified graph-separation and Jacobian margins. Consumer: Luo--Sun--Zhang's empirical bulk-gene causal-recoverability workflow, prospectively redesigned with linearly independent known-composition replicate pools. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The score-blind presolve derived the full-rank inverse and positive-Poisson converse, verified a nonlinear three-node CPCM witness with intervention contrasts 3 and 25, established normwise stability and cross-type/grid covariance, and proved existence of a separating finite grid for compact positive-polynomial Poisson DAG families from score-information positivity, signed-PGF uniqueness, and compactness. A 27-point pilot had component-Jacobian singular values 0.00326480 and 0.00262027; Shih--Hero and transform-GMM collisions, rank-deficient graph aliases, finite-grid nonparametric aliases, unknown channels, vanishing edges, and pooling attenuation were checked. UNRESOLVED BOTTLENECK: Produce an explicit certified grid with a positive wrong-graph score gap, uniform within-graph Jacobian lower bound, controlled PGF truncation, and useful propagated contrast precision over the compact parameter boxes. EARLY KILL TEST: For p=3, M=[[1,1],[1,2]], coefficients in [1/2,3], and grid {0.8,0.9,0.97}^3, certify separation from all 24 incorrect single-type DAGs and both witness Jacobians by interval/global optimization; an exact collision kills that protocol, and failure of useful precision after one prespecified grid refinement stops the practical launch. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_bulk_poolrank_cpcm_effect.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** D0.5 terminal kernel_substituted@oeq:three-node-benchmark: the accepted focal Xi0/Xi1 proof-producing certificate remains open, while only conditional certifier and existence machinery was delivered.

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

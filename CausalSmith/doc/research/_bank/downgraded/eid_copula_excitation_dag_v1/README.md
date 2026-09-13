---
qid: eid_copula_excitation_dag
spec: v1
topic: "Projective copula-excitation frontier for scale-erased causal discovery. Fix p and an invariant acyclic linear-Gaussian SCM with unknown baseline innovation variances. Across environments, innovation coordinates receive known positive multipliers, but each site releases only its Gaussian copula/correlation matrix, with unrelated marginal scales. Define the projective Cholesky fiber of compatible directed supports. Prove the sharp universal generic criterion: every pair of multiplier-profile columns is projectively distinct iff every DAG is generically a singleton of this fiber; give explicit nonisomorphic fork/chain twins when profiles tie. Construct canonical order predictors and exact fiber recovery, including an O(Ep^3) conditional-pair algorithm on generic complete DAGs, then invert Kendall-tau rank summaries into honest graph confidence sets under explicit separation. Consumer: FedCDH-style federated summary sharing and the backShift workflow, which can accept rank-only site releases exactly above the excitation boundary. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Reference-environment Cholesky normalization was derived to eliminate continuous scale search: each candidate order determines one canonical standardized recursive model and predicts every other correlation matrix. Reversed-edge polynomial witnesses give an all-p generic uniqueness spine under pairwise nonproportional schedule columns; tied columns yield an explicit positive fork/chain counterfamily. Exact computations recovered all 25 labeled three-node DAGs across 300 rational parameter choices, checked diagonal-gauge equivariance and weak/singular regimes, and verified conditional-pair peeling through p=6. No direct primary-source or internal collision was found. Compressed standard claims, the all-p polynomial argument, sparse-graph computation, and the uniform inference perturbation layer still require independent audit. UNRESOLVED BOTTLENECK: Prove uniform Cholesky-predictor perturbation bounds and close the finite-sample graph-confidence theorem with an explicit fallback convention and normalized beta-min margin. EARLY KILL TEST: Reconstruct the canonical-order reduction under arbitrary positive reference rescaling and reproduce the p=3 covariance example with d_1=(1,4,9) and all five wrong-order exclusions; any legal model outside the canonical list or matching wrong order stops this spine. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_copula_excitation_dag.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "The field-level promise was not met because sparse-fiber recovery remains factorial rather than output-sensitive or polynomial-delay, and practical usefulness under realistic finite-sample margins was not demonstrated."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The claimed cubic recovery result is confined to generic complete DAGs, while arbitrary sparse fibers still require factorial order traversal and the output-sensitive enumeration question remains open."
  - "The confidence set has finite-sample coverage, but informative singleton recovery requires imposed conditioning, beta-min, wrong-order separation, exact calibration, and fixed p, with no numerical study showing that these thresholds yield useful sets at realistic sample sizes."
  - "Those scope restrictions, the unresolved sparse computation problem, and the absence of an applied or simulation demonstration constrain the leading-journal score despite the delivered field-level identification theorem."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_oeq_sparse_output_sensitive_enumeration.json
  - discovery/solve_thm_conditional_pair_completeness.json
seeds_burned: []
proof_attempt_summary: |
  The derivation established the sound sharp generic projective-schedule frontier, tied-profile counterexamples, canonical recovery, a cubic complete-DAG procedure, and fixed-p rank-summary confidence sets; both D0.5 mathematical panels passed with no findings. The field-tier package collapsed at the contribution gate because general sparse recovery remained factorial and practical singleton recovery depended on strong margins without an empirical demonstration. A future re-raise should supply genuinely output-sensitive or polynomial-delay sparse enumeration, or comparably substantial new robustness and applied architecture, rather than repeat the completed perturbation analysis.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 33474728
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 33474728
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# eid_copula_excitation_dag / v1 — Downgraded

**Topic.** Projective copula-excitation frontier for scale-erased causal discovery. Fix p and an invariant acyclic linear-Gaussian SCM with unknown baseline innovation variances. Across environments, innovation coordinates receive known positive multipliers, but each site releases only its Gaussian copula/correlation matrix, with unrelated marginal scales. Define the projective Cholesky fiber of compatible directed supports. Prove the sharp universal generic criterion: every pair of multiplier-profile columns is projectively distinct iff every DAG is generically a singleton of this fiber; give explicit nonisomorphic fork/chain twins when profiles tie. Construct canonical order predictors and exact fiber recovery, including an O(Ep^3) conditional-pair algorithm on generic complete DAGs, then invert Kendall-tau rank summaries into honest graph confidence sets under explicit separation. Consumer: FedCDH-style federated summary sharing and the backShift workflow, which can accept rank-only site releases exactly above the excitation boundary. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Reference-environment Cholesky normalization was derived to eliminate continuous scale search: each candidate order determines one canonical standardized recursive model and predicts every other correlation matrix. Reversed-edge polynomial witnesses give an all-p generic uniqueness spine under pairwise nonproportional schedule columns; tied columns yield an explicit positive fork/chain counterfamily. Exact computations recovered all 25 labeled three-node DAGs across 300 rational parameter choices, checked diagonal-gauge equivariance and weak/singular regimes, and verified conditional-pair peeling through p=6. No direct primary-source or internal collision was found. Compressed standard claims, the all-p polynomial argument, sparse-graph computation, and the uniform inference perturbation layer still require independent audit. UNRESOLVED BOTTLENECK: Prove uniform Cholesky-predictor perturbation bounds and close the finite-sample graph-confidence theorem with an explicit fallback convention and normalized beta-min margin. EARLY KILL TEST: Reconstruct the canonical-order reduction under arbitrary positive reference rescaling and reproduce the p=3 covariance example with d_1=(1,4,9) and all five wrong-order exclusions; any legal model outside the canonical list or matching wrong order stops this spine. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_copula_excitation_dag.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** The note proves the advertised sharp generic identification frontier only within an acyclic linear-Gaussian model having exactly known, coordinatewise normalized innovation multipliers and fixed vertex correspondence; complete-DAG-only cubic recovery, factorial sparse traversal, fixed-p strong-margin inference, and no applied demonstration cap the sound result at subfield.

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

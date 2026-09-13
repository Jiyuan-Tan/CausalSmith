---
qid: eid_limvam_calibration_frontier
spec: v1
topic: "Complete removable-root calibration frontier for paired Gaussian LiMVAMs. For finite p variables and m views, observe every within-view covariance but paired cross-view blocks only inside a calibration subset S; views share an unknown topological order, view-specific coefficients, and independent-across-variable Gaussian disturbance vectors with positive-definite cross-view covariances. Prove that an order is compatible iff its order-constrained modified-Cholesky residual cross-blocks are diagonal, and that a removable-root recursion is necessary and sufficient with Schur-complement state indexed only by the removed variable set. Build a memoized 2^p-state plus output-size algorithm returning all distinct full-view coefficient tuples, positive-definite noise certificates, the essential ancestral poset, and a minimum-cardinality S identifying the full tuple. Add finite-sample operator-norm covariance-region inversion, Hausdorff coefficient-set consistency off feasibility boundaries, and exact poset recovery under fixed score and path-product margins. Apply it to Heurtebise et al.'s Cam-CAN MEG and fMRI PairwiseLiMVAM/DirectLiMVAM workflow, using a certified participant calibration subset for order while retaining every participant marginal for coefficients. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolver derived that each fixed order uniquely determines every view's modified-Cholesky residualizer and is compatible exactly when all selected residual cross-covariance blocks are diagonal. Those diagonal blocks are positive definite and extend to unselected views by zero cross-disturbance completion. Sequential root removal equals projection onto the span of removed variables, so its Schur complement depends only on that set; root cross-orthogonality plus recursive feasibility is necessary and sufficient. Exact p=2 calculations gave reverse compatibility iff the two disturbance correlations agree. Exact p=m=3 enumeration matched the subset DP for all six orders and seven nonempty calibration subsets; a chain with selected correlations 1/5, 2/5, and 3/5 was identified by S={1,2}, while view 3 was recovered from its marginal. Checks covered equal-correlation ambiguity, unequal-correlation rejection, zero-edge duplicate orders, residual positivity, unobserved-block completion, consumer organization, and current-literature collisions. UNRESOLVED BOTTLENECK: Prove output-sensitive quotient enumeration that emits every distinct full-view coefficient tuple once from the 2^p-state order DAG without factorial traversal when many topological orders induce the same tuple. EARLY KILL TEST: Re-run exact-arithmetic p=m=3 exhaustive order/subset enumeration against DP leaves and require both leaf-set equality and a proper-subset unique-tuple witness; any mismatch stops the run."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The 2^p removed-set recursion enumerates compatible orders, not distinct coefficient tuples exactly once with output-sensitive complexity; minimum calibration therefore remains exhaustive."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The 2^p-state DAG enumerates compatible orders only; it does not deliver the promised output-sensitive, exact-once enumeration of distinct coefficient tuples."
  - "The established fiber lemma canonicalizes inducing orders only after a tuple is known; traversing all compatible paths can remain factorial even when N_out=1."
  - "The paper is mathematically sound and substantially strengthened, but the original field-level computational kernel remains unproved."
reusable_artifacts:
  - discovery/core.json
  - discovery/solve_thm_calibration_graph_completion.json
  - discovery/solve_tex/solve_thm_calibration_graph_completion.tex
  - discovery/solve_thm_generic_calibration_elbow.json
  - discovery/solve_thm_covariance_region_inversion.json
  - discovery/solve_oeq_output_sensitive_quotient.json
seeds_burned:
  - index: 0
    one_liner: "A complete partial-calibration LiMVAM equivalence theorem: an order is compatible if and only if every observed order-residual cross-block is diagonal, with a path-independent removed-set recursion."
    reason: "The sole proposal angle exhausted bounded graph-completion and inference repairs; the remaining exact-once quotient oracle is not derivable noncircularly from the removed-set DAG."
proof_attempt_summary: |
  The run proved a sound component-aligned Gaussian theory: fixed-order residual compatibility,
  arbitrary observation-graph positive-definite completion with chordal and nonchordal certificates,
  a generic one-pair calibration elbow, and graph-aware covariance-region and poset recovery.
  It could not turn the removed-set order DAG into a duplicate-free output-sensitive enumerator of
  distinct coefficient tuples; the needed child oracle would assume the unresolved crux and path
  traversal can remain factorial. A future re-raise needs a genuinely noncircular quotient algorithm
  or a precise hardness replacement, not another graph-completion or unrestricted-class extension.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 70415840
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-07"
---

# eid_limvam_calibration_frontier / v1 — Downgraded

**Topic.** Complete removable-root calibration frontier for paired Gaussian LiMVAMs. For finite p variables and m views, observe every within-view covariance but paired cross-view blocks only inside a calibration subset S; views share an unknown topological order, view-specific coefficients, and independent-across-variable Gaussian disturbance vectors with positive-definite cross-view covariances. Prove that an order is compatible iff its order-constrained modified-Cholesky residual cross-blocks are diagonal, and that a removable-root recursion is necessary and sufficient with Schur-complement state indexed only by the removed variable set. Build a memoized 2^p-state plus output-size algorithm returning all distinct full-view coefficient tuples, positive-definite noise certificates, the essential ancestral poset, and a minimum-cardinality S identifying the full tuple. Add finite-sample operator-norm covariance-region inversion, Hausdorff coefficient-set consistency off feasibility boundaries, and exact poset recovery under fixed score and path-product margins. Apply it to Heurtebise et al.'s Cam-CAN MEG and fMRI PairwiseLiMVAM/DirectLiMVAM workflow, using a certified participant calibration subset for order while retaining every participant marginal for coefficients. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolver derived that each fixed order uniquely determines every view's modified-Cholesky residualizer and is compatible exactly when all selected residual cross-covariance blocks are diagonal. Those diagonal blocks are positive definite and extend to unselected views by zero cross-disturbance completion. Sequential root removal equals projection onto the span of removed variables, so its Schur complement depends only on that set; root cross-orthogonality plus recursive feasibility is necessary and sufficient. Exact p=2 calculations gave reverse compatibility iff the two disturbance correlations agree. Exact p=m=3 enumeration matched the subset DP for all six orders and seven nonempty calibration subsets; a chain with selected correlations 1/5, 2/5, and 3/5 was identified by S={1,2}, while view 3 was recovered from its marginal. Checks covered equal-correlation ambiguity, unequal-correlation rejection, zero-edge duplicate orders, residual positivity, unobserved-block completion, consumer organization, and current-literature collisions. UNRESOLVED BOTTLENECK: Prove output-sensitive quotient enumeration that emits every distinct full-view coefficient tuple once from the 2^p-state order DAG without factorial traversal when many topological orders induce the same tuple. EARLY KILL TEST: Re-run exact-arithmetic p=m=3 exhaustive order/subset enumeration against DP leaves and require both leaf-set equality and a proper-subset unique-tuple witness; any mismatch stops the run.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** Final D0.5 math review passed, but the general referee assessed subfield (7.4) and the decision panel found the promised duplicate-free output-sensitive coefficient-tuple enumeration undelivered.

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

---
qid: eid_softlcd_terminalrow_complete
spec: v1
topic: "Corrected terminal-row compatibility and the covariance information frontier for soft-intervention linear causal disentanglement. For every 2<=p<=q and q-node DAG G, observe one baseline and one unknown-target single-node soft-intervention context per latent node in X^(k)=F(I-Lambda^(k))^-1 epsilon^(k), with full-row-rank mixing, noncollinear columns, exact nonzero graph support, independent non-Gaussian errors, and algebraically independent nonzero incoming-edge changes. Define Hsoft(G) from the actual intervention rows h_k^T=delta_k^T(I-Lambda^0)^-1, not the published observational-path substitution, with exact support and noncancellation admissibility; define Cov_p(G) by generic positive-real covariance compatibility. Prove: (1) a sound-and-complete terminal-copy strict-gammoid plus affine-hyperplane certificate algorithm for Hsoft and an exact characterization of when the published Definition 3.14 class agrees; (2) Cov_q(G)=Hsoft(G) under square mixing by whitening and ancestor-order recovery, including all sign, scale, support, and variance branches; and (3) for p<q, a graph-specific non-QE positive-real projection-completeness criterion deciding Cov_p(G)\\Hsoft(G), with generic realization or separator certificates, explicit complexity, and infinite equality and strict families. Credit Leyes Carreno--Meroni--Seigal 2025 Theorem 1.7, Definition 3.14, and Problems 5.1--5.2, and Squires et al. 2023 for injective soft-intervention transitive-closure recovery. The companion LCD workflow is a prospective same-question consumer: it must report the corrected compatible DAG set and whether high cumulants genuinely remove covariance alternatives. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact symbolic checks give a generic four-node determinant gamma(beta*d-b*delta) refuting the observational-path substitution, five positive-definite square covariances, and a separate p=2 rational covariance collision with actual-row obstruction -2. Terminal-copy linkage and affine support testing, square covariance equality, an infinite small-component equality family, and a complete regular reduction of the four-node noninjective fork to eight two-scalar positive systems were derived. A stronger rational collision keeps candidate variances T+144/121 and 19/4 positive for every T>0, T!=1. Classical-linkage, generic-QE, degenerate-rank, all-sign/variance-chamber, rational-certificate, finite-sample, consumer-deployment, and bounded-literature failure modes were checked; the all-p positive chamber union remains open. UNRESOLVED BOTTLENECK: Prove a graph-specific, non-QE positive-real projection-completeness criterion deciding whether the finite union of every legal covariance branch has complement of empty relative interior in the full true parameter domain. EARLY KILL TEST: Complete the eight-branch two-scalar positive-feasibility classification of the four-node p=2 fork over its full true parameter domain and verify every proposed separator against the original context covariance equations; pivot if the structured reduction is unsound or generalizes only through unrestricted quantifier elimination. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_softlcd_terminalrow_complete.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "Missing all-eight-system chamberwise density-or-separation classification, square-mixing equality, and the non-QE positive-real compiler; only pointwise fork separation and finite branch reductions were delivered."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The delivered core honestly leaves the proposed all-graph non-QE positive-real projection compiler open and contains no square-mixing Cov_q=Hsoft theorem, so it substitutes terminal correction plus a pointwise fork witness for the promised covariance-frontier result."
  - "The note proves a general terminal-copy/affine characterization of corrected actual-row compatibility, an arithmetic per-candidate algorithm, and a concrete refutation of the published Theorem 3.15, but these constitute a narrow correction rather than the advertised covariance information frontier."
  - "Classify the projected feasible union of all eight two-scalar fork systems over the full true-parameter domain and prove the resulting density or separation conclusion chamber by chamber."
reusable_artifacts:
  - discovery/solve_thm_terminal_certificate.tex
  - discovery/solve_prop_published_mismatch.tex
  - discovery/solve_prop_fork_pointwise_separation.tex
  - discovery/solve_thm_fork_all_chamber_projection.tex
  - discovery/core.json
seeds_burned: []
proof_attempt_summary: |
  The run proved the corrected actual-row terminal-copy/affine membership criterion with an O(q^4)
  field-operation certificate, an explicit generic counterexample to the published theorem, exact
  finite covariance-branch reductions, and a quotient-invariant one-parameter fork separation. The
  prescribed fork-only resultant/subresultant CAD attempt did not produce projection polynomials,
  full-dimensional sign cells, or Thom certificates, so the chamberwise density-or-separation theorem,
  square-mixing equality, and all-graph non-QE compiler remain open.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 66857936
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 66857936
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# eid_softlcd_terminalrow_complete / v1 — Downgraded

**Topic.** Corrected terminal-row compatibility and the covariance information frontier for soft-intervention linear causal disentanglement. For every 2<=p<=q and q-node DAG G, observe one baseline and one unknown-target single-node soft-intervention context per latent node in X^(k)=F(I-Lambda^(k))^-1 epsilon^(k), with full-row-rank mixing, noncollinear columns, exact nonzero graph support, independent non-Gaussian errors, and algebraically independent nonzero incoming-edge changes. Define Hsoft(G) from the actual intervention rows h_k^T=delta_k^T(I-Lambda^0)^-1, not the published observational-path substitution, with exact support and noncancellation admissibility; define Cov_p(G) by generic positive-real covariance compatibility. Prove: (1) a sound-and-complete terminal-copy strict-gammoid plus affine-hyperplane certificate algorithm for Hsoft and an exact characterization of when the published Definition 3.14 class agrees; (2) Cov_q(G)=Hsoft(G) under square mixing by whitening and ancestor-order recovery, including all sign, scale, support, and variance branches; and (3) for p<q, a graph-specific non-QE positive-real projection-completeness criterion deciding Cov_p(G)\Hsoft(G), with generic realization or separator certificates, explicit complexity, and infinite equality and strict families. Credit Leyes Carreno--Meroni--Seigal 2025 Theorem 1.7, Definition 3.14, and Problems 5.1--5.2, and Squires et al. 2023 for injective soft-intervention transitive-closure recovery. The companion LCD workflow is a prospective same-question consumer: it must report the corrected compatible DAG set and whether high cumulants genuinely remove covariance alternatives. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact symbolic checks give a generic four-node determinant gamma(beta*d-b*delta) refuting the observational-path substitution, five positive-definite square covariances, and a separate p=2 rational covariance collision with actual-row obstruction -2. Terminal-copy linkage and affine support testing, square covariance equality, an infinite small-component equality family, and a complete regular reduction of the four-node noninjective fork to eight two-scalar positive systems were derived. A stronger rational collision keeps candidate variances T+144/121 and 19/4 positive for every T>0, T!=1. Classical-linkage, generic-QE, degenerate-rank, all-sign/variance-chamber, rational-certificate, finite-sample, consumer-deployment, and bounded-literature failure modes were checked; the all-p positive chamber union remains open. UNRESOLVED BOTTLENECK: Prove a graph-specific, non-QE positive-real projection-completeness criterion deciding whether the finite union of every legal covariance branch has complement of empty relative interior in the full true parameter domain. EARLY KILL TEST: Complete the eight-branch two-scalar positive-feasibility classification of the four-node p=2 fork over its full true parameter domain and verify every proposed separator against the original context covariance equations; pivot if the structured reduction is unsound or generalizes only through unrestricted quantifier elimination. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_softlcd_terminalrow_complete.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The delivered actual-row correction is mathematically sound, but the cold review rates it incremental (5.4 below the 7.4 field floor); the promised chamberwise covariance frontier remains open after the prescribed nonidentical bounded attempt failed.

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

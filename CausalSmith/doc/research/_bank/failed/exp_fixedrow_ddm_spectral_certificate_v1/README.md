---
qid: exp_fixedrow_ddm_spectral_certificate
spec: v1
topic: "Certified-accuracy fixed-row spectral distributional-discrepancy benchmarks for unequal randomization. For fixed r>=2, integer B in Z^(r x n), rational prescribed treatment probabilities p_i, z in {-1,1}^n with E[z]=2p-1, and OPT=min_D lambda_max(E[B(z-Ez)(z-Ez)'B']), prove exact equivalence between assignment laws and reachable vector-prefix flows preserving every marginal and the terminal covariance. Construct rational epsilon-instance-optimal designs with matching PSD/spectral-Bellman lower certificates in time polynomial in the expanded lattice, input length, and log(1/epsilon); verify supplied algebraic exact certificates, claiming polynomial exact construction only when a polynomial-size projected covariance-hull description is supplied. Extract an optimal sparse law with at most n+r(r+1)/2 atoms, state the sharper attainable-feature-rank bound, preserve the corrected finite-population Horvitz--Thompson factor 1/(4n^2), and build a thin-matrix adapter/benchmark protocol for Rao--Zhang's released pure-balance MWU code. Explicitly credit Altschuler--Boix-Adsera for scalarized structured MOT, Haus for mixability/PARTITION, and standard SDP/ellipsoid machinery; exclude unrestricted exact construction, identity-block robustness, fixed counts, entropy constraints, superpopulation inference, and unexecuted performance claims. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Three fresh presolves derived exact flow/law and covariance preservation, minimax certificates valid at eigenvalue ties, explicit primal and spectral/Bellman feasibility repairs, a polynomial-bit dual box, covariance-preserving support compression, and exact marginal postprocessing for empirical MWU outputs. Exact symbolic checks verified the irrational optimum (67+sqrt(1609))/288 for a rational two-row unequal-margin instance; sixteen flow/Bellman/feature-rank cases and sixty marginal-repair cases passed. Boundary audits covered zero columns, rank deficiency, zero covariance, endpoint propensities, rational-value failure, support off-by-one errors, HT normalization, and projected-hull complexity; current-source checks found no complete-package collision. UNRESOLVED BOTTLENECK: Instantiate a concrete rational ellipsoid/truncation theorem and prove that the implementation meets the draft's exact-affine, delta-residual output contract in polynomial expanded-lattice, input-bit, and logarithmic-accuracy time; the conditioning bounds and repair algebra are supplied. EARLY KILL TEST: Execute the four-cell pilot: the irrational witness at certified gap <=2^-12, zero-column marginal preservation, a nondegenerate thin full-row-rank instance through unchanged-source zero padding, and the exact zero-matrix branch; independently verify repaired laws and certificates, stopping or pivoting if any mathematical cell fails or no nondegenerate consumer cell works without substantive source changes. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_fixedrow_ddm_spectral_certificate.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: REVISE
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: retry
gap_reasons:
  - "The exact zero-residual restriction mu=B^T theta is a restrictive consumer model, not the standard Harshaw et al. condition cited under that name; retag it novel and justify its scientific setting, or cite a source imposing this exact span."
  - "The unit Euclidean coefficient ball is an additional normalization for the proposal's consumer risk, not a standard condition established by the cited Gram--Schmidt-walk result; retag it novel with an application-scale justification."
reusable_artifacts:
  - "discovery/proto_core.json — field-rated PrefixCert kernel, exact irrational witness, literature map, and rational finite-support/certificate specification"
  - "reviews/angle0_v6.json — final source-verification receipts and the two unresolved consumer-assumption flags"
seeds_burned:
  - index: 0
    one_liner: "Fixed-row certified spectral design"
    reason: "Six revisions, including one consult-approved extra revision, repeated the same nonessential consumer-assumption disclosure defect."
proof_attempt_summary: |
  Six D-0.5 proposal revisions refined a field-rated PrefixCert kernel for rational finite-support recovery and locally checkable two-sided additive certificates. The run exhausted its angle cap before derivation because the exact outcome-span and coefficient-ball restrictions were still structurally tagged as standard consumer assumptions after an explicit repair directive and one consult-approved extra revision. No D0 derivation or Lean formalization was started; a future retry should remove the orphan Horvitz--Thompson consumer bridge and preserve the standalone PrefixCert kernel.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 17584205
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 17584205
  total_tokens_consumed: null
banked_on: "2026-09-15"
---

# exp_fixedrow_ddm_spectral_certificate / v1 — Failed

**Topic.** Certified-accuracy fixed-row spectral distributional-discrepancy benchmarks for unequal randomization. For fixed r>=2, integer B in Z^(r x n), rational prescribed treatment probabilities p_i, z in {-1,1}^n with E[z]=2p-1, and OPT=min_D lambda_max(E[B(z-Ez)(z-Ez)'B']), prove exact equivalence between assignment laws and reachable vector-prefix flows preserving every marginal and the terminal covariance. Construct rational epsilon-instance-optimal designs with matching PSD/spectral-Bellman lower certificates in time polynomial in the expanded lattice, input length, and log(1/epsilon); verify supplied algebraic exact certificates, claiming polynomial exact construction only when a polynomial-size projected covariance-hull description is supplied. Extract an optimal sparse law with at most n+r(r+1)/2 atoms, state the sharper attainable-feature-rank bound, preserve the corrected finite-population Horvitz--Thompson factor 1/(4n^2), and build a thin-matrix adapter/benchmark protocol for Rao--Zhang's released pure-balance MWU code. Explicitly credit Altschuler--Boix-Adsera for scalarized structured MOT, Haus for mixability/PARTITION, and standard SDP/ellipsoid machinery; exclude unrestricted exact construction, identity-block robustness, fixed counts, entropy constraints, superpopulation inference, and unexecuted performance claims. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Three fresh presolves derived exact flow/law and covariance preservation, minimax certificates valid at eigenvalue ties, explicit primal and spectral/Bellman feasibility repairs, a polynomial-bit dual box, covariance-preserving support compression, and exact marginal postprocessing for empirical MWU outputs. Exact symbolic checks verified the irrational optimum (67+sqrt(1609))/288 for a rational two-row unequal-margin instance; sixteen flow/Bellman/feature-rank cases and sixty marginal-repair cases passed. Boundary audits covered zero columns, rank deficiency, zero covariance, endpoint propensities, rational-value failure, support off-by-one errors, HT normalization, and projected-hull complexity; current-source checks found no complete-package collision. UNRESOLVED BOTTLENECK: Instantiate a concrete rational ellipsoid/truncation theorem and prove that the implementation meets the draft's exact-affine, delta-residual output contract in polynomial expanded-lattice, input-bit, and logarithmic-accuracy time; the conditioning bounds and repair algebra are supplied. EARLY KILL TEST: Execute the four-cell pilot: the irrational witness at certified gap <=2^-12, zero-column marginal preservation, a nondegenerate thin full-row-rank instance through unchanged-source zero padding, and the exact zero-matrix branch; independently verify repaired laws and certificates, stopping or pivoting if any mathematical cell fails or no nondegenerate consumer cell works without substantive source changes. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_fixedrow_ddm_spectral_certificate.md.

**Novelty target.** field

**Stage -0.5 verdict.** REVISE

**Stage 0.5 verdict.** NA

**Banking reason.** D-0.5 angle 0 v6 exhausted its revision cap after reviewer REVISE: ass:weighted-outcome-span and ass:coefficient-ball remained mis-tagged as standard consumer conditions.

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

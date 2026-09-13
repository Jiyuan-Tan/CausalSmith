---
qid: eid_crl_transcript_betamin_boundary
spec: v1
topic: "A query-local beta-min phase boundary for finite-sample interventional causal representation learning. Fix Acarturk et al.'s deterministic population recovery program with a public smallest-label tie rule. For public g0,h0>0, let P_A(g0,h0) contain models whose every positive eigenvalue and nonzero projector comparison on that population transcript is at least g0 and h0, respectively; this is a model promise, never inferred from post-hoc empirical gaps. In the linear Gaussian variance-reset subclass with publicly conditioned observed covariances, construct an honest sequential certificate that returns the exact latent transitive closure and an approximate parent-supported encoder or abstains, with probability at least 1-alpha and polynomial sample dependence on n,kappa,g0^{-1},h0^{-1},log(1/alpha), but no unqueried subset margin. Prove that without a restriction excluding graph-changing weak alternatives, every uniformly alpha-valid randomized sequential procedure returns the correct singleton empty graph at the specified bounded-kernel logistic null with probability at most alpha. Finally, prove that for every n>=4 an explicit uniformly conditioned Gaussian bipartite family has reached gaps at least 1/40 and graph comparisons zero or one across n^2+2n-2 matrix occurrences, while the published all-subset margin is at most 2^(-2n-1) through the unqueried subset {3,4}. Use actual projector geometry, not the source's false printed angular expression. Consumer: add declared-gap certification, abstention/set output, and encoder error bars to the official finite-sample-linear-crl implementation. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Fresh presolve derived ||Rhat_m-R_m||<=40*kappa^4*a from covariance error a, exact rank/projector intervals, transcript induction, and encoder-range error at most 4*sqrt(n)*e/g0. It proved the all-n Gaussian separation algebraically and independently checked exact transcripts, the 1/40 PSD inequality, and logistic forbidden-band exclusion at n=4,8,12,16. It also replaced a compressed source-membership argument by an explicit Legendre differential-operator construction and checked the weak-edge finite-prefix limit. Destructive checks covered path circularity, official exact-real ties, intervention legality, covariance conditioning, false angular and subset-pseudoinverse identities, repeated encoder eigenvalues, and accessible current literature; no collision survived. UNRESOLVED BOTTLENECK: prove that rational covariance, eigenspace, and projector-norm enclosures implement every decision with polynomial bit precision below a fixed fraction of the public tolerance. EARLY KILL TEST: run the certificate at the logistic null with positive-epsilon alternatives; any finite singleton claim without the public forbidden band contradicts the no-return theorem, while under g0 every sufficiently weak alternative must be excluded by a reached eigenvalue in (0,g0). STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_crl_transcript_betamin_boundary.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: null
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The positive theorem delivers finite-sample recover-or-abstain certification only for linear Gaussian perfect variance resets under known, transcript-defined population bands; it neither extends to the broader smooth-intervention class nor derives those bands from more primitive law conditions."
  - "The logistic converse proves an exact no-return result at one explicit null, but establishes only the necessity of excluding some weak graph-changing alternatives, not necessity of the proposed bands or a quantitative minimax beta-min boundary."
  - "D0.5.G projected paper-score gate: paper_score_ceiling 7.1 < 7.4, so the graded tier 'field' is capped at 'subfield'."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_promised_transcript_certificate.json
  - discovery/solve_thm_separation_family.json
  - discovery/solve_thm_strict_margin_improvement.json
seeds_burned: []
proof_attempt_summary: |
  Discovery derived a sound transcript-local Gaussian recover-or-abstain certificate, a polynomial-bit post-summary realization, an explicit separation family, and a bounded-kernel logistic no-return boundary; the D0.5 mathematics review passed. The package nevertheless missed the field floor because its positive theorem remains confined to a perfect-variance-reset Gaussian subclass with declared bands, while the converse is not a matched quantitative minimax boundary and the implementation is not end-to-end from raw data. No Lean formalization was entered.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 38444500
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 38444500
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# eid_crl_transcript_betamin_boundary / v1 — Downgraded

**Topic.** A query-local beta-min phase boundary for finite-sample interventional causal representation learning. Fix Acarturk et al.'s deterministic population recovery program with a public smallest-label tie rule. For public g0,h0>0, let P_A(g0,h0) contain models whose every positive eigenvalue and nonzero projector comparison on that population transcript is at least g0 and h0, respectively; this is a model promise, never inferred from post-hoc empirical gaps. In the linear Gaussian variance-reset subclass with publicly conditioned observed covariances, construct an honest sequential certificate that returns the exact latent transitive closure and an approximate parent-supported encoder or abstains, with probability at least 1-alpha and polynomial sample dependence on n,kappa,g0^{-1},h0^{-1},log(1/alpha), but no unqueried subset margin. Prove that without a restriction excluding graph-changing weak alternatives, every uniformly alpha-valid randomized sequential procedure returns the correct singleton empty graph at the specified bounded-kernel logistic null with probability at most alpha. Finally, prove that for every n>=4 an explicit uniformly conditioned Gaussian bipartite family has reached gaps at least 1/40 and graph comparisons zero or one across n^2+2n-2 matrix occurrences, while the published all-subset margin is at most 2^(-2n-1) through the unqueried subset {3,4}. Use actual projector geometry, not the source's false printed angular expression. Consumer: add declared-gap certification, abstention/set output, and encoder error bars to the official finite-sample-linear-crl implementation. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Fresh presolve derived ||Rhat_m-R_m||<=40*kappa^4*a from covariance error a, exact rank/projector intervals, transcript induction, and encoder-range error at most 4*sqrt(n)*e/g0. It proved the all-n Gaussian separation algebraically and independently checked exact transcripts, the 1/40 PSD inequality, and logistic forbidden-band exclusion at n=4,8,12,16. It also replaced a compressed source-membership argument by an explicit Legendre differential-operator construction and checked the weak-edge finite-prefix limit. Destructive checks covered path circularity, official exact-real ties, intervention legality, covariance conditioning, false angular and subset-pseudoinverse identities, repeated encoder eigenvalues, and accessible current literature; no collision survived. UNRESOLVED BOTTLENECK: prove that rational covariance, eigenspace, and projector-norm enclosures implement every decision with polynomial bit precision below a fixed fraction of the public tolerance. EARLY KILL TEST: run the certificate at the logistic null with positive-epsilon alternatives; any finite singleton claim without the public forbidden band contradicts the no-return theorem, while under g0 every sufficiently weak alternative must be excluded by a reached eigenvalue in (0,g0). STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_crl_transcript_betamin_boundary.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5 math PASS, but paper_score_ceiling 7.1 < 7.4 capped the sound package at subfield below the field floor; no faithful bounded repair exists.

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

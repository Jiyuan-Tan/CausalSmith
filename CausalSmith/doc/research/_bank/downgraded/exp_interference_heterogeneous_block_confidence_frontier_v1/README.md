---
qid: exp_interference_heterogeneous_block_confidence_frontier
spec: v1
topic: "Sharp confidence length under heterogeneous rare network exposures. Partition n units into known unequal disjoint clique blocks B_l of sizes r_l and assign units independently Bernoulli(1/2). Outcomes are fixed in [-1/2,1/2], interference is confined to blocks, and each unit's target exposures are its whole block All Treat and All Control, each with probability q_l=2^(-r_l). For theta=n^(-1)sum_i[Y_i(a)-Y_i(b)], write w_l=r_l/n, S=sum_l w_l^2/q_l and M=max_l w_l/q_l. Construct a clipped block-specific HT interval with finite-sample length controlled by sqrt(S log(2/alpha))+M log(2/alpha), then prove that every uniformly randomization-valid measurable interval has worst-case expected length at least c min{1,sqrt(S log(1/alpha))) for 0<alpha<=1/4 whenever M sqrt(log(1/alpha))<=c0 sqrt(S). The lower bound must use a heterogeneous block-homogeneous weighted-erasure prior and cover randomized intervals. Recover the parent's equal-block theorem without its extreme-alpha artifact. Outside the no-dominant-block regime, derive a trimmed/water-filling modulus and the correct consistency boundary rather than claiming S alone is necessary. Implement the diagnostic for the R interference package's full-neighborhood exposure map. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolver derived the exact independent categorical block reduction, including mutually exclusive treatment/control reveals, variance at most S/2, increment bound M, and the clipped honest Bernstein interval. Normalized slopes a_l=w_l/(q_l sqrt(S)) satisfy sum q_l a_l^2=1 and sum w_l a_l=sqrt(S); the no-dominant-block condition keeps the proposed least-favourable Bernoulli prior interior. Exact two-block enumeration checked unbiasedness, variance, saturation, and all factors. Literature searches found no matching weighted all-measurable-interval theorem. UNRESOLVED BOTTLENECK: Prove the weighted erasure posterior-spread lemma with universal constants at every conventional alpha, jointly controlling random weighted information, compact-prior boundaries, unrevealed target slope, conditional target fluctuation, and externally randomized intervals; then prove the water-filling characterization outside the Lindeberg regime. EARLY KILL TEST: Establish or refute that lemma for arrays with max_l a_l sqrt(log(1/alpha))->0. Any counterexample with vanishing dominance ratio stops the frontier; failure only of constants tightens c0. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_interference_heterogeneous_block_confidence_frontier.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "The universal all-measurable confidence-length lower bounds remain open: the weighted-erasure posterior-spread and linear capped water-filling converse were not proved; the delivered result instead gives a cubic consistency converse, capped upper bound, and a fixed-family matching rate."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "It does not prove the universal sharp confidence-length frontier: both the linear water-filling converse and the matching no-dominance lower bound remain open, so the general result is not a sharp minimax rate theorem."
  - "The central implication from the outer posterior pieces to two target tails is asserted rather than derived."
  - "Pairwise Hellinger control does not by itself prove the asserted posterior interval missed-mass event."
  - "The central all-procedure confidence-length consistency boundary is not positioned against the accepted-bank closest experiment result exp_snipe_degree_frontier_v1."
  - "The positioning does not give each cited item a relevance sentence: in particular KandirosPipisDaskalakisHarshaw2024 and HarshawMiddletonSavje2021 appear in the bibliography but are absent from the substantive related-work comparison."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - reviews/review_math.json
  - reviews/review_general.json
seeds_burned: []
proof_attempt_summary: |
  The run proved the exact categorical block reduction, sharpened finite and trimmed HT upper bounds, capped-modulus duality, a cubic all-procedure lower bound yielding the exact fixed-confidence consistency boundary, and a matching fixed-alpha rate for the constructed two-scale family. Two attempts at the advertised universal linear lower frontier failed at the same load-bearing posterior-spread step: weighted-Rademacher anti-concentration did not establish the required posterior quantile gap, while the smooth-location route did not control moving-support endpoints or convert Hellinger bounds into posterior interval spread. The surviving package is mathematically sound but incremental; both universal lower obligations remain open.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 55793818
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 55793818
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# exp_interference_heterogeneous_block_confidence_frontier / v1 — Downgraded

**Topic.** Sharp confidence length under heterogeneous rare network exposures. Partition n units into known unequal disjoint clique blocks B_l of sizes r_l and assign units independently Bernoulli(1/2). Outcomes are fixed in [-1/2,1/2], interference is confined to blocks, and each unit's target exposures are its whole block All Treat and All Control, each with probability q_l=2^(-r_l). For theta=n^(-1)sum_i[Y_i(a)-Y_i(b)], write w_l=r_l/n, S=sum_l w_l^2/q_l and M=max_l w_l/q_l. Construct a clipped block-specific HT interval with finite-sample length controlled by sqrt(S log(2/alpha))+M log(2/alpha), then prove that every uniformly randomization-valid measurable interval has worst-case expected length at least c min{1,sqrt(S log(1/alpha))) for 0<alpha<=1/4 whenever M sqrt(log(1/alpha))<=c0 sqrt(S). The lower bound must use a heterogeneous block-homogeneous weighted-erasure prior and cover randomized intervals. Recover the parent's equal-block theorem without its extreme-alpha artifact. Outside the no-dominant-block regime, derive a trimmed/water-filling modulus and the correct consistency boundary rather than claiming S alone is necessary. Implement the diagnostic for the R interference package's full-neighborhood exposure map. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolver derived the exact independent categorical block reduction, including mutually exclusive treatment/control reveals, variance at most S/2, increment bound M, and the clipped honest Bernstein interval. Normalized slopes a_l=w_l/(q_l sqrt(S)) satisfy sum q_l a_l^2=1 and sum w_l a_l=sqrt(S); the no-dominant-block condition keeps the proposed least-favourable Bernoulli prior interior. Exact two-block enumeration checked unbiasedness, variance, saturation, and all factors. Literature searches found no matching weighted all-measurable-interval theorem. UNRESOLVED BOTTLENECK: Prove the weighted erasure posterior-spread lemma with universal constants at every conventional alpha, jointly controlling random weighted information, compact-prior boundaries, unrevealed target slope, conditional target fluctuation, and externally randomized intervals; then prove the water-filling characterization outside the Lindeberg regime. EARLY KILL TEST: Establish or refute that lemma for arrays with max_l a_l sqrt(log(1/alpha))->0. Any counterexample with vanishing dominance ratio stops the frontier; failure only of constants tightens c0. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_interference_heterogeneous_block_confidence_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G delivered tier=incremental below floor=field; projected paper-score ceiling 6.4 < 7.4; salvageable=false.

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

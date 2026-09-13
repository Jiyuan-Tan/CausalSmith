---
qid: stat_dp_cate_uniform_design_nuisance_privacy_frontier
spec: v1
topic: "Revival of banked downgraded parent stat_dp_cate_minimax_v1_holder_central_dp. Determine the incremental central-private minimax price for pointwise CATE on the exact-uniform coupled-nuisance Holder class with q=alpha+beta<gamma, leaving the separate nonprivate risk R_n^NP symbolic. Prove R_n^DP equivalent to max{R_n^NP,rho_n^priv} with an explicit phase diagram, one total private higher-order local estimator with complete all-dataset sensitivity accounting, and a matching positive-design fuzzy causal converse beyond the parent's two-point-TV barrier. Independently verify the presolved candidate rho_n^priv=max{(n epsilon_n)^(-gamma/(gamma+d)),(n^2 epsilon_n)^(-1/(1+d/gamma+d/q))}; do not restore the parent's unsupported (n epsilon)^(-q/(q+d)) formula. Do not duplicate or assume queued stat_cate_uniform_sparse_component_converse, which concerns only R_n^NP. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A fixed-uniform-design projection identity makes local R-moment bias the product of alpha- and beta-projection errors plus gamma-localization bias. Binomial-normalized within-cell pair averages have exact expectation and claimed replacement sensitivity C/(n^2 h^d ell^d), avoiding nuisance pilots and occupancy logarithms. A same-class smooth fuzzy family has singleton cancellation; component maximal couplings and a spanning-tree sum claim Hamming cost C ab n^2 h^d ell^d, leading with adjacent-output DP telescoping to rho_priv=max{(n epsilon)^(-gamma/(gamma+d)),(n^2 epsilon)^(-1/(1+d/gamma+d/(alpha+beta)))}. The d=1, alpha=beta=1/8, gamma=1, epsilon=n^(-2/5) specialization gives matching n^(-4/15) upper and lower scales. UNRESOLVED BOTTLENECK: Below the nuisance elbow when privacy is inactive, replace the known nonprivate upper benchmark by symbolic R_n^NP using an independently verified comparator or a new privacy-transfer lemma; the queued nonprivate result is not assumed. EARLY KILL TEST: Verify the complete d=1 pair-release sensitivity and component-Hamming calculation at h proportional to n^(-4/15), ell proportional to n^(-16/15); stop on a surviving singleton, false factorization, or normalization bias. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_dp_cate_uniform_design_nuisance_privacy_frontier.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "No grounded same-assumption stability transfer proves R_DP <= C max{R_NP,rho_priv} in the below-elbow privacy-inactive regime, while the alternative same-class nonprivate converse was explicitly excluded."
reusable: unknown
reraise_status: retry
gap_reasons:
  - "The promised global symbolic frontier R_n^DP asymp max{R_n^NP,rho_n^priv} is not delivered: this theorem matches only for q >= q_0 or privacy-leading rho_n^priv, leaving the below-elbow privacy-inactive region open."
  - "This open question explicitly retains the missing privacy-transfer/attainment step, so the current artifact supplies a conditional frontier rather than the proposal's claimed full incremental-private-price theorem."
  - "The upper construction also relies essentially on a known exact-uniform design, while the broader bounded-density result is only a transferred lower bound, substantially limiting econometric applicability."
reusable_artifacts:
  - "discovery/core.json — discharged exact-uniform private upper/lower envelopes, complete phase map, and the bounded-density lower-only transfer"
  - "discovery/writeup.tex — auditable one-release estimator, sensitivity ledger, fuzzy Hamming converse, and d=1 worked calibration"
  - "reviews/review_math.json — clean mathematical-review receipt for the delivered conditional results"
  - "orchestrator/decision_log.jsonl — algebra correction, exact release-map repair, maximality audit, and terminal boundary consult"
seeds_burned:
  - index: 0
    one_liner: "seed:full-frontier"
    reason: "The sole proposal angle was exhaustively repaired and reviewed; closing the remaining regime requires a new theorem outside the fixed topic's permitted dependencies."
proof_attempt_summary: |
  The run repaired the presolved phase algebra, made the private release and postprocessing map unique, proved the exact-uniform two-sided bracket and matched privacy-leading regimes, and transferred the privacy lower barriers to a bounded-density superclass. The global symbolic equality collapsed in the below-elbow privacy-inactive regime because scalar nonprivate minimax risk provides no replacement-stability certificate. A future retry needs either a genuine stability-aware oracle privatization theorem or an independent same-class nonprivate nuisance converse; the latter was explicitly excluded from this topic.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 30449179
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 30449179
  total_tokens_consumed: null
banked_on: "2026-09-10"
---

# stat_dp_cate_uniform_design_nuisance_privacy_frontier / v1 — Downgraded

**Topic.** Revival of banked downgraded parent stat_dp_cate_minimax_v1_holder_central_dp. Determine the incremental central-private minimax price for pointwise CATE on the exact-uniform coupled-nuisance Holder class with q=alpha+beta<gamma, leaving the separate nonprivate risk R_n^NP symbolic. Prove R_n^DP equivalent to max{R_n^NP,rho_n^priv} with an explicit phase diagram, one total private higher-order local estimator with complete all-dataset sensitivity accounting, and a matching positive-design fuzzy causal converse beyond the parent's two-point-TV barrier. Independently verify the presolved candidate rho_n^priv=max{(n epsilon_n)^(-gamma/(gamma+d)),(n^2 epsilon_n)^(-1/(1+d/gamma+d/q))}; do not restore the parent's unsupported (n epsilon)^(-q/(q+d)) formula. Do not duplicate or assume queued stat_cate_uniform_sparse_component_converse, which concerns only R_n^NP. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A fixed-uniform-design projection identity makes local R-moment bias the product of alpha- and beta-projection errors plus gamma-localization bias. Binomial-normalized within-cell pair averages have exact expectation and claimed replacement sensitivity C/(n^2 h^d ell^d), avoiding nuisance pilots and occupancy logarithms. A same-class smooth fuzzy family has singleton cancellation; component maximal couplings and a spanning-tree sum claim Hamming cost C ab n^2 h^d ell^d, leading with adjacent-output DP telescoping to rho_priv=max{(n epsilon)^(-gamma/(gamma+d)),(n^2 epsilon)^(-1/(1+d/gamma+d/(alpha+beta)))}. The d=1, alpha=beta=1/8, gamma=1, epsilon=n^(-2/5) specialization gives matching n^(-4/15) upper and lower scales. UNRESOLVED BOTTLENECK: Below the nuisance elbow when privacy is inactive, replace the known nonprivate upper benchmark by symbolic R_n^NP using an independently verified comparator or a new privacy-transfer lemma; the queued nonprivate result is not assumed. EARLY KILL TEST: Verify the complete d=1 pair-release sensitivity and component-Hamming calculation at h proportional to n^(-4/15), ell proportional to n^(-16/15); stop on a surviving singleton, false factorization, or normalization bias. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_dp_cate_uniform_design_nuisance_privacy_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The delivered conditional minimax bracket is mathematically sound, but the promised global symbolic frontier remains open below the nuisance elbow; the general referee scored the honest package 6.8 below the 7.2 field floor.

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

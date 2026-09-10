---
qid: stat_causal_resolution_growingk_frontier
spec: v1
topic: "K1 Define a triangular class for scalar bounded causal features and K<K_n with unique interior quantizers, controlled curvature and margin, nuisance rate r_n, adjacent score variance sigma_{P,K}^2=Var(phi_{rho,K+1}-phi_{rho,K}), and minimum standardized gap min_K [rho(K+1)-rho(K)]/sigma_{P,K}. K2 derive the maximal joint growth region for K_n, standardized gap, curvature, margin, and r_n that permits simultaneous bands and locally honest set-valued profiles, plus the complementary failure boundary. K3 construct a corrected-moment growing-class bootstrap attaining it. K4 prove a matching adjacent-quantization lower bound. Use U uniform on [0,1] and MineThatData as witness and consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: For the uniform law, W(K)=1/(12K^2), rho(K)=1-K^{-2}, fixed-K loss variance is 1/(180K^4), adjacent score deviation is plausibly order K^{-2}, and the standardized gap is therefore order K^{-1}, refuting the raw-gap n^{1/6} heuristic. Cell-center estimation contributes excess risk near 1/(nK), so codebook estimation, nuisance error, and Gaussian approximation determine the frontier. UNRESOLVED BOTTLENECK: Prove uniform codebook stability and bootstrap approximation while tracking standardized gap, margin, and causal-feature remainder. EARLY KILL TEST: Compute adjacent score variance exactly for growing K under the uniform law; pivot if cancellation changes its order or corrected-moment remainder becomes first-order well below the conjectured range."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "No feasible two-sided positive-noise growing-K upper/matching theorem over a primitive observational class with joint curvature, margin, nuisance-rate, and locally honest profile guarantees."
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "The matched width theorem is proved only on the noiseless uniform experiment and its specially constructed finite exponential-tilt family, not on the full causal-quantizer class or under positive outcome noise."
  - "The full-class results are converse-only and require branch-specific localization and nuisance-envelope conditions, so they do not establish the advertised growing-resolution frontier or a feasible all-noise procedure."
  - "What remains is a specialized covariance calculation, local matched experiment, and full-class lower obstruction rather than a flagship characterization."
reusable_artifacts:
  - "discovery/core.json — final structured theorem graph, including exact covariance/width results and the geometric/residual all-noise converse constructions"
  - "discovery/writeup.tex — sound derivations for the noiseless-local feasible matched band, positive-noise packings, and full-class lower transfers"
  - "reviews/review_general.json — final subfield ceiling and the precise missing primitive positive-noise upper/matching theorem"
  - "orchestrator/decision_log.jsonl — adjudication trail for localization, Fano membership, covariance packing, CCK/Tsybakov source repairs, and the exhausted positive-noise repair"
seeds_burned: []
proof_attempt_summary: |
  The run derived exact growing-resolution covariance and standardized-width formulas, a feasible multiplier band matched on a noiseless local experiment, and complementary geometric/residual Fano constructions transferring all-noise lower bounds to the full class. It then attempted the field-level repair through a primitive positive-noise class, explicit nuisance rates, global quantizer localization, fitted-score replacement, and bootstrap validity. That repair collapsed because the high-noise score directions leave a common fixed-radius Hölder class, while smoothing would require a new same-class covariance, containment, basin, learner, and bootstrap theory; the surviving subfield results remain sound.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 114495469
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-02"
---

# stat_causal_resolution_growingk_frontier / v1 — Downgraded

**Topic.** K1 Define a triangular class for scalar bounded causal features and K<K_n with unique interior quantizers, controlled curvature and margin, nuisance rate r_n, adjacent score variance sigma_{P,K}^2=Var(phi_{rho,K+1}-phi_{rho,K}), and minimum standardized gap min_K [rho(K+1)-rho(K)]/sigma_{P,K}. K2 derive the maximal joint growth region for K_n, standardized gap, curvature, margin, and r_n that permits simultaneous bands and locally honest set-valued profiles, plus the complementary failure boundary. K3 construct a corrected-moment growing-class bootstrap attaining it. K4 prove a matching adjacent-quantization lower bound. Use U uniform on [0,1] and MineThatData as witness and consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: For the uniform law, W(K)=1/(12K^2), rho(K)=1-K^{-2}, fixed-K loss variance is 1/(180K^4), adjacent score deviation is plausibly order K^{-2}, and the standardized gap is therefore order K^{-1}, refuting the raw-gap n^{1/6} heuristic. Cell-center estimation contributes excess risk near 1/(nK), so codebook estimation, nuisance error, and Gaussian approximation determine the frontier. UNRESOLVED BOTTLENECK: Prove uniform codebook stability and bootstrap approximation while tracking standardized gap, margin, and causal-feature remainder. EARLY KILL TEST: Compute adjacent score variance exactly for growing K under the uniform law; pivot if cancellation changes its order or corrected-moment remainder becomes first-order well below the conjectured range.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** D0.5 found a sound noiseless-local matched theorem and all-noise converse package, but the promised primitive positive-noise growing-resolution frontier remains unsupported and the final ceiling 6.7 is below the field floor.

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

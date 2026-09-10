---
qid: stat_cot_boundary_degeneracy_frontier
spec: v1
topic: "K1 Fix two randomized treatment-arm samples with a shared covariate marginal, positive smooth densities, and the quadratic conditional-Wasserstein partial-identification endpoint; allow smoothness and the conditional-law discrepancy to drift. K2 derive the sharp joint phase diagram for the intrinsic smoothness elbow and equality/near-equality degeneracy, including a growing-rank Gaussian-quadratic approximation with forced Gaussianization for d>=1 and a separate exact d=0 null quadratic-process law. K3 construct a wavelet second-order or U-statistic estimator and isolate construction of a frontier-width confidence procedure honest across regular, null, local, and critical regimes as the remaining open problem. K4 prove matching high-frequency minimax lower bounds. Use p=1 and q_theta(y,z)=1+theta b(z)cos(2pi y), and the STAR benchmark, as witness and consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: At equality the first derivative of squared conditional W2 vanishes; its second variation is a conditional inverse-elliptic quadratic form. A wavelet estimator is therefore a degenerate quadratic statistic whose effective rank grows with resolution, while local discrepancies restore a first-order term. Existing unconditional smooth-Wasserstein null laws and fixed-entropic Sinkhorn theory do not settle this unregularized conditional frontier. UNRESOLVED BOTTLENECK: Prove a uniform second-order expansion with controlled spectral tails and a calibration honest across null, local, smoothness-critical, and regular regimes. EARLY KILL TEST: For the cosine witness, compute the exact second variation and increasing-resolution null statistic; pivot if it tensorizes verbatim into an existing unconditional quadratic-functional theorem with no conditional calibration obstruction."
novelty_target: flagship
banked_novelty_tier: field
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The proof's split Delta=p+r_z+r_y omits 2a(r_z,r_y) from B^y=a(Delta,Delta)-a(P_y Delta,P_y Delta); equations (16)--(18) do not bound it, so the asserted outcome-gap envelope is not discharged as written."
  - "The d>=1 headline promises a sharp joint frontier, but this theorem expressly delivers only an intrinsic lower frontier plus slower certified upper envelopes; recast the contribution as a bracket or supply a matching upper result."
  - "What is settled therefore supports a field contribution, not a flagship resolution."
reusable_artifacts:
  - "discovery/core.json — typed field-tier bracket, Gram-conjugated inverse-elliptic operator, lower-frontier witnesses, and sealed calibration OEQ"
  - "discovery/writeup.tex — anisotropic wavelet construction, d=0 equality law, and growing-kernel contraction attempt"
  - "discovery/literature_map.md — SmoothCOT, direct-COT, Ji-Lei-Spector, and null-law comparator audit"
  - "reviews/ — exact D0.5 math, rubric, novelty-tier, and terminal receipts"
seeds_burned: []
proof_attempt_summary: |
  The run developed a Gram-corrected anisotropic wavelet/U-statistic program, an intrinsic lower frontier, a separate d=0 equality law, and slower certified SmoothCOT/direct-COT upper envelopes. The flagship sharp-frontier claim collapsed because the observable d>=1 result remained a lower/upper bracket, and the final carrier still omitted the cross-term 2a(r_z,r_y) in the energy-gap proof. A future field-level repair should bound that term and synchronize the bracket framing; a flagship upgrade additionally needs a new matching observable estimator and an honest all-regime calibration theorem.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 139083634
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-02"
---

# stat_cot_boundary_degeneracy_frontier / v1 — Downgraded

**Topic.** K1 Fix two randomized treatment-arm samples with a shared covariate marginal, positive smooth densities, and the quadratic conditional-Wasserstein partial-identification endpoint; allow smoothness and the conditional-law discrepancy to drift. K2 derive the sharp joint phase diagram for the intrinsic smoothness elbow and equality/near-equality degeneracy, including a growing-rank Gaussian-quadratic approximation with forced Gaussianization for d>=1 and a separate exact d=0 null quadratic-process law. K3 construct a wavelet second-order or U-statistic estimator and isolate construction of a frontier-width confidence procedure honest across regular, null, local, and critical regimes as the remaining open problem. K4 prove matching high-frequency minimax lower bounds. Use p=1 and q_theta(y,z)=1+theta b(z)cos(2pi y), and the STAR benchmark, as witness and consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: At equality the first derivative of squared conditional W2 vanishes; its second variation is a conditional inverse-elliptic quadratic form. A wavelet estimator is therefore a degenerate quadratic statistic whose effective rank grows with resolution, while local discrepancies restore a first-order term. Existing unconditional smooth-Wasserstein null laws and fixed-entropic Sinkhorn theory do not settle this unregularized conditional frontier. UNRESOLVED BOTTLENECK: Prove a uniform second-order expansion with controlled spectral tails and a calibration honest across null, local, smoothness-critical, and regular regimes. EARLY KILL TEST: For the cosine witness, compute the exact second variation and increasing-resolution null statistic; pivot if it tensorizes verbatim into an existing unconditional quadratic-functional theorem with no conditional calibration obstruction.

**Novelty target.** flagship

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** What is settled supports a field contribution, not a flagship resolution; current carriers retain the omitted 2a(r_z,r_y) bound and the sharp-frontier versus bracket promise mismatch.

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

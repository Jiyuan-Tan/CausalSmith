---
qid: stat_cot_boundary_degeneracy_frontier
spec: v1
topic: "K1 Fix two randomized treatment-arm samples with a shared covariate marginal, positive smooth densities, and the quadratic conditional-Wasserstein partial-identification endpoint; allow smoothness and the conditional-law discrepancy to drift. K2 derive the intrinsic lower phase frontier and an explicit observable upper phase envelope, yielding a two-sided bracket; derive the population growing-rank Gaussian-quadratic transition for d>=1 and a separate exact d=0 null quadratic-process law. K3 construct the observable Gram, SmoothCOT, and direct-COT upper candidates and leave both d>=1 bracket tightness and a frontier-width confidence procedure honest across regular, null, local, and critical regimes as open problems. K4 prove the intrinsic high-frequency minimax lower bound. Use p=1 and q_theta(y,z)=1+theta b(z)cos(2pi y), and the STAR benchmark, as witness and consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: At equality the first derivative of squared conditional W2 vanishes; its second variation is a conditional inverse-elliptic quadratic form. A wavelet estimator is therefore a degenerate quadratic statistic whose effective rank grows with resolution, while local discrepancies restore a first-order term. Existing unconditional smooth-Wasserstein null laws and fixed-entropic Sinkhorn theory do not settle this unregularized conditional bracket. UNRESOLVED BOTTLENECK: Close the d>=1 observable minimax bracket and prove calibration honest across null, local, smoothness-critical, and regular regimes. EARLY KILL TEST: For the cosine witness, compute the exact second variation and increasing-resolution null statistic; pivot if it tensorizes verbatim into an existing unconditional quadratic-functional theorem with no conditional calibration obstruction."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "For d≥1, the central minimax theorem proves an intrinsic lower frontier but only a strictly slower observable upper envelope, so it does not determine the quadratic-zone rate."
  - "The growing-rank transition applies only to an infeasible population-score, population-kernel statistic, while the load-bearing observable mixed-regime calibration remains open."
  - "The isotropic transfer is likewise an unmatched bracket on a class constructed in the note rather than a resolution of the published SmoothCOT class."
reusable_artifacts:
  - "discovery/core.json — typed intrinsic frontier, observable upper envelope, repaired anisotropic Gram operator, and sealed calibration OEQ"
  - "discovery/writeup.tex — repaired cross-term and variance arguments, population Gaussian–quadratic transition, and exact d=0 branch with projector-dependent centering"
  - "discovery/literature_map.md — SmoothCOT, direct-COT, Ji–Lei–Spector, null-law, and class-transfer audit"
  - "reviews/ — final math/decision PASS receipts and subfield 6.8 novelty boundary"
seeds_burned: []
proof_attempt_summary: |
  The run repaired the anisotropic cross-term proof, the false two-sided linear-variance equivalence,
  the Gateaux-direction domain, and the d=0 projector centering, then proved an honest unmatched bracket
  on both the native class and a fixed-radius positive-isotropic scalar SmoothCOT slice. The d≥1 observable
  upper rates remain polynomially slower than the intrinsic quadratic lower rate, and the population
  Gaussian–quadratic transition does not yield an observable all-regime interval. Reaching field tier now
  requires genuinely new estimator, relative spectral/Hessian, multiplier-coupling, and anti-concentration machinery.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 185344905
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-03"
---

# stat_cot_boundary_degeneracy_frontier / v1 — Downgraded

**Topic.** K1 Fix two randomized treatment-arm samples with a shared covariate marginal, positive smooth densities, and the quadratic conditional-Wasserstein partial-identification endpoint; allow smoothness and the conditional-law discrepancy to drift. K2 derive the intrinsic lower phase frontier and an explicit observable upper phase envelope, yielding a two-sided bracket; derive the population growing-rank Gaussian-quadratic transition for d>=1 and a separate exact d=0 null quadratic-process law. K3 construct the observable Gram, SmoothCOT, and direct-COT upper candidates and leave both d>=1 bracket tightness and a frontier-width confidence procedure honest across regular, null, local, and critical regimes as open problems. K4 prove the intrinsic high-frequency minimax lower bound. Use p=1 and q_theta(y,z)=1+theta b(z)cos(2pi y), and the STAR benchmark, as witness and consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: At equality the first derivative of squared conditional W2 vanishes; its second variation is a conditional inverse-elliptic quadratic form. A wavelet estimator is therefore a degenerate quadratic statistic whose effective rank grows with resolution, while local discrepancies restore a first-order term. Existing unconditional smooth-Wasserstein null laws and fixed-entropic Sinkhorn theory do not settle this unregularized conditional bracket. UNRESOLVED BOTTLENECK: Close the d>=1 observable minimax bracket and prove calibration honest across null, local, smoothness-critical, and regular regimes. EARLY KILL TEST: For the cosine witness, compute the exact second variation and increasing-resolution null statistic; pivot if it tensorizes verbatim into an existing unconditional quadratic-functional theorem with no conditional calibration obstruction.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** Final D0.5 math and decision reviews pass, but the sound unmatched conditional frontier and calibration result scores subfield 6.8 below the field cutoff 7 after both reroutes.

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

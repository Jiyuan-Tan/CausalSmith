---
qid: stat_blind_replicate_adrf_protectedcontrast_frontier
spec: v1
topic: "Protected-contrast minimax simultaneous bands for a blind-replicate ADRF. Prove the matching expected-maximal-width statistical frontier using continuous integrated probability and signed marked-channel contrasts on a moment-derived protected frequency square, quantitative analytic continuation and Sobolev quotient recovery, measurable extrema over the theoretical exact compact continuous-channel profile, and a fixed-density, fixed-error Bernoulli marked converse. The band is an existence-level exact-profile procedure: no terminating finite cover or finitely checkable o(r_n) endpoint enclosure is proved, and effective finite-profile certification remains an explicit open computational question. This revives banked parent eid_blind_replicate_adrf_honest_supband_blind_cfzero_adrf_band with a different mathematical handle; the refuted empirical-grid/Jackson inverse and any oracle-dependent finite-witness construction are forbidden."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: "The exact-profile upper/inverse route may be sound, but the advertised matching minimax lower bound is not delivered: the Lean packet is scaled by an extra factor k, its error predicate does not imply the required nonaligned-zero lower envelope, and the central chi-square bridge remains unproved."
reusable: solver_blocked
reraise_status: true-negative
gap_reasons:
  - "The requested generic theorem is inconsistent with its admissibility assumptions. Compact support, pointwise domination, and increasing moment cancellation do not uniformly control the weighted output norm by its unweighted Fourier energy."
  - "The current Lean packet is not the frozen paper packet at the required scaling: JacobiPacket.lean:55-60 defines the unnormalized w*K_k packet with multiplier k^(1/2-β), while the frozen paper after equation (55) specifies h_k = k^(-β-1/2) * tilde h_k."
  - "The current predicate permits common zeros, so the strictly positive lower envelope required by equation (58), hence the RN/chi-square bridge, is not derivable."
reusable_artifacts:
  - discovery/writeup.tex
  - discovery/core.json
  - formalization/plan.json
  - orchestrator/decision_log.jsonl
  - logs/stages/_f2-5__unified-faithfulness-reviewer.log
seeds_burned: []
proof_attempt_summary: |
  Discovery proved a field-tier exact-profile upper/inverse route and proposed a fixed-nuisance
  Jacobi/sinc-fourth lower packet. Three scaffold-faithfulness repairs aligned the existential laws,
  measure-level error witnesses, and packet mode range, after which F3 and a four-round substrate
  study attacked the weighted Plancherel/Radon–Nikodym χ² bridge. The generic bridge was refuted by a
  derivative-bump family, while the frozen packet still has a factor-k scaling mismatch and lacks
  the Jacobi, sinc-envelope, Fourier, and RN formalization needed for the matching lower bound.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 110723961
  pipeline_claude_tokens: 5219990
  pipeline_tokens_consumed: 115943951
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# stat_blind_replicate_adrf_protectedcontrast_frontier / v1 — Failed

**Topic.** Protected-contrast minimax simultaneous bands for a blind-replicate ADRF. Prove the matching expected-maximal-width statistical frontier using continuous integrated probability and signed marked-channel contrasts on a moment-derived protected frequency square, quantitative analytic continuation and Sobolev quotient recovery, measurable extrema over the theoretical exact compact continuous-channel profile, and a fixed-density, fixed-error Bernoulli marked converse. The band is an existence-level exact-profile procedure: no terminating finite cover or finitely checkable o(r_n) endpoint enclosure is proved, and effective finite-profile certification remains an explicit open computational question. This revives banked parent eid_blind_replicate_adrf_honest_supband_blind_cfzero_adrf_band with a different mathematical handle; the refuted empirical-grid/Jackson inverse and any oracle-dependent finite-witness construction are forbidden.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** substrate-unbuildable: the generic weighted Plancherel bridge is false under its stated assumptions, and the frozen packet's factor-k normalization mismatch plus missing Jacobi/sinc/Fourier/RN chain blocks the matching lower bound.

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

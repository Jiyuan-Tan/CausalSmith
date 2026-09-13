---
qid: panel_staggered_nuclear_radius
spec: v1
topic: "Matched honest nuclear-radius frontier for staggered low-rank panels under iid noise: under fixed deterministic adoption, known fixed rank, iid Gaussian cell errors, normalized strong-factor/incoherence bounds, and quantitative overlap Grams, define the minimax expected observable nuclear-error radius over all uniformly honest procedures. Characterize it up to constants with a polynomial-time wedge-aware spectral certificate and a same-class all-procedure lower bound; keep the exact rate answer-open. Derive only a coverage-valid diffuse-weight ATT corollary by nuclear/operator duality. PRESOLVE EVIDENCE REQUIRING VERIFICATION: the exact block identity Gamma_IQ=Gamma_IP Gamma_CP^dagger Gamma_CQ and balanced rank-one analysis suggest scale sigma sqrt(n), far below diameter n. UNRESOLVED BOTTLENECK: matching tangent packing for every admissible wedge. EARLY KILL TEST: matching sigma_+ sqrt(n) bounds for the balanced rank-one L-mask."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "tier_genuinely_below"
reusable: unknown
reraise_status: unknown
gap_reasons:
  - "The matched result is confined to a balanced square panel, rank one, one missing quadrant, and fixed interior incoherence; the general staggered multi-chart frontier and shrinking-incoherence regime remain open, so the note does not deliver a frontier for staggered low-rank panels broadly."
  - "The displayed Taylor audit treats the core pseudoinverse as an ordinary inverse on fixed rank-one spaces; for Π_1(B)^† it omits the subspace/projection-curvature remainder from DΠ_1 and the corresponding Moore--Penrose projector terms, so the asserted C_0τ_n^2(δ̂_n^{-1}+M̂_nδ̂_n^{-2}+M̂_n^2δ̂_n^{-3}) bound is not reproduced."
  - "The ATT proposition transfers coverage by norm duality but supplies neither an optimal-length result nor evidence that the resulting interval is practically competitive."
reusable_artifacts:
  - "discovery/solve_thm_balanced_frontier.json — balanced rank-one interior packing and σ√n frontier attempt"
  - "discovery/solve_thm_boundary_frontier_obstruction.json — μ=1 boundary phase and σ/zero-radius elbow"
  - "discovery/solve_thm_general_wedge_boundary_obstruction.json — superseded general-wedge obstruction work"
  - "discovery/core.json — final model, comparator map, open questions, and accepted metadata repairs"
seeds_burned: []
proof_attempt_summary: |
  The run derived a balanced rank-one, one-missing-quadrant interior frontier of order σ√n and a sharp μ=1 boundary phase, then attempted to lift the construction to an observable wedge-aware certificate. The field-level program collapsed because the genuine multi-chart synchronization and matching packing remained open, while the balanced WSVD upper proof still omitted singular-subspace and Moore--Penrose curvature terms. A future run should reuse the endpoint packings and boundary geometry but independently rebuild the transport perturbation argument before claiming honesty.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 55840886
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 55840886
  total_tokens_consumed: null
banked_on: "2026-09-12"
---

# panel_staggered_nuclear_radius / v1 — Downgraded

**Topic.** Matched honest nuclear-radius frontier for staggered low-rank panels under iid noise: under fixed deterministic adoption, known fixed rank, iid Gaussian cell errors, normalized strong-factor/incoherence bounds, and quantitative overlap Grams, define the minimax expected observable nuclear-error radius over all uniformly honest procedures. Characterize it up to constants with a polynomial-time wedge-aware spectral certificate and a same-class all-procedure lower bound; keep the exact rate answer-open. Derive only a coverage-valid diffuse-weight ATT corollary by nuclear/operator duality. PRESOLVE EVIDENCE REQUIRING VERIFICATION: the exact block identity Gamma_IQ=Gamma_IP Gamma_CP^dagger Gamma_CQ and balanced rank-one analysis suggest scale sigma sqrt(n), far below diameter n. UNRESOLVED BOTTLENECK: matching tangent packing for every admissible wedge. EARLY KILL TEST: matching sigma_+ sqrt(n) bounds for the balanced rank-one L-mask.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5 score gate capped the balanced rank-one one-quadrant result at incremental (paper-score ceiling 5.6), below the field floor; a genuine multi-chart matched frontier is an unbounded new program, and the WSVD Taylor-curvature proof remains unestablished.

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

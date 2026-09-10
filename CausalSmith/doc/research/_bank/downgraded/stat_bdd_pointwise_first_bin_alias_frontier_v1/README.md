---
qid: stat_bdd_pointwise_first_bin_alias_frontier
spec: v1
topic: "PRESOLVE EVIDENCE REQUIRING VERIFICATION: At one fixed smooth boundary point b, observe iid units from a uniform two-sided half-disc with Bernoulli outcomes whose side means lie in [1/4,3/4] and are L-Lipschitz, but retain only treatment side and radial point-distance Q_Delta(R)=Delta floor(R/Delta), not angle or raw coordinates. Target tau(b). Prove minimax absolute-error and honest expected-length order max{n^(-1/4),Delta}, with squared risk of the corresponding squared order, uniformly across Delta, using a bin-aware local estimator with explicit Lipschitz bias. The lower seed is exact: on the treated first bin set phi(u)=(1-u)(1-2u), u=R/Delta; half-disc radial density is proportional to u and integral_0^1 u phi(u)du=0, so a Bernoulli-mean perturbation c Delta phi gives the same rounded-bin law while changing the boundary limit by c Delta and retaining bounded derivative. The rd2d.distance R, Python, and Stata workflow and its Ser Pilo Paga replication are the consumer. UNRESOLVED BOTTLENECK: Prove a same-class lower combining sampling and aliasing rather than merely maximizing separate bounds, construct total honest intervals for all Delta regimes, and state exactly what coordinate coarsening the analyst observes. EARLY KILL TEST: Drop if Dong-Kolesar or discrete-running-variable RD already yields this 2D radial-compression point-BATEC frontier, if the weighted integral identity or Bernoulli-mixture equality fails, or if raw coordinates remain available."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REVISE
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  - "The exact release-law-specific endpoint characterization remains open."
  - "Without endpoint attainability or a sharp diameter constant, the honestly positioned PartialID contribution is subfield rather than field tier (paper-score ceiling 7.2)."
  - "The Cattaneo–Titiunik–Yu exact-distance class does not contain this rounded-release experiment, so its results cannot supply the missing lift."
reusable_artifacts:
  - discovery/proto_core.json
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/proof_archive/
  - reviews/review_math.json
  - reviews/review_general.json
seeds_burned: []
proof_attempt_summary: |
  Discovery proved the release-fiber diameter bounds 2 c_L Δ ≤ ω_Δ ≤ 4 L Δ,
  a computable certified outer interval, the joint sampling/alias minimax frontier,
  and matching honest expected-length results; the math and decision reviews pass,
  and the Hoeffding leaf is cited, verified, and attested. The field-tier attempt
  collapsed only on novelty: exact per-Q endpoints, endpoint attainability, and the
  sharp maximal-diameter constant remain unproved and require new mathematics.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 113148197
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-04"
---

# stat_bdd_pointwise_first_bin_alias_frontier / v1 — Downgraded

**Topic.** PRESOLVE EVIDENCE REQUIRING VERIFICATION: At one fixed smooth boundary point b, observe iid units from a uniform two-sided half-disc with Bernoulli outcomes whose side means lie in [1/4,3/4] and are L-Lipschitz, but retain only treatment side and radial point-distance Q_Delta(R)=Delta floor(R/Delta), not angle or raw coordinates. Target tau(b). Prove minimax absolute-error and honest expected-length order max{n^(-1/4),Delta}, with squared risk of the corresponding squared order, uniformly across Delta, using a bin-aware local estimator with explicit Lipschitz bias. The lower seed is exact: on the treated first bin set phi(u)=(1-u)(1-2u), u=R/Delta; half-disc radial density is proportional to u and integral_0^1 u phi(u)du=0, so a Bernoulli-mean perturbation c Delta phi gives the same rounded-bin law while changing the boundary limit by c Delta and retaining bounded derivative. The rd2d.distance R, Python, and Stata workflow and its Ser Pilo Paga replication are the consumer. UNRESOLVED BOTTLENECK: Prove a same-class lower combining sampling and aliasing rather than merely maximizing separate bounds, construct total honest intervals for all Delta regimes, and state exactly what coordinate coarsening the analyst observes. EARLY KILL TEST: Drop if Dong-Kolesar or discrete-running-variable RD already yields this 2D radial-compression point-BATEC frontier, if the weighted integral identity or Bernoulli-mixture equality fails, or if raw coordinates remain available.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REVISE

**Banking reason.** Cold general review: publishability_tier=subfield, meets_floor=false, paper_score_ceiling=7.2; exact per-Q endpoints and attainability remain open.

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

---
qid: panel_dsc_jump_energy_phase
spec: v1
topic: "Under an exact stable quantile-span distributional synthetic-control model with fixed donor and period counts, smooth pre-period laws with a uniformly strong sum-zero Gram, simplex-constrained weight estimation from n observations per pre cell, and finite-support post-period laws estimated from m independent observations per cell, derive the exact separately anchored signed endpoint energy for discrete quantile errors and the constrained-Gaussian pre-weight quadratic. Prove the joint expansion and its three n/sqrt(m) phase laws, including local m^(-1/2) knot offsets, n^(-1/2) simplex-face offsets, cross-term control, and necessary-and-sufficient component degeneracy conditions. Construct feasible simultaneous L2 QTE confidence balls with uniform coverage and diameter order n^(-1/2)+m^(-1/4), oracle calibration only on separated regular strata, and a certified conditional minimax common-cutoff calculation near collisions/faces. Prove the unavoidable honesty penalty rather than claiming oracle adaptation. The same-question consumer is Zhai et al.'s discrete mosquito-abundance distributional synthetic-control analysis, excluding its separate binary CDF/W1 estimator. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Separately anchored endpoint algebra, tangent-cone weight limits, cross-term bounds and all three phases are derived; within-cell local offsets are asymptotically observed while cross-cell translations and face offsets remain nuisance; a one-dimensional Bernoulli calculation certifies the least stable 95% squared-radius cutoff in (1.913,1.914], versus collision oracle 1.385903824, and finite-sample DKW balls attain the target diameter order. UNRESOLVED BOTTLENECK: Prove one measurable certified nuisance-region/cluster procedure attains the conditional local minimax cutoff while retaining uniform coverage across changing supports, covariance ranks and simplex faces, with oracle calibration on separated regular strata. EARLY KILL TEST: Solve the specified two-donor Gaussian calibration problem with a weight at h/sqrt(n), bounded face/cross-cell knot offsets, and certified probability enclosures; add a within-cell mass of order m^(-1/2) and require the procedure to learn its internal offset, retain coverage, and converge to the conditional cutoff with vanishing fallback probability. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/panel_dsc_jump_energy_phase.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The proposal's all-strata measurable attainment claim remains an explicit open question: the delivered pilot-split result attains the conditional cutoff only on bounded-or-pilot-resolvable strata, a strict weakening."
  - "This diagonal impossibility is architecture-free and already defeats cutoff convergence before uniform coverage is imposed."
  - "The contradiction permits arbitrary raw-sample measurable, full-sample, cross-fitted, multiscale, observation-dependent, and independently randomized radii, and arises before imposing uniform coverage."
reusable_artifacts:
  - "discovery/core.json — strongest sound graph: exact endpoint decomposition, three phase laws, global honest rate-optimal ball, pilot-resolvable cutoff theorem, and explicit open all-strata question."
  - "discovery/writeup.tex — derivations for the pulse-sharp cross-term order, Bernoulli cutoff bracket, and pilot-resolution obstruction."
  - "orchestrator/decision_log.jsonl — full PR adjudications and the architecture-free fixed-h/slow-diagonal counterexample."
  - "reviews/ — D-1 and D0.5 novelty, soundness, and kernel-substitution receipts."
seeds_burned: []
proof_attempt_summary: |
  The run proved the finite-array six-term endpoint-loss decomposition, all three two-sample phase laws, a globally honest rate-optimal confidence ball, an exact Bernoulli honesty penalty, and conditional-cutoff convergence on quantitatively pilot-resolvable regimes. Attempts to upgrade this to the promised all-array feasible sharp calibration collapsed: fixed local Bernoulli experiments are contiguous to collision, while a slowly diverging diagonal is macro-separated, forcing incompatible cutoff limits. The sound subfield-level mathematics remains reusable, but the field-level all-array attainment kernel is false under the unchanged model.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 53087737
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-08"
---

# panel_dsc_jump_energy_phase / v1 — Failed

**Topic.** Under an exact stable quantile-span distributional synthetic-control model with fixed donor and period counts, smooth pre-period laws with a uniformly strong sum-zero Gram, simplex-constrained weight estimation from n observations per pre cell, and finite-support post-period laws estimated from m independent observations per cell, derive the exact separately anchored signed endpoint energy for discrete quantile errors and the constrained-Gaussian pre-weight quadratic. Prove the joint expansion and its three n/sqrt(m) phase laws, including local m^(-1/2) knot offsets, n^(-1/2) simplex-face offsets, cross-term control, and necessary-and-sufficient component degeneracy conditions. Construct feasible simultaneous L2 QTE confidence balls with uniform coverage and diameter order n^(-1/2)+m^(-1/4), oracle calibration only on separated regular strata, and a certified conditional minimax common-cutoff calculation near collisions/faces. Prove the unavoidable honesty penalty rather than claiming oracle adaptation. The same-question consumer is Zhai et al.'s discrete mosquito-abundance distributional synthetic-control analysis, excluding its separate binary CDF/W1 estimator. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Separately anchored endpoint algebra, tangent-cone weight limits, cross-term bounds and all three phases are derived; within-cell local offsets are asymptotically observed while cross-cell translations and face offsets remain nuisance; a one-dimensional Bernoulli calculation certifies the least stable 95% squared-radius cutoff in (1.913,1.914], versus collision oracle 1.385903824, and finite-sample DKW balls attain the target diameter order. UNRESOLVED BOTTLENECK: Prove one measurable certified nuisance-region/cluster procedure attains the conditional local minimax cutoff while retaining uniform coverage across changing supports, covariance ranks and simplex faces, with oracle calibration on separated regular strata. EARLY KILL TEST: Solve the specified two-donor Gaussian calibration problem with a weight at h/sqrt(n), bounded face/cross-cell knot offsets, and certified probability enclosures; add a within-cell mass of order m^(-1/2) and require the procedure to learn its internal offset, retain coverage, and converge to the conditional cutoff with vanishing fallback probability. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/panel_dsc_jump_energy_phase.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** terminal:laundering confirmed by independent validity gate: a legal Bernoulli contiguity diagonal makes the requested all-array conditional-minimax cutoff attainment impossible; the strongest sound result only covers pilot-resolvable regimes.

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

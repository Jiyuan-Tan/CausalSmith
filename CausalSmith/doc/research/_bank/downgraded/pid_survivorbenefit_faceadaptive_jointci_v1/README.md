---
qid: pid_survivorbenefit_faceadaptive_jointci
spec: v1
topic: "Support-adaptive uniform joint inference for the accepted survivor-complier sharp benefit interval. Keep the accepted parent's finite-X, finite-ordered-Y binary-IV model and exact endpoint map Phi=(L,U), assume only instrument overlap and aggregate survivor mass M>=m_*>0, and allow individual survivor cells and threshold gaps to vanish arbitrarily. Construct the explicit nearby-legal-base directional envelope T_n and its common-Gaussian max-norm rectangle C_n. Prove uniform joint 1-alpha coverage over all triangular arrays, exact oracle Gaussian calibration on separated regular faces, and O_P(n^-1/2) width along root-n emerging-support and tied-cut arrays. The hard kernel is the legal observed-law inner-neighborhood comparison and relative critical-value transfer when endpoint variance vanishes; pointwise bootstrap validity, endpoint-wise Bonferroni, or the parent's deterministic guard cannot substitute. PRESOLVE EVIDENCE REQUIRING VERIFICATION: the presolve derived the finite unconditional-capacity reduction, regular-face oracle calibration, uniformly tight critical values, and a multinomial Gaussian coupling. It verified a legal K=4 two-cell array with upper cuts (.40,.30,.30,.40), M_n=.25+.25/sqrt(n), exact upper endpoint (.8+.4/sqrt(n))/(1+1/sqrt(n)), and centered limit N(0,1.28); a Poisson rare-outcome counterexample attempt was conservatively covered by endogenous nearby-base padding. These calculations separate root-n deterministic drift from sampling fluctuation and correctly type projection on contrast masses rather than atom vectors. UNRESOLVED BOTTLENECK: prove the deterministic inner-neighborhood comparison LC, especially legal-law realization of capacity derivative domination and relative quantile validity when the envelope scale vanishes. EARLY KILL TEST: certify legal-face maximization on K=4 two-cell arrays combining root-n survivor emergence, lambda/n rare atoms, simultaneous ties, and a degenerate endpoint limit for a_n=n^-1/3 and n^-0.49; a controlled coverage deficit or persistent legal-versus-ambient mismatch stops the run. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_survivorbenefit_faceadaptive_jointci.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The proposed all-array uniform joint-coverage theorem was removed; only regular-face calibration, width without global validity, a diagnostic, and a singleton-ray obstruction/repair were delivered."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The advertised support-adaptive uniform joint-inference problem is not settled: the note proves coverage only at fixed separated regular faces and for one engineered K=4 array, while uniform coverage over arbitrary changing-support and tied-face arrays remains the open question oeq:legal-relative-comparison."
  - "The uniform root-n width theorem supplies no inferential validity by itself, and the singleton-cell oriented construction establishes domination only along one ray on one face."
  - "The main novel delivered result is therefore a narrow counterexample to an even symmetric-probe proof strategy, accompanied by a face-specific repair, rather than a usable confidence procedure for the maintained class."
reusable_artifacts:
  - "discovery/core.json — final theorem graph, including the proved obstruction proposition and the explicitly open global legal-relative comparison."
  - "discovery/writeup.tex — sound derivation note for finite-capacity geometry, regular-face calibration, width, the K=4 diagnostic, and the symmetric-probe obstruction."
  - "discovery/solve_lem_finite_legal_probe.json — explicit legal counterexample that refutes the symmetric-probe route."
  - "discovery/solve_oeq_legal_relative_comparison.json — surviving oriented singleton-ray construction and the exact unresolved global obligation."
seeds_burned:
  - index: 0
    one_liner: "legal-inner-neighborhood-envelope"
    reason: "The symmetric legal-probe route was refuted by an explicit legal counterexample, and the distinct oriented route did not establish the global simultaneous-face comparison, covariance traction, relative vanishing-scale quantile transfer, or zero-scale branch."
  - index: 1
    one_liner: "common-gaussian-support-adaptive-rectangle"
    reason: "The symmetric legal-probe route was refuted by an explicit legal counterexample, and the distinct oriented route did not establish the global simultaneous-face comparison, covariance traction, relative vanishing-scale quantile transfer, or zero-scale branch."
  - index: 2
    one_liner: "relative-quantile-transfer-at-collapsing-scale"
    reason: "The symmetric legal-probe route was refuted by an explicit legal counterexample, and the distinct oriented route did not establish the global simultaneous-face comparison, covariance traction, relative vanishing-scale quantile transfer, or zero-scale branch."
proof_attempt_summary: |
  Stage D proved the finite-capacity geometry, measurable endpoint machinery, separated regular-face calibration, root-n width, and a certified K=4 diagnostic. A symmetric nearby-legal-probe argument was refuted by an explicit legal counterexample; a genuinely distinct oriented positive-part construction repaired one singleton ray but did not establish simultaneous-face domination, covariance traction, relative vanishing-scale quantile transfer, or the exact-zero-scale branch. The all-array coverage theorem was therefore removed, the global comparison retained as an open question, and the sound surviving package was graded incremental rather than field.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 29887314
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 29887314
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# pid_survivorbenefit_faceadaptive_jointci / v1 — Downgraded

**Topic.** Support-adaptive uniform joint inference for the accepted survivor-complier sharp benefit interval. Keep the accepted parent's finite-X, finite-ordered-Y binary-IV model and exact endpoint map Phi=(L,U), assume only instrument overlap and aggregate survivor mass M>=m_*>0, and allow individual survivor cells and threshold gaps to vanish arbitrarily. Construct the explicit nearby-legal-base directional envelope T_n and its common-Gaussian max-norm rectangle C_n. Prove uniform joint 1-alpha coverage over all triangular arrays, exact oracle Gaussian calibration on separated regular faces, and O_P(n^-1/2) width along root-n emerging-support and tied-cut arrays. The hard kernel is the legal observed-law inner-neighborhood comparison and relative critical-value transfer when endpoint variance vanishes; pointwise bootstrap validity, endpoint-wise Bonferroni, or the parent's deterministic guard cannot substitute. PRESOLVE EVIDENCE REQUIRING VERIFICATION: the presolve derived the finite unconditional-capacity reduction, regular-face oracle calibration, uniformly tight critical values, and a multinomial Gaussian coupling. It verified a legal K=4 two-cell array with upper cuts (.40,.30,.30,.40), M_n=.25+.25/sqrt(n), exact upper endpoint (.8+.4/sqrt(n))/(1+1/sqrt(n)), and centered limit N(0,1.28); a Poisson rare-outcome counterexample attempt was conservatively covered by endogenous nearby-base padding. These calculations separate root-n deterministic drift from sampling fluctuation and correctly type projection on contrast masses rather than atom vectors. UNRESOLVED BOTTLENECK: prove the deterministic inner-neighborhood comparison LC, especially legal-law realization of capacity derivative domination and relative quantile validity when the envelope scale vanishes. EARLY KILL TEST: certify legal-face maximization on K=4 two-cell arrays combining root-n survivor emergence, lambda/n rare atoms, simultaneous ties, and a degenerate endpoint limit for a_n=n^-1/3 and n^-0.49; a controlled coverage deficit or persistent legal-versus-ambient mismatch stops the run. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_survivorbenefit_faceadaptive_jointci.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The advertised support-adaptive uniform joint-inference problem is not settled: uniform coverage over arbitrary changing-support and tied-face arrays remains open; the cold tier is incremental with paper_score_ceiling 4.6 below the field floor.

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

---
qid: stat_adaptive_mask_vc_rowwise_frontier
spec: v1
topic: "K1 prove recorded-propensity IPW–SVD has normalized maximum-row loss O_P(a^{loose}_{nm}) on the frozen predictable effect-only low-rank class, and prove by a same-class endogenous-target construction that uniform O_P(b_{nm}) attainment by this estimator is false. K2 prove the same-loss observed-data minimax bracket c b_{nm} ≤ R*_{nm} ≤ C(1 ∧ a^{loose}_{nm}), leaving the rate between these endpoints open. K3 prove blind causal loss and observed blind-versus-recorded disagreement resolve total drift only up to O_P(d_{nm}), retain the 0.25/0.75 Markov failure witness, and make no b_{nm}-scale iff claim. K4 retain direct finite-sample simultaneous bands with the separate sqrt(log |G_n|) multiplicity cost and no multiplier-exactness claim."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The proposed matched b_nm IPW-SVD frontier is false on the frozen class. The banked result retains a sound b_nm-to-constant minimax bracket, estimator-specific IPW failure, d_nm blind resolution, Markov witness, and conservative simultaneous bands, but does not close the estimator-independent minimax rate."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The proposed matched b_nm IPW--SVD frontier is replaced by a loose a^{loose}_{nm} bound and an open minimax bracket; retain and position this as the weaker delivered kernel, not as the promised frontier."
  - "The central theorem proves only c b_nm <= R*_nm <= C(1 wedge a^{loose}_{nm}), and under the fixed-complexity subregime the upper endpoint is nonshrinking."
reusable_artifacts:
  - "discovery/solve_prop_adaptive_endogenous_target_obstruction.json — same-class counterexample to uniform b_nm attainment by recorded IPW--SVD"
  - "discovery/solve_prop_fixed_complexity_resolution_gap.json — bounded-outcome signal ceiling and nonshrinking-resolution calculation"
  - "discovery/core.json — deterministic sine-frame hybrid and the sound b_nm-to-constant minimax bracket"
  - "discovery/writeup.tex — literature/anchor separation, Markov witness, blind-resolution result, and simultaneous-band derivations"
seeds_burned:
  - index: 0
    one_liner: "Joint predictable-mask IPW-SVD rate, blind-drift equivalence, and simultaneous-query frontier"
    reason: "The sole predictable-mask angle was maximized through seven D0 solve rounds, an endogenous-target counterexample, a deterministic sine-frame hybrid, and anchor audits; the remaining minimax gap has no concrete same-assumption construction."
proof_attempt_summary: |
  The run pursued a martingale-sharp IPW--SVD upper bound, matching constant-propensity minimax converse, blind-drift equivalence, and simultaneous bands under predictable masks. A same-class endogenous-target construction refuted uniform b_nm attainment by recorded IPW--SVD; matrix-Freedman arguments yielded only a_loose_nm, while a deterministic sine-frame hybrid reduced the minimax upper endpoint to C(1 wedge a_loose_nm). The estimator-independent rate between c b_nm and that constant endpoint remains open, and standard shrinking routes would require exogeneity or singular-factor predictability absent from the frozen class.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 108188424
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 108188424
  total_tokens_consumed: null
banked_on: "2026-09-08"
---

# stat_adaptive_mask_vc_rowwise_frontier / v1 — Downgraded

**Topic.** K1 prove recorded-propensity IPW–SVD has normalized maximum-row loss O_P(a^{loose}_{nm}) on the frozen predictable effect-only low-rank class, and prove by a same-class endogenous-target construction that uniform O_P(b_{nm}) attainment by this estimator is false. K2 prove the same-loss observed-data minimax bracket c b_{nm} ≤ R*_{nm} ≤ C(1 ∧ a^{loose}_{nm}), leaving the rate between these endpoints open. K3 prove blind causal loss and observed blind-versus-recorded disagreement resolve total drift only up to O_P(d_{nm}), retain the 0.25/0.75 Markov failure witness, and make no b_{nm}-scale iff claim. K4 retain direct finite-sample simultaneous bands with the separate sqrt(log |G_n|) multiplicity cost and no multiplier-exactness claim.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The central theorem proves only c b_nm <= R*_nm <= C(1 wedge a_loose_nm); the fixed-complexity upper endpoint is nonshrinking, so the achieved tier is subfield below the field floor.

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

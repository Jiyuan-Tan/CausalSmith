---
qid: stat_unknowncutoff_weaklate_frontier
spec: v1
topic: "Honest fuzzy-RD inference when the compliance jump and its unknown location vanish together PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolve derives the known-cutoff honest-length order min(1,n^(-s/(2s+1))/kappa) and constructs legal smooth latent monotone causal mixtures over disjoint cutoff locations. Exact full-joint likelihood calculations yield a nonshrinking unknown-cutoff lower bound when n*kappa^(2+1/s)=o(log(1/kappa)), including sequences on which known-cutoff intervals shrink. A second construction assigns all response types the same smoothly varying potential-outcome table, making outcomes conditionally identical across alternatives: outcome-assisted localization cannot remove the worst-case barrier. A four-sample coarse scan, flank regression, local cutoff classifier, and fixed-center moment inversion provide a detailed strong-signal upper-bound architecture. The closest fixed-jump, known-cutoff weak-IV, and derivative-location sources were checked; no same-object collision was found in the bounded search. These results do not prove the full frontier.\nUNRESOLVED BOTTLENECK: Derive and explicitly evaluate the matched fixed-alpha connected-interval length inside n*kappa^(2+1/s) comparable to log(1/kappa), using sharp compensation profiles, truncated location mixtures, and effect-label testing; finish the strong-upper constants and maximal inequality.\nEARLY KILL TEST: Solve the s=1 common-outcome plateau experiment through its critical window and compare the compensation profile with a finite-grid latent Lipschitz optimization. Do not replace the full kernel with separated regimes or coverage-only inversion.\nSTRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/mill/scratch/mill-w10/presolve_stat_unknowncutoff_weaklate_frontier.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "tier_genuinely_below"
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The delivered result is not the full advertised smoothness-indexed frontier: it proves the known-cutoff benchmark, a one-sided nonshrinking lower threshold for all stated smoothness levels, and oracle-order achievability only on the Lipschitz face under strong signal."
  - "For s>1, the note proves only that one frozen profile localizer fails, not that the proposed rate is attainable or minimax."
  - "In Theorem 3's expected-length argument, equation (18), derived on the event that the cutoff error is at most R_c, is later invoked on the larger event that the error is at most b/8; an explicit recalculation is needed to justify the asserted containment of the denominator-fallback event."
reusable_artifacts:
  - "discovery/core.json — versioned dependency graph for the known-cutoff benchmark, location-mixture barrier, Lipschitz-face upper result, and smooth-profile counterexample."
  - "discovery/solve_thm_finite_sample_location_barrier.json — finite-sample full-joint location-mixture lower-bound derivation."
  - "discovery/solve_thm_finite_sample_location_barrier_explicit_elbow.json — explicit one-sided noncontraction elbow and strengthened witness constants."
  - "discovery/solve_lem_profile_cutoff_localization.json — failed profile-localization route and counterexample material reusable in a future higher-smoothness attempt."
  - "discovery/writeup.tex — consolidated theorem statements, proofs, literature positioning, and open critical-window obligations."
seeds_burned: []
proof_attempt_summary: |
  Eight solve rounds established the known-cutoff minimax benchmark, a legal full-observation
  location-mixture noncontraction barrier with an explicit one-sided elbow, and oracle-order
  attainment on the s=1 Lipschitz strong-signal face. The proposed affine/profile cutoff
  localizer fails for s>1, and the exact critical-window connected-length law, a matching
  higher-smoothness procedure and converse term, and one bounded denominator-event
  recalculation remain unresolved. The repaired cold review therefore rated the sound package
  subfield (6.5), below the field gate (7.2), and not salvageable within this run's scope.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 70772001
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 70772001
  total_tokens_consumed: null
banked_on: "2026-09-10"
---

# stat_unknowncutoff_weaklate_frontier / v1 — Downgraded

**Topic.** Honest fuzzy-RD inference when the compliance jump and its unknown location vanish together PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolve derives the known-cutoff honest-length order min(1,n^(-s/(2s+1))/kappa) and constructs legal smooth latent monotone causal mixtures over disjoint cutoff locations. Exact full-joint likelihood calculations yield a nonshrinking unknown-cutoff lower bound when n*kappa^(2+1/s)=o(log(1/kappa)), including sequences on which known-cutoff intervals shrink. A second construction assigns all response types the same smoothly varying potential-outcome table, making outcomes conditionally identical across alternatives: outcome-assisted localization cannot remove the worst-case barrier. A four-sample coarse scan, flank regression, local cutoff classifier, and fixed-center moment inversion provide a detailed strong-signal upper-bound architecture. The closest fixed-jump, known-cutoff weak-IV, and derivative-location sources were checked; no same-object collision was found in the bounded search. These results do not prove the full frontier.
UNRESOLVED BOTTLENECK: Derive and explicitly evaluate the matched fixed-alpha connected-interval length inside n*kappa^(2+1/s) comparable to log(1/kappa), using sharp compensation profiles, truncated location mixtures, and effect-label testing; finish the strong-upper constants and maximal inequality.
EARLY KILL TEST: Solve the s=1 common-outcome plateau experiment through its critical window and compare the compensation profile with a finite-grid latent Lipschitz optimization. Do not replace the full kernel with separated regimes or coverage-only inversion.
STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/mill/scratch/mill-w10/presolve_stat_unknowncutoff_weaklate_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** Delivered tier subfield < floor field; not salvageable within scope.

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

---
qid: exp_complete_balance_secondorder
spec: v1
topic: "For fixed binary potential outcomes and uniform assignment of exactly half of a positive even population to treatment, let rho_n^CR be worst-schedule squared-error minimax risk for ATE estimators using both arm-success counts and let rho_n^W restrict rules to W=2(X_1-X_0). Prove rho_n^CR=rho_n^W at n=2,4,6 and rho_8^CR<rho_8^W. Supply analytic primal/least-favorable-prior equality certificates, including the algebraic seven-state n=6 saddle, and a serialized rational n=8 two-count upper certificate and W-only prior lower certificate proving rho_8^CR<0.06541<0.06578<rho_8^W. Derive the exact response-type hypergeometric games and explain why the second count first changes the minimax envelope at eight. Treat later-even persistence and every higher-order balance-tax law as open; make no confidence-set or pointwise-dominance claim. The consumer is DeclareDesign randomizr::complete_ra, whose exact-balance users learn the first small-n setting where reducing two counts to their difference is minimax-lossy. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Fresh exact checks verify rho_2=1/4, rho_4=1-sqrt(3)/2, an algebraic seven-state equality saddle at n=6, and the rational n=8 sandwich 457801172643/7000000000000<0.06541<0.06578<224641744872980943629642927781/3414537001722982784239360000000. A strengthened standard-library verifier checks legal assignments, positive priors, radical isolation, active-risk identities, every full-count posterior equation, inactive constraints, and certificate directions. Bounded searches found no exact-cutoff collision; Hull v3 leaves the related complete-randomization question conjectural. UNRESOLVED BOTTLENECK: Independently reconstruct the four finite certificates directly from the response-type hypergeometric kernel, separately from the embedded labeled-assignment enumerator. EARLY KILL TEST: Reconstruct the n=6 seven-state saddle from hypergeometric coefficients and verify every posterior identity and all 77 inactive inequalities exactly; any mismatch stops the finite headline. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_complete_balance_secondorder.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "The delivered theorem covers n=2,4,6,8 only; exact n=8 risk, all-even persistence, and the compression-tax rate remain open."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The delivered compression result is confined to four very small population sizes: equality is established at 2, 4, and 6, while only strict separation and a nonmatching bracket are established at 8."
  - "The general behavior for every even n at least 10, the exact eight-unit value, and the magnitude or asymptotic order of the compression tax all remain open, so the note does not deliver a reusable minimax frontier or rate."
  - "Consequently the package is a careful specialized finite-game contribution rather than a field-level result of broad practical or theoretical reach, which also limits its leading-journal score."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_n24_equality.json
  - discovery/solve_thm_n8_strict_separation.json
  - discovery/solve_thm_hull_class_complete_randomization_strict_small_n.json
  - discovery/solve_prop_first_lossy_size.json
  - discovery/solve_prop_posterior_fiber_change.json
seeds_burned: []
proof_attempt_summary: |
  The run independently reconstructed the response-type hypergeometric games and the finite saddle/certificate package: exact equality at n=2,4,6, strict full-count versus difference-only separation at n=8, and bounded-outcome consequences grounded in Hull's primary source. Both mathematical and decision referees passed, and the two Hull citations were source-attested after correcting a stale equation locator. The field-level promise collapsed because exact n=8 risk, strictness for every later even n, and any uniform compression-tax rate remain open and require a new all-size certificate or active-gradient theory.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 21865031
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 21865031
  total_tokens_consumed: null
banked_on: "2026-09-12"
---

# exp_complete_balance_secondorder / v1 — Downgraded

**Topic.** For fixed binary potential outcomes and uniform assignment of exactly half of a positive even population to treatment, let rho_n^CR be worst-schedule squared-error minimax risk for ATE estimators using both arm-success counts and let rho_n^W restrict rules to W=2(X_1-X_0). Prove rho_n^CR=rho_n^W at n=2,4,6 and rho_8^CR<rho_8^W. Supply analytic primal/least-favorable-prior equality certificates, including the algebraic seven-state n=6 saddle, and a serialized rational n=8 two-count upper certificate and W-only prior lower certificate proving rho_8^CR<0.06541<0.06578<rho_8^W. Derive the exact response-type hypergeometric games and explain why the second count first changes the minimax envelope at eight. Treat later-even persistence and every higher-order balance-tax law as open; make no confidence-set or pointwise-dominance claim. The consumer is DeclareDesign randomizr::complete_ra, whose exact-balance users learn the first small-n setting where reducing two counts to their difference is minimax-lossy. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Fresh exact checks verify rho_2=1/4, rho_4=1-sqrt(3)/2, an algebraic seven-state equality saddle at n=6, and the rational n=8 sandwich 457801172643/7000000000000<0.06541<0.06578<224641744872980943629642927781/3414537001722982784239360000000. A strengthened standard-library verifier checks legal assignments, positive priors, radical isolation, active-risk identities, every full-count posterior equation, inactive constraints, and certificate directions. Bounded searches found no exact-cutoff collision; Hull v3 leaves the related complete-randomization question conjectural. UNRESOLVED BOTTLENECK: Independently reconstruct the four finite certificates directly from the response-type hypergeometric kernel, separately from the embedded labeled-assignment enumerator. EARLY KILL TEST: Reconstruct the n=6 seven-state saddle from hypergeometric coefficients and verify every posterior identity and all 77 inactive inequalities exactly; any mismatch stops the finite headline. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_complete_balance_secondorder.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5 verified a sound specialized finite-game result but graded it incremental below the field floor; all-even persistence is a genuine unresolved research barrier.

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

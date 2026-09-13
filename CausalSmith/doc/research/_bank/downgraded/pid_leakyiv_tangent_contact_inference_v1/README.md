---
qid: pid_leakyiv_tangent_contact_inference
spec: v1
topic: "Leaky-IV tangent-contact inference in Watson et al.'s p=2 linear SEM. Let delta=tau^2-tau_check^2 approach zero over explicit local triangular arrays. Define the total positive-part plug-in interval on empirically infeasible samples, derive its exact square-root Gaussian endpoint law, derive the distinct data-dependent retained-resample kernel used by leakyIV, and prove ordinary/discarded bootstrap nonuniformity. Construct a multiplier score-inversion confidence hull with uniform whole-identified-set coverage, matched n^-1/4 minimax outer directed-Hausdorff loss at contact, root-n loss in the fixed interior, and adaptation by the same one-dimensional procedure. Use the explicit positive-definite Sigma(a) witness and exclude weak instruments by a fixed relevance bound. PRESOLVE EVIDENCE REQUIRING VERIFICATION: In the Gaussian witness, X=Z1+epsilon_x and Y=aZ2+epsilon_y imply sqrt(n)(delta_hat-delta_n) converges to N(0,4) along a_n^2=1-h/sqrt(n); after n^1/4 scaling the ordered endpoints become plus/minus sqrt((h+Z)_+). Conditional on the first-stage realization, retained bootstrap endpoints instead follow a random truncated kernel, establishing a concrete nonuniformity mechanism. A uniform score error r expands quadratic-contact sets by order sqrt(r) and interior sets by order r, so one root-n score hull plausibly adapts between n^-1/4 and n^-1/2. LAN contiguity along the witness supplies the converse route. UNRESOLVED BOTTLENECK: Prove one uniform multiplier approximation for the quadratic score process over both contact-local and interior classes that yields simultaneous whole-set coverage and expected outer-loss bounds under the same critical-value rule. EARLY KILL TEST: On the one-parameter Gaussian witness, prove uniformly for h in a fixed compact set that the score hull covers the entire interval with worst expected outer loss of order n^-1/4 and that the retained bootstrap has the stated random truncated kernel; pivot or stop if either assertion fails."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "tier_genuinely_below"
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The narrow p=2 fixed-d setting, the compressed justification of uniform integrable score-radius control, and the absence of an applied or computational demonstration keep the package below flagship level and constrain its leading-journal score."
  - "The minimax converses match the contact and fixed-interior rates through Gaussian LAN subexperiments, but there is no matching converse for the displayed continuous intermediate-slack elbow."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_bootstrap_nonuniformity.json
  - discovery/solve_thm_adaptive_score_hull.json
  - discovery/solve_lem_ridge_totalization_negligible.json
  - reviews/review_general.json
  - reviews/review_math.json
seeds_burned: []
proof_attempt_summary: |
  The run derived and internally proved 11 statements covering the contact endpoint law,
  the retained-resample random kernel, bootstrap-law nonuniformity, a uniformly valid
  score-inversion hull, and matched contact/interior directed-loss rates. A bounded final
  repair removed an unsupported fixed-percentile coverage consequence and completed the
  related-work comparisons; renewed math and decision panels then passed with no findings.
  The remaining gap is contribution scale: the upper theory stays within a strongly regular
  fixed-dimensional p=2 subclass, with no intermediate-slack converse or applied demonstration.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 27288962
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 27288962
  total_tokens_consumed: null
banked_on: "2026-09-10"
---

# pid_leakyiv_tangent_contact_inference / v1 — Downgraded

**Topic.** Leaky-IV tangent-contact inference in Watson et al.'s p=2 linear SEM. Let delta=tau^2-tau_check^2 approach zero over explicit local triangular arrays. Define the total positive-part plug-in interval on empirically infeasible samples, derive its exact square-root Gaussian endpoint law, derive the distinct data-dependent retained-resample kernel used by leakyIV, and prove ordinary/discarded bootstrap nonuniformity. Construct a multiplier score-inversion confidence hull with uniform whole-identified-set coverage, matched n^-1/4 minimax outer directed-Hausdorff loss at contact, root-n loss in the fixed interior, and adaptation by the same one-dimensional procedure. Use the explicit positive-definite Sigma(a) witness and exclude weak instruments by a fixed relevance bound. PRESOLVE EVIDENCE REQUIRING VERIFICATION: In the Gaussian witness, X=Z1+epsilon_x and Y=aZ2+epsilon_y imply sqrt(n)(delta_hat-delta_n) converges to N(0,4) along a_n^2=1-h/sqrt(n); after n^1/4 scaling the ordered endpoints become plus/minus sqrt((h+Z)_+). Conditional on the first-stage realization, retained bootstrap endpoints instead follow a random truncated kernel, establishing a concrete nonuniformity mechanism. A uniform score error r expands quadratic-contact sets by order sqrt(r) and interior sets by order r, so one root-n score hull plausibly adapts between n^-1/4 and n^-1/2. LAN contiguity along the witness supplies the converse route. UNRESOLVED BOTTLENECK: Prove one uniform multiplier approximation for the quadratic score process over both contact-local and interior classes that yields simultaneous whole-set coverage and expected outer-loss bounds under the same critical-value rule. EARLY KILL TEST: On the one-parameter Gaussian witness, prove uniformly for h in a fixed compact set that the score hull covers the entire interval with worst expected outer loss of order n^-1/4 and that the retained bootstrap has the stated random truncated kernel; pivot or stop if either assertion fails.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** The delivered limit laws, uniform score hull, and matched endpoint-regime rates are sound, but the narrow p=2 fixed-dimensional scope caps the package at subfield (paper-score ceiling 7 below the field threshold 7.2).

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

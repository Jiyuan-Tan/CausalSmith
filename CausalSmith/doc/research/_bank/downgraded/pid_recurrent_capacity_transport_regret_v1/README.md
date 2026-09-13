---
qid: pid_recurrent_capacity_transport_regret
spec: v1
topic: "Study a two-arm randomized recurrent-event trial with absorbing death and right censoring, fixed switch time k, clinical cap H>=2, and a finite event-count threshold menu M. Retain the Janvin C2-C6 causal conditions but DEFINE capped no-carry-over as the replacement for raw C7: for intensive survivors, baseline capped burden B and switched residual W have identified marginals and obey B+W<=H. Characterize the resulting Ferrers transport polytope by exact Hall inequalities and a constructive coupling. Derive sharp fixed-threshold endpoints including the backward-deficit upper CDF; prove every compatible triple coupling has an observed-law-preserving finite-history causal response-tree lift; identify the complete joint threshold-value set; compute support functions, pairwise worst-case regret, and minimax thresholds with the eligibility-greedy O(H log H) algorithm; and give censoring-adjusted simultaneous confidence-polytope inversion covering the whole value set and all robust optimizers at Hall and policy ties. Include a concrete H=3 rational example where shared-law regret selects threshold 1 but separate marginal intervals select threshold 3. Treat SPRINT's published k=300 adverse-event switching analysis as a capped-loss consumer only if a clinically defensible cap can be prespecified. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact endpoint proofs, a full-history response-tree construction, and an eligibility-greedy support algorithm were derived. Exact rational checks passed 2,500 endpoint comparisons and 2,100 greedy-versus-LP comparisons, both gated witnesses, and the recommendation-reversal regret matrix. UNRESOLVED BOTTLENECK: Establish a clinically defensible cumulative cap H for which capped-increment no-carry-over is substantively credible in SPRINT, and independently formalize the finite-history causal lift and dual Lipschitz details. EARLY KILL TEST: For externally justified caps at k=300, compute censoring-adjusted Hall slacks and confidence-polytope feasibility, then compare shared-law regret with fixed m=1 and interval-box decisions; reject the SPRINT application if no defensible cap is credible or the model is statistically incompatible. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_recurrent_capacity_transport_regret.md"
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The exact Hall characterization, causal lift, joint value set, regret calculations, and inference theory are all conditional on the bespoke law-side restriction B+W<=H."
  - "No clinically grounded derivation or external application establishes that restriction, and SPRINT remains explicitly unevaluated, so the delivered practical contribution is a specialized sensitivity construction rather than a field-level recurrent-event result."
  - "No genuinely prespecified k=300 SPRINT analysis establishes a defensible H, Hall feasibility, or resulting decision consequence."
reusable_artifacts:
  - "discovery/core.json — accepted theorem graph: Ferrers endpoints, cap-fibre causal lift, shared-law deterministic/randomized regret, and positive/negative inference boundary"
  - "discovery/writeup.tex — discharged derivation and synchronized scope/limitations"
  - "discovery/solve_thm_causal_response_tree_lift.json — observed-law-preserving cap-fibre construction"
  - "discovery/solve_thm_confidence_polytope.json — deterministic and randomized optimizer confidence inversion"
  - "discovery/solve_thm_uniform_censoring_inference_limit.json — quantitative-overlap positive result and pointwise-overlap impossibility"
  - "discovery/gaps.json — literature map and source locators, including Dahl and Janvin comparators"
seeds_burned:
  - index: 0
    one_liner: "Shared-law capped threshold geometry and minimax regret"
    reason: "The selected angle exhausted six proposal revisions and four D0 solve rounds; the remaining deficit is external clinical mechanism/application evidence, not an unresolved mathematical kernel."
proof_attempt_summary: |
  Discovery proved a sound conditional mathematical package: exact Ferrers sharp bounds, an observed-law-preserving cap-fibre lift with exact transfer to the Janvin raw-no-carry-over subclass, shared-law deterministic and randomized regret, and complementary root-n quantitative-overlap inference versus pointwise-overlap impossibility. Four D0 solve rounds and three D0.5 revisions closed the mathematical and inference gaps, and the final math referee passed. The result remained below the field floor because B+W<=H was imposed rather than derived from a clinically credible primitive mechanism, and no prespecified SPRINT k=300 analysis validated the cap, Hall system, or decision consequence.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 77460678
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 77460678
  total_tokens_consumed: null
banked_on: "2026-09-09"
---

# pid_recurrent_capacity_transport_regret / v1 — Downgraded

**Topic.** Study a two-arm randomized recurrent-event trial with absorbing death and right censoring, fixed switch time k, clinical cap H>=2, and a finite event-count threshold menu M. Retain the Janvin C2-C6 causal conditions but DEFINE capped no-carry-over as the replacement for raw C7: for intensive survivors, baseline capped burden B and switched residual W have identified marginals and obey B+W<=H. Characterize the resulting Ferrers transport polytope by exact Hall inequalities and a constructive coupling. Derive sharp fixed-threshold endpoints including the backward-deficit upper CDF; prove every compatible triple coupling has an observed-law-preserving finite-history causal response-tree lift; identify the complete joint threshold-value set; compute support functions, pairwise worst-case regret, and minimax thresholds with the eligibility-greedy O(H log H) algorithm; and give censoring-adjusted simultaneous confidence-polytope inversion covering the whole value set and all robust optimizers at Hall and policy ties. Include a concrete H=3 rational example where shared-law regret selects threshold 1 but separate marginal intervals select threshold 3. Treat SPRINT's published k=300 adverse-event switching analysis as a capped-loss consumer only if a clinically defensible cap can be prespecified. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact endpoint proofs, a full-history response-tree construction, and an eligibility-greedy support algorithm were derived. Exact rational checks passed 2,500 endpoint comparisons and 2,100 greedy-versus-LP comparisons, both gated witnesses, and the recommendation-reversal regret matrix. UNRESOLVED BOTTLENECK: Establish a clinically defensible cumulative cap H for which capped-increment no-carry-over is substantively credible in SPRINT, and independently formalize the finite-history causal lift and dual Lipschitz details. EARLY KILL TEST: For externally justified caps at k=300, compute censoring-adjusted Hall slacks and confidence-polytope feasibility, then compare shared-law regret with fixed m=1 and interval-box decisions; reject the SPRINT application if no defensible cap is credible or the model is statistically incompatible. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_recurrent_capacity_transport_regret.md

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** Sound and non-laundered, but below the field floor: no primitive clinically credible derivation of B+W<=H and no genuinely prespecified k=300 SPRINT Hall-feasibility and decision analysis.

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

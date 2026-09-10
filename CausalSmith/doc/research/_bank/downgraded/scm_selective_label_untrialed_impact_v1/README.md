---
qid: scm_selective_label_untrialed_impact
spec: v1
topic: "Sharp action-dependent selective-label bounds for untrialed human-AI deployment. In a finite randomized multi-policy SCM, observe binary ground-truth Z only when endogenous action A reveals it, index common response potentials by distinct externally certified prediction-performance values q, and impose the Zhang-Skalnes-Chen-Oberst unit-level correctness, performance-order, and neutral restrictions. Define the Selective-Label Counterfactual-Correctness polytope over Z and q-indexed action/outcome response types; prove its two LP optima are attained sharp endpoints for the untrialed downstream mean, strictly refine the Z-blind projection on a nonempty relative-open set, and construct finite-sample whole-set inference by intersecting a simultaneous multinomial confidence polytope with the observable-law polytope. Use Euclidean projection for plug-in endpoints and derive projection-composed directional limits with valid m-out-of-n subsampling at simultaneous ties. Include the verified 32-type witness with full [1/2,3/4], blind [1/4,1], and the Imai PSA trial/aihuman consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Finite legal types give O=B(Delta) and every feasible weight vector canonically constructs an attaining SCM, so optimizing the untrialed-outcome coordinate yields the exact sharp interval. Independent enumeration reproduced the 32-type bounds and the relative-interior perturbation full [397/800,601/800] versus blind [99/400,1]. Checks covered same-q collisions, performance ties, empirical infeasibility, boundary laws, endpoint attainment, and classification-risk or policy-value relabeling; no prior-art collision survived. UNRESOLVED BOTTLENECK: Prove conservative conditional quantile validity for centered m-out-of-n subsampling of the joint projection-composed endpoint map when the observable law lies on a projection face and both LPs have multiple optimal bases, including atoms in the directional limit. EARLY KILL TEST: On the 32-type instance, choose a boundary law with simultaneous projection and endpoint ties, enumerate active cones and optimal dual faces, derive the exact Gaussian directional law, and compare centered subsampling for several m/n tending to zero; stop if conservative-quantile convergence fails."
novelty_target: field
banked_novelty_tier: field
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: "kernel_substituted"
reusable: solver_blocked
reraise_status: unknown
gap_reasons:
  # TODO: paste verbatim reviewer phrases identifying which Conjecture
  # collapsed and why. Source: scm_selective_label_untrialed_impact_v1_reviews.jsonl and any
  # *_oneshot_stage0_5_*.txt files in this directory.
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  TODO: 2-3 sentence epitaph — what was attempted, what collapsed, what remains.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 108462463
  pipeline_claude_tokens: 36583669
  total_tokens_consumed: null
banked_on: "2026-09-04"
---

# scm_selective_label_untrialed_impact / v1 — Downgraded

**Topic.** Sharp action-dependent selective-label bounds for untrialed human-AI deployment. In a finite randomized multi-policy SCM, observe binary ground-truth Z only when endogenous action A reveals it, index common response potentials by distinct externally certified prediction-performance values q, and impose the Zhang-Skalnes-Chen-Oberst unit-level correctness, performance-order, and neutral restrictions. Define the Selective-Label Counterfactual-Correctness polytope over Z and q-indexed action/outcome response types; prove its two LP optima are attained sharp endpoints for the untrialed downstream mean, strictly refine the Z-blind projection on a nonempty relative-open set, and construct finite-sample whole-set inference by intersecting a simultaneous multinomial confidence polytope with the observable-law polytope. Use Euclidean projection for plug-in endpoints and derive projection-composed directional limits with valid m-out-of-n subsampling at simultaneous ties. Include the verified 32-type witness with full [1/2,3/4], blind [1/4,1], and the Imai PSA trial/aihuman consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Finite legal types give O=B(Delta) and every feasible weight vector canonically constructs an attaining SCM, so optimizing the untrialed-outcome coordinate yields the exact sharp interval. Independent enumeration reproduced the 32-type bounds and the relative-interior perturbation full [397/800,601/800] versus blind [99/400,1]. Checks covered same-q collisions, performance ties, empirical infeasibility, boundary laws, endpoint attainment, and classification-risk or policy-value relabeling; no prior-art collision survived. UNRESOLVED BOTTLENECK: Prove conservative conditional quantile validity for centered m-out-of-n subsampling of the joint projection-composed endpoint map when the observable law lies on a projection face and both LPs have multiple optimal bases, including atoms in the directional limit. EARLY KILL TEST: On the 32-type instance, choose a boundary law with simultaneous projection and endpoint ties, enumerate active cones and optimal dual faces, derive the exact Gaussian directional law, and compare centered subsampling for several m/n tending to zero; stop if conservative-quantile convergence fails.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** Operator decision 2026-09-04: paper_score_ceiling 7.2 is below the raised D0.5 field bar of 7.5. All three D0.5 referees passed (general field/meets_floor, math pass, rubric pass); the F2 scaffold had failed the structural plan gate at P9. Banked downgraded without further formalization spend.

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

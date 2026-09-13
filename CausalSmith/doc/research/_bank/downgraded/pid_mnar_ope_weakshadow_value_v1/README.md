---
qid: pid_mnar_ope_weakshadow_value
spec: v1
topic: "Sharp policy-value bounds and whole-set inference for finite-horizon off-policy evaluation with MNAR discrete rewards and an incomplete next-state weak shadow. The known behavior policy uses recorded history, while a fixed complete-information deployment policy may depend on latent reward history. Define full-history compatible laws by observed-cell marginalization, known behavior factors, positivity, and weak-shadow cross-product equations. Prove attained sharp endpoints for the policy-value polynomial, an observable necessary-and-sufficient factorization-versus-strict-containment theorem relative to stagewise Chen programs, and whole-set coverage by simultaneous multinomial confidence-fiber inversion with certified global optimization. Reanalyse the Wang et al. and Wei et al. sepsis OPE workflows. PRESOLVE EVIDENCE REQUIRING VERIFICATION: In the finite full-history simplex, observed-data and behavior restrictions are linear, weak-shadow restrictions are polynomial cross-products, and the fixed-policy value is linear in the compatible full-law probabilities; compactness therefore gives attained extrema, while confidence-fiber inversion covers the whole true set whenever the observed law lies in the multinomial fiber. Exact arithmetic for the two-stage three-reward witness verifies Aw=beta, the null direction, normalization, completion-dependent policy occupancy, and the value interval [229/140,26/15]. Static T=1, reward-history-blind targets, completeness, zero-cell boundaries, and the supplied-source collision set were checked without defeating the coupled program; generic semialgebraic optimization alone would not carry the tier. UNRESOLVED BOTTLENECK: Prove the observable rectangularity/extremizing-face theorem characterizing exactly when the global full-history fiber contains simultaneous stagewise extrema and when reward-history policy dependence forces strict containment. EARLY KILL TEST: On the smallest two-stage binary-action models with one and then two MNAR three-level rewards, compute certified global extrema and the correctly continuation-weighted rectangular Chen relaxation; if every nondegenerate instance agrees, pivot because the dynamic non-factorization headline collapses."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  - "The proposed theorem-level contribution—a coefficient-complete, relatively open strict-containment certificate with a rational witness and equality locus—has been replaced by an expressly unresolved obligation; the proved compactness, face identity, static reduction, CAD specialization, and fiber-inversion coverage do not supply that advertised dynamic novelty."
  - "The compact-face criterion reduces strict containment to emptiness of a simultaneous stage-face system, while the signed-minor calculation only certifies a local objective slope. It does not show that locally forced opposite boundary choices are incompatible with one globally coupled complete-history law."
reusable_artifacts:
  - "discovery/core.json — sound compact semialgebraic fiber/value-image framework, static Chen reduction, common-face criterion, and finite-sample confidence-fiber coverage"
  - "discovery/solve_oeq_generic_strict_containment.json — audited exact fixed-(p,mu) policy-slice witness and phase-diagram attempt"
  - "discovery/writeup.tex — derivation narrative and exact [229/140,26/15] witness calculations"
  - "orchestrator/decision_log.jsonl — source corrections, maximality audit, and terminal validity receipts"
seeds_burned:
  - index: 0
    one_liner: "dynamic-face-pasting"
    reason: "Selected seeds were incorporated, but four D0 solve rounds could not lift the dynamic-face-pasting kernel to a full-space theorem; the other two contributed only incremental support."
  - index: 1
    one_liner: "multinomial-fiber-inversion"
    reason: "Selected seeds were incorporated, but four D0 solve rounds could not lift the dynamic-face-pasting kernel to a full-space theorem; the other two contributed only incremental support."
  - index: 2
    one_liner: "value-identification-without-law-identification"
    reason: "Selected seeds were incorporated, but four D0 solve rounds could not lift the dynamic-face-pasting kernel to a full-space theorem; the other two contributed only incremental support."
proof_attempt_summary: |
  Four substantive D0 solve rounds corrected the behavior-factorization model, proved the supporting compactness/CAD/static-reduction/coverage results, and produced an exact fixed-(p,mu) policy-slice phase diagram with rational interval [229/140,26/15] and 1/6 endpoint gaps. The attempt did not prove strict containment on a relatively open region of the full compatible (p,mu,pi) parameter space; doing so still requires a concrete rational witness plus the cross-stage elimination and sign certificate, so the field-tier headline remains open.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 39748568
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 39748568
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# pid_mnar_ope_weakshadow_value / v1 — Downgraded

**Topic.** Sharp policy-value bounds and whole-set inference for finite-horizon off-policy evaluation with MNAR discrete rewards and an incomplete next-state weak shadow. The known behavior policy uses recorded history, while a fixed complete-information deployment policy may depend on latent reward history. Define full-history compatible laws by observed-cell marginalization, known behavior factors, positivity, and weak-shadow cross-product equations. Prove attained sharp endpoints for the policy-value polynomial, an observable necessary-and-sufficient factorization-versus-strict-containment theorem relative to stagewise Chen programs, and whole-set coverage by simultaneous multinomial confidence-fiber inversion with certified global optimization. Reanalyse the Wang et al. and Wei et al. sepsis OPE workflows. PRESOLVE EVIDENCE REQUIRING VERIFICATION: In the finite full-history simplex, observed-data and behavior restrictions are linear, weak-shadow restrictions are polynomial cross-products, and the fixed-policy value is linear in the compatible full-law probabilities; compactness therefore gives attained extrema, while confidence-fiber inversion covers the whole true set whenever the observed law lies in the multinomial fiber. Exact arithmetic for the two-stage three-reward witness verifies Aw=beta, the null direction, normalization, completion-dependent policy occupancy, and the value interval [229/140,26/15]. Static T=1, reward-history-blind targets, completeness, zero-cell boundaries, and the supplied-source collision set were checked without defeating the coupled program; generic semialgebraic optimization alone would not carry the tier. UNRESOLVED BOTTLENECK: Prove the observable rectangularity/extremizing-face theorem characterizing exactly when the global full-history fiber contains simultaneous stagewise extrema and when reward-history policy dependence forces strict containment. EARLY KILL TEST: On the smallest two-stage binary-action models with one and then two MNAR three-level rewards, compute certified global extrema and the correctly continuation-weighted rectangular Chen relaxation; if every nondegenerate instance agrees, pivot because the dynamic non-factorization headline collapses.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The proposed coefficient-complete, relatively open strict-containment certificate remains an unresolved obligation; the proved supporting results do not supply the advertised dynamic novelty.

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

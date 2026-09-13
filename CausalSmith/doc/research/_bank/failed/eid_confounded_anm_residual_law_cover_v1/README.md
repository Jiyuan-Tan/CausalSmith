---
qid: eid_confounded_anm_residual_law_cover
spec: v1
topic: "Gaussian-free residual-law identification of all interventions in confounded additive-noise SCMs under an exact intervention cover. For a known acyclic treatment DAG with X_i=f_i(X_Pa(i))+U_i and Y=f_Y(X)+U_Y, allow an arbitrary correlated Borel disturbance law with finite second moments. Given the full observational law, do(X=x), and a fixed finite regime collection R whose families leave each i free while intervening on all Pa(i), require coverage of the entire observational support and every recursively reached target support. Prove that regime means identify every structural mean, observational residuals identify the complete centered joint exogenous law, and a topological residual pushforward identifies every covered postintervention distribution and bounded AOI. Prove the same exact combinatorial cover is necessary for universal identification by two bounded non-Gaussian SCMs that agree simultaneously on the complete regime tuple but differ on a target intervention. Construct a cross-fitted regime-regression plus joint-residual-resampling estimator with bootstrap inference for smooth AOIs and distributional bands under explicit no-atom/density conditions. Use the four-point Rademacher residual witness and Jeunen et al.'s published International Stroke Trial semi-synthetic intervention-disentanglement benchmark; do not claim a new clinical aspirin conclusion."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: REVISE
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: retry
gap_reasons:
  - "For a failed parent-cell certificate p_star may belong to the observational support by definition of H_i, but W4 requires every observational row to avoid p_star; its point modification therefore cannot simultaneously preserve P_obs in that allowed case."
  - "f^D is declared unique even when C_Delta=0, but the mean-zero normalization does not eliminate a nonconstant zero-mean kernel element; define it only conditional on C_Delta=1 or as a set-valued inverse."
  - "The shrinking neighborhood, stability modulus, implementation-error metric, sampling experiment, and minimax loss are unspecified, so neither 'largest' nor the proposed lower bound is defined."
  - "The angle-1 revision could not pass the D-1.2 producer boundary after three attempts: invalid schema metadata, persistence to a noncanonical path, then unmatched inline-math delimiters."
reusable_artifacts:
  - "discovery/proto_core.json — field-tier angle-1 natural-value-shift operator-rank frontier before requested repairs"
  - "discovery/proto_core_angle0_rejected.json — rejected direct-cover formulation retained with its atomic-support failure mode"
  - "reviews/angle1_v1.json — repairable field-tier review and shift-intervention literature gaps"
  - "orchestrator/decision_log.jsonl — explicit atomic counterexample showing direct parent cover is sufficient but not necessary"
seeds_burned: []
proof_attempt_summary: |
  Angle 0 pursued an exact direct-intervention-cover iff, but an observed atomic parent cell refuted necessity: observational means can identify the missing mechanism value without direct coverage. Angle 1 pivoted to a functional operator-rank frontier and received a repairable field-tier REVISE, but three D-1.2 author attempts failed the producer boundary before a corrected proposal could be reviewed. The operator deferred the required boundary redesign, so the run was banked as a retry rather than as a mathematical defeat.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 34040215
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 34040215
  total_tokens_consumed: null
banked_on: "2026-09-12"
---

# eid_confounded_anm_residual_law_cover / v1 — Failed

**Topic.** Gaussian-free residual-law identification of all interventions in confounded additive-noise SCMs under an exact intervention cover. For a known acyclic treatment DAG with X_i=f_i(X_Pa(i))+U_i and Y=f_Y(X)+U_Y, allow an arbitrary correlated Borel disturbance law with finite second moments. Given the full observational law, do(X=x), and a fixed finite regime collection R whose families leave each i free while intervening on all Pa(i), require coverage of the entire observational support and every recursively reached target support. Prove that regime means identify every structural mean, observational residuals identify the complete centered joint exogenous law, and a topological residual pushforward identifies every covered postintervention distribution and bounded AOI. Prove the same exact combinatorial cover is necessary for universal identification by two bounded non-Gaussian SCMs that agree simultaneously on the complete regime tuple but differ on a target intervention. Construct a cross-fitted regime-regression plus joint-residual-resampling estimator with bootstrap inference for smooth AOIs and distributional bands under explicit no-atom/density conditions. Use the four-point Rademacher residual witness and Jeunen et al.'s published International Stroke Trial semi-synthetic intervention-disentanglement benchmark; do not claim a new clinical aspirin conclusion.

**Novelty target.** field

**Stage -0.5 verdict.** REVISE

**Stage 0.5 verdict.** NA

**Banking reason.** D-1.2 producer boundary exhausted three attempts through invalid schema metadata, a noncanonical output path, and unmatched inline-math delimiters; operator deferred the required redesign and directed terminal banking.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

The promising follow-on is the angle-1 operator-rank formulation. A future run should first repair the
D-1.2 producer architecture so TypeScript owns canonical persistence, then address the inverse/domain
definitions, specify the stability experiment, and compare directly with BackShift and Causal Dantzig.

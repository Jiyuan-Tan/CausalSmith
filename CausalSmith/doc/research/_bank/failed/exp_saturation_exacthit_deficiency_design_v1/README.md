---
qid: exp_saturation_exacthit_deficiency_design
spec: v1
topic: "Exact-hit information deficiency and minimax design for ranking exact treatment saturations. Fix K≥2, equal cluster size n, distinct interior rational exact-count policies pi_k=m_k/n, iid clusters with unrestricted binary within-cluster interference schedules, and exact-slice welfare targets. Compare fixed-count two-stage complete randomization with iid nominal labels followed by unit-Bernoulli assignment. Let B_kl=Pr(Bin(n,pi_l)=m_k) and q=Bp. Prove the target-tangent lower experiment and local minimax regret bound by holding nontarget-count laws fixed, match it with assignment-calibrated cross-label exact-hit estimation, derive the primitive joint CLT, consistent studentization and rank set, characterize sharp CR/Bernoulli equality and strict-loss conditions, solve the complete two-policy allocation map, and give a certified general-K Gaussian-risk/outer-simplex computation. Use the four-node pi={1/4,1/2} witness and Egger et al.'s Kenya saturation design as consumer; distinguish Han–Owusu–Shin, Joo's downstream Gaussian selection result, Chan et al., and Loomba–Eckles. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact nuisance deletion and an independent target-bit submodel derive pooled hit rates q=Bp. Recalculation gives B=[[27/64,1/4],[27/128,3/8]], optimal first-label share 0.39383577843, local regret penalty 1.26189430297, and sample-size penalty 1.59237723186 relative to optimized exact-count assignment. Raw pooling is not pointwise efficient when within-slice assignment means differ; calibration over the observed assignment fixes this without changing the target. Checks covered zero hits, boundary shares, unequal variances, separated versus tied means, informative nontarget schedules, shrinking variances, common-parameter games, and 280840 two-count menus; no verified collision appeared. UNRESOLVED BOTTLENECK: Prove a certified general-K Gaussian minimax selector on the full contrast space with partial ties and covariance perturbations, then transfer its risk uniformly to the primitive calibrated cluster experiment. EARLY KILL TEST: At n=4 and pi={1/4,1/2}, verify tau²/q information for both the independent tied target-bit submodel and the legal assignment-heterogeneous means (4/5,4/5,1/5,1/5), and match the two-point Gaussian lower bound to pooled regret; failure stops the kernel. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_saturation_exacthit_deficiency_design.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: null
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  - "TriangularArrayUniformTransfer assumes only measurability of PilotCovarianceGoodEvent, while the arbitrary covariance-cell assignment and choice-based semantic evaluation leave empiricalProgramSelector potentially nonmeasurable in pilot data."
  - "For every singleton S⊆A, RetainedFaceCovariancePartitions requires multiple nonempty covariance cells, but CovarianceCellContains forces every singleton cell to equal [] because QuotientIndex S is empty; thus UniformCertifiedTriangularScheduleArray is impossible and the entire triangular-transfer implication is vacuous."
  - "CheckedOuterDesignTranscript omits a certified interval for each outer optimum and does not identify the cells containing all minimizers, while it additionally requires finitely many finite rational upper bounds to cover every strictly positive exact-count allocation."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/d05_acceptance_receipt.json
  - discovery/proof_archive/
  - formalization/plan.json
seeds_burned: []
proof_attempt_summary: |
  Discovery converged to a 24/24 proved paper and passed the field-tier D0.5 review; formalization also completed the reusable finite-categorical multinomial-count helper and its exact-hit-factorization consumer. Repeated F2/F2.5 re-scaffolds repaired sequence indexing, empirical covariance snapping, active-face support, and executable certificate structure, but the final authorized repair again failed to make the empirical selector jointly measurable. The remaining scaffold also made singleton faces vacuous and incorrectly required a finite bounded transcript over the full open exact-count simplex, so the binding no-progress condition ended the run without refuting the mathematical kernel.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 383318619
  pipeline_claude_tokens: 107812548
  total_tokens_consumed: null
banked_on: "2026-09-07"
---

# exp_saturation_exacthit_deficiency_design / v1 — Failed

**Topic.** Exact-hit information deficiency and minimax design for ranking exact treatment saturations. Fix K≥2, equal cluster size n, distinct interior rational exact-count policies pi_k=m_k/n, iid clusters with unrestricted binary within-cluster interference schedules, and exact-slice welfare targets. Compare fixed-count two-stage complete randomization with iid nominal labels followed by unit-Bernoulli assignment. Let B_kl=Pr(Bin(n,pi_l)=m_k) and q=Bp. Prove the target-tangent lower experiment and local minimax regret bound by holding nontarget-count laws fixed, match it with assignment-calibrated cross-label exact-hit estimation, derive the primitive joint CLT, consistent studentization and rank set, characterize sharp CR/Bernoulli equality and strict-loss conditions, solve the complete two-policy allocation map, and give a certified general-K Gaussian-risk/outer-simplex computation. Use the four-node pi={1/4,1/2} witness and Egger et al.'s Kenya saturation design as consumer; distinguish Han–Owusu–Shin, Joo's downstream Gaussian selection result, Chan et al., and Loomba–Eckles. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact nuisance deletion and an independent target-bit submodel derive pooled hit rates q=Bp. Recalculation gives B=[[27/64,1/4],[27/128,3/8]], optimal first-label share 0.39383577843, local regret penalty 1.26189430297, and sample-size penalty 1.59237723186 relative to optimized exact-count assignment. Raw pooling is not pointwise efficient when within-slice assignment means differ; calibration over the observed assignment fixes this without changing the target. Checks covered zero hits, boundary shares, unequal variances, separated versus tied means, informative nontarget schedules, shrinking variances, common-parameter games, and 280840 two-count menus; no verified collision appeared. UNRESOLVED BOTTLENECK: Prove a certified general-K Gaussian minimax selector on the full contrast space with partial ties and covariance perturbations, then transfer its risk uniformly to the primitive calibrated cluster experiment. EARLY KILL TEST: At n=4 and pi={1/4,1/2}, verify tau²/q information for both the independent tied target-bit submodel and the legal assignment-heterogeneous means (4/5,4/5,1/5,1/5), and match the two-point Gaussian lower bound to pooled regret; failure stops the kernel. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_saturation_exacthit_deficiency_design.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** The identical empiricalProgramSelector joint-measurability defect recurred after the supervisor-approved final scoped reset, triggering the binding no-progress stop.

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

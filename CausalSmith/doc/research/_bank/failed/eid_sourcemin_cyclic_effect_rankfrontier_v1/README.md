---
qid: eid_sourcemin_cyclic_effect_rankfrontier
spec: v1
topic: "Deletion-rank equilibrium-effect frontier for source-minimal cyclic latent LiNG models. Given a normalized full-row-rank overcomplete ICA representation X=C epsilon with independent moment-determinate non-Gaussian sources and no zero or proportional columns, range over every latent cyclic SCM completion with exactly those source directions, zero structural diagonal, invertible observational and postintervention systems, and no stability assumption. For ordered observed x!=y, prove the sharp equilibrium-effect set is {C_yj/C_xj: C_xj!=0 and rank(C_{-x,-j})=p-1}; construct a full same-law completion for every admissible j, characterize identification iff the set is a singleton, return two exact SCMs otherwise, and certify all values in O(n^4) arithmetic operations. For iid samples on a common-cumulant-order subclass with fixed moment, tensor-separation, minor, and denominator margins, derive the OICA inverse and simultaneous confidence union with uniform coverage and root-N Hausdorff uncertainty. Use Dai et al. 2026 and Tramontano et al. as anchors and the 14-stock HSI equivalence class as the consumer; graphical irreducibility without source minimality is explicitly excluded. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Algebra gives the hard-intervention effect as a mixing-column ratio. A deletion-rank/cofactor argument plus one latent-row shear constructs every admissible completion, yielding the exact finite set and an O(n^4) all-witness algorithm; 248 rational witnesses across 24 matrices were checked. A common-order lifted-cumulant tensor pencil gives an explicit local inverse and finite-sample simultaneous coverage. Duplicate source directions, deletion-rank jumps, vanishing treatment loadings, stability restrictions, multi-effect set diameter, and nearby 2024-2026 literature were stress-tested; the larger graphically irreducible fiber fails. UNRESOLVED BOTTLENECK: The mathematical theorem spine is complete on the stated separated iid class, but using the HSI illustration requires a defensible dependent-time-series sampling model and an informative empirical separation certificate; source-specific multi-order cumulant adaptation remains outside scope. EARLY KILL TEST: Reproduce the row-shear and perfect-matching constructions on rational p<=4,n<=6 instances and challenge the tensor inverse near every declared margin; any failed completion identity, legal separated tensor collision, or prior theorem with the same fixed-law source-minimal fiber and conclusion stops the run. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_sourcemin_cyclic_effect_rankfrontier.md"
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: null
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  - "Closed: none."
  - "All exploratory edits were reverted."
  - "basisSelectionStage: blocked on proving the full register-state simulation connecting the projector/echelon scan and one-hot serialization to greedyCompletionSet, then to greedyCompletionTail_eq_canonical."
reusable_artifacts:
  - "discovery/core.json — field-tier, source-attested theorem/dependency graph"
  - "orchestrator/exact_matrix_matching_compiler_requirement.md — neutral reusable compiler contract"
  - "orchestrator/finite_moment_near_gaussian_perturbation_requirement.md — completed near-Gaussian substrate contract"
  - "CausalSmith/ExactID/EID_SourceminCyclicEffectRankfrontier_Research/Helpers/KernelMatching.lean — paper-local exact matching composition and completed cubic pair helper"
seeds_burned: []
proof_attempt_summary: |
  Discovery passed the field-tier panel and most of the Lean development closed, including the exact shared-run cubic pair helper and a promoted finite-moment near-Gaussian perturbation theorem. The reusable exact matrix/matching study completed six supporting modules, but the bounded extension's renewed basis-selection filler closed nothing and reverted its exploratory edits. Four execution-linked stage proofs remain in RegisterProgram.lean, so the paper-owned shared-kernel matching certificate could not be delivered under the unchanged API.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 364475560
  pipeline_claude_tokens: 25546077
  total_tokens_consumed: null
banked_on: "2026-09-07"
---

# eid_sourcemin_cyclic_effect_rankfrontier / v1 — Failed

**Topic.** Deletion-rank equilibrium-effect frontier for source-minimal cyclic latent LiNG models. Given a normalized full-row-rank overcomplete ICA representation X=C epsilon with independent moment-determinate non-Gaussian sources and no zero or proportional columns, range over every latent cyclic SCM completion with exactly those source directions, zero structural diagonal, invertible observational and postintervention systems, and no stability assumption. For ordered observed x!=y, prove the sharp equilibrium-effect set is {C_yj/C_xj: C_xj!=0 and rank(C_{-x,-j})=p-1}; construct a full same-law completion for every admissible j, characterize identification iff the set is a singleton, return two exact SCMs otherwise, and certify all values in O(n^4) arithmetic operations. For iid samples on a common-cumulant-order subclass with fixed moment, tensor-separation, minor, and denominator margins, derive the OICA inverse and simultaneous confidence union with uniform coverage and root-N Hausdorff uncertainty. Use Dai et al. 2026 and Tramontano et al. as anchors and the 14-stock HSI equivalence class as the consumer; graphical irreducibility without source minimality is explicitly excluded. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Algebra gives the hard-intervention effect as a mixing-column ratio. A deletion-rank/cofactor argument plus one latent-row shear constructs every admissible completion, yielding the exact finite set and an O(n^4) all-witness algorithm; 248 rational witnesses across 24 matrices were checked. A common-order lifted-cumulant tensor pencil gives an explicit local inverse and finite-sample simultaneous coverage. Duplicate source directions, deletion-rank jumps, vanishing treatment loadings, stability restrictions, multi-effect set diameter, and nearby 2024-2026 literature were stress-tested; the larger graphically irreducible fiber fails. UNRESOLVED BOTTLENECK: The mathematical theorem spine is complete on the stated separated iid class, but using the HSI illustration requires a defensible dependent-time-series sampling model and an informative empirical separation certificate; source-specific multi-order cumulant adaptation remains outside scope. EARLY KILL TEST: Reproduce the row-shear and perfect-matching constructions on rational p<=4,n<=6 instances and challenge the tensor inverse near every declared margin; any failed completion identity, legal separated tensor collision, or prior theorem with the same fixed-law source-minimal fiber and conclusion stops the run. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_sourcemin_cyclic_effect_rankfrontier.md

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** Substrate unbuildable within the operator-approved bound: post-extension round 9 closed none, reverted all exploratory edits, and left the exact uniform register compiler four proofs short.

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

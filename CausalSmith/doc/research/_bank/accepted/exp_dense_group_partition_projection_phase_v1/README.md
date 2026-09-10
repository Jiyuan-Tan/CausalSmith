---
qid: exp_dense_group_partition_projection_phase
spec: v1
topic: "For fixed M>=2, uniformly draw G disjoint M-subsets from n units and completely randomize G1 groups, with bounded arbitrary composition interference and the PAME target. Derive the exact Kneser/Johnson variance identity and prove G Var(tauhat)=V1/p+V0/(1-p)-rho||Pi1(h1-h0)||^2+o(1) when MG/n->rho. Prove the exact scalar group-CR2 variance identity and its schedule-uniform expansion: at rho=0 the CR2 variance estimator is ratio-consistent under N/n->0 without an N^2/n condition, while at rho>0 its missing first-projection correction gives asymptotic conservativeness and ratio consistency exactly when that correction is negligible. This is a variance-estimation frontier only; claim no centered Gaussian limit, studentization law, or Wald coverage. Establish that no one-realization estimator is uniformly ratio-consistent for the exact variance over the full positive-density class, using the proved common-versus-independent Rademacher schedules, predictable-variation verification, high-probability diagonal selection, and equal observed-data mixtures. Verify the n=8,M=2,G=4 balanced witness with true variance 1/7 and expected CR2 2/7, and state the precise equal-group clubSandwich::vcovCR(type='CR2') consumer. The normalized Kneser eigenvalues are lambda_nk=(-1)^k(M)_k/(n-M)_k and yield sigma_n^2=A_n/G+C_tautau,n-C_11,n/G1-C_00,n/G0, so only Johnson degree one survives after multiplication by G. The pure-degree special case fixes the correction's sign; arm sample variances converge to V_z; and exhaustive enumeration verifies the eight-unit witness over 630 design points. The additive no-interference impossibility transfers upward to arbitrary bounded composition interference but does not extend the positive homogeneous theory to variable group sizes."
novelty_target: field
banked_novelty_tier: field
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: null
reusable: unknown
reraise_status: unknown
gap_reasons: []
reusable_artifacts:
  - Causalean/Mathlib/Combinatorics/JohnsonKneser/Basic.lean
  - Causalean/Mathlib/Combinatorics/JohnsonKneser/Harmonics.lean
  - Causalean/Mathlib/Combinatorics/JohnsonKneser/Kneser.lean
seeds_burned: []
proof_attempt_summary: |
  The run proved the exact finite-sample variance identity, dense projection correction,
  CR2 phase frontier, sparse ratio-consistency result, finite witness, and positive-density
  one-realization impossibility theorem. The initially missing Johnson–Kneser spectral theory
  was built as reusable Causalean substrate and integrated through an axiom-clean local adapter;
  all final proof obligations closed with no added assumptions or remaining sorries.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 341423239
  pipeline_claude_tokens: 36802463
  pipeline_tokens_consumed: 378225702
  total_tokens_consumed: null
banked_on: "2026-09-09"
---

# exp_dense_group_partition_projection_phase / v1 — Accepted

**Topic.** For fixed M>=2, uniformly draw G disjoint M-subsets from n units and completely randomize G1 groups, with bounded arbitrary composition interference and the PAME target. Derive the exact Kneser/Johnson variance identity and prove G Var(tauhat)=V1/p+V0/(1-p)-rho||Pi1(h1-h0)||^2+o(1) when MG/n->rho. Prove the exact scalar group-CR2 variance identity and its schedule-uniform expansion: at rho=0 the CR2 variance estimator is ratio-consistent under N/n->0 without an N^2/n condition, while at rho>0 its missing first-projection correction gives asymptotic conservativeness and ratio consistency exactly when that correction is negligible. This is a variance-estimation frontier only; claim no centered Gaussian limit, studentization law, or Wald coverage. Establish that no one-realization estimator is uniformly ratio-consistent for the exact variance over the full positive-density class, using the proved common-versus-independent Rademacher schedules, predictable-variation verification, high-probability diagonal selection, and equal observed-data mixtures. Verify the n=8,M=2,G=4 balanced witness with true variance 1/7 and expected CR2 2/7, and state the precise equal-group clubSandwich::vcovCR(type='CR2') consumer. The normalized Kneser eigenvalues are lambda_nk=(-1)^k(M)_k/(n-M)_k and yield sigma_n^2=A_n/G+C_tautau,n-C_11,n/G1-C_00,n/G0, so only Johnson degree one survives after multiplication by G. The pure-degree special case fixes the correction's sign; arm sample variances converge to V_z; and exhaustive enumeration verifies the eight-unit witness over 630 design points. The additive no-interference impossibility transfers upward to arbitrary bounded composition interference but does not extend the positive homogeneous theory to variable group sizes.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** F5 and fresh post-cleanup dual-model F4 passed at field; six headline theorems build with zero sorry/axiom debt and only standard Lean axioms.

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

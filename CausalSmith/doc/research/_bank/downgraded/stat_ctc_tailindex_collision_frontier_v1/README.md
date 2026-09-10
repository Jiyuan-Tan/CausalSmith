---
qid: stat_ctc_tailindex_collision_frontier
spec: v1
topic: "K1 Fix a bivariate positive-coefficient linear SCM with independent second-order regularly varying innovations, arbitrary common bodies, local tail-index gap Delta_n, and intermediate sequence k_n; target the finite-threshold CTC contrast, not unrestricted causal direction. K2 derive the exact-Pareto and class-level forward and reverse population collision curves on the intrinsic threshold coordinate and its Delta_n log(n/k_n) corollary, including the sharp scaled-Pareto endpoints. K3 characterize the feasible relation between the logarithmic mixture and root-k_n ordering scales, and prove that a four-coordinate summed-marginal local experiment is invalid because it omits a root-k_n common-index coordinate and order-k_n joint exceedance-overlap intensity. K4 certify the constant full-alphabet direction set as an exactly honest label-equivariant fallback and state only the nontrivial experiment/ambiguity obstructions supported by the model. The augmented paired experiment, nonconstant envelope-conditional honest set, and matching opposite-orientation ambiguity frontier remain explicit open questions requiring additional joint-process, likelihood, bias, and contiguity primitives."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: kernel_substituted
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - >-
    The positive results are sequential population collision curves for a finite-threshold contrast over a specially constructed triangular-array class; they provide neither observed-law orientation identification nor a sampling limit, rate, or uniform remainder for the empirical contrast.
  - >-
    The experiment theorem only disproves one four-coordinate summed-marginal representation by exhibiting omitted common-index variation and overlap covariance; it does not construct the augmented experiment or establish a general impossibility result.
  - >-
    The order-k_n covariance of the raw exceedance counts proves process overlap, but it does not prove a nonzero cross-covariance for the unspecified tangent scores dot_ell_{a,r}; derive that score-level cross term (or weaken the information-form conclusion).
  - >-
    The sole certified coverage result is the definition-tautological full-alphabet set, while no theorem gives a rate, limit law, nontrivial coverage result, or other frontier advance for the declared estimator hat_D_n; demote this fallback to scope prose or add a substantive Stat deliverable.
reusable_artifacts:
  - path: discovery/writeup.tex
    kind: other
    one_line: Sequential exact-Pareto and class-level forward/reverse CTC collision curves, feasible two-scale geometry, and the four-coordinate experiment obstruction.
  - path: discovery/core.json
    kind: witness
    one_line: Structured scaled-Pareto collision witnesses and proof-bearing theorem graph for future augmented-experiment work.
  - path: reviews/review_general.json
    kind: literature_map
    one_line: Final field-floor comparison against Leimenstoll-Schienle and the precise missing augmented paired-process frontier.
seeds_burned: []
proof_attempt_summary: |
  The run attempted a joint local tail-rank experiment, an honest adaptive
  direction set, and a matching ambiguity frontier across the two collision
  scales. It proved useful sequential population collision curves and exposed
  missing common-index and overlap coordinates, but did not derive the joint
  likelihood/process expansion, nonconstant honest procedure, or matching
  opposite-orientation lower bound. Two cold D0.5 reviews and the independent
  main validity gate therefore placed the honest result at subfield rather than
  the requested field tier.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 79560381
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-02"
---

# stat_ctc_tailindex_collision_frontier / v1 — Downgraded

**Topic.** K1 Fix a bivariate positive-coefficient linear SCM with independent second-order regularly varying innovations, arbitrary common bodies, local tail-index gap Delta_n, and intermediate sequence k_n; target the finite-threshold CTC contrast, not unrestricted causal direction. K2 derive the exact-Pareto and class-level forward and reverse population collision curves on the intrinsic threshold coordinate and its Delta_n log(n/k_n) corollary, including the sharp scaled-Pareto endpoints. K3 characterize the feasible relation between the logarithmic mixture and root-k_n ordering scales, and prove that a four-coordinate summed-marginal local experiment is invalid because it omits a root-k_n common-index coordinate and order-k_n joint exceedance-overlap intensity. K4 certify the constant full-alphabet direction set as an exactly honest label-equivariant fallback and state only the nontrivial experiment/ambiguity obstructions supported by the model. The augmented paired experiment, nonconstant envelope-conditional honest set, and matching opposite-orientation ambiguity frontier remain explicit open questions requiring additional joint-process, likelihood, bias, and contiguity primitives.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT (below the requested floor; achieved tier: subfield)

**Banking reason.** Second D0.5 cold review remained subfield (6.6) below the field floor (7); the field-tier upgrade requires new joint-process and inference primitives outside the frozen premises.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

The main validity gate confirmed that the remaining local cleanup findings are
tier-neutral. A future re-raise should reuse the population curves and witnesses,
but must supply the missing paired marked-process/QMD construction, a uniform CTC
bias and remainder bridge, a nonconstant honest direction set, and a same-class
opposite-orientation contiguity lower bound. Do not treat the raw exceedance-count
overlap covariance as a proved tangent-score cross term.

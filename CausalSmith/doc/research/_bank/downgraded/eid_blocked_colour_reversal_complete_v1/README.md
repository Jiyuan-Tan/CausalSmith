---
qid: eid_blocked_colour_reversal_complete
spec: v1
topic: "For every finite labelled causally sufficient linear Gaussian DAG with unrestricted positive noise variances and one coefficient per block of each target's parent partition, allowing singleton blocks, characterize equality of the full positive-definite covariance models. Prove that two blocked-colour states are equivalent exactly when they are connected by covered reversals whose reversed edge is a singleton block and whose endpoint partitions agree on their common parents, with the prescribed partition transport. Equivalently, prove the static criterion: common skeleton and unshielded colliders, identical nonsingleton parent-block families at every vertex, and fixed orientation for every edge joining vertices with unequal block families. Derive complete component enumeration, a shortest reversal path whose length is the number of disagreeing arrows, fixed-p generic Gaussian likelihood/BIC component recovery, and simultaneous inference for the component's finite causal-effect set. Do not broaden to unrestricted cross-target edge colourings or equate a compelled arrow with an identified coefficient. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Tangent supports at diagonal covariances recover each nonsingleton parent block; an exact sparse covariance separator forces every reversed edge to join equal endpoint block families; Chickering's monotone reversal theorem then supplies the proposed path. Exhaustive p=5 enumeration matched all 348631 states and 153462 static classes to move components, with exact separators and mixed-partition stress witnesses. UNRESOLVED BOTTLENECK: Independently audit tangent-support recovery and the arbitrary-reversed-edge sparse separator, especially extra target parents and simultaneous arrow changes, and verify the imported generic-faithfulness and monotone-transformation results. EARLY KILL TEST: Reproduce the exact separator on legal five-node pairs and audit the monotone induction; any full-model-equivalent pair with different nonsingleton blocks or a reversal across unequal endpoint families falsifies the theorem. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_blocked_colour_reversal_complete.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REVISE
proposal_promise_gap: "kernel_substituted"
reusable: unknown
reraise_status: retry
gap_reasons:
  - "[D0.5.G cold referee] delivered tier=subfield below novelty_target=field (floor=field)."
  - "That lemma is supplied without proof or a precise theorem-level citation, despite being the load-bearing bridge from equality of constrained covariance images to ordinary Markov equivalence."
  - "Discharge `lem:edge-coloured-model-equivalence-markov` by precisely citing the published corollary for edge-coloured DAGs and reproducing its short generic-faithfulness argument showing that equality of the two models forces equality of their DAG conditional-independence models."
reusable_artifacts:
  - "discovery/core.json — final 18-statement graph at main dd17f4a09626, including the tangent-support recovery, sparse reversed-edge separator, canonical PDAG lift, and exact enumeration results."
  - "discovery/solve_thm_complete_blocked_equivalence.json — solved complete-equivalence kernel and source receipts."
  - "discovery/solve_lem_exact_global_rational_effect_identity.json — exact rational-effect identity construction."
  - "discovery/gaps.json — verified literature map and open-problem inventory."
seeds_burned: []
proof_attempt_summary: |
  Discovery derived and independently audited a sound complete covariance-model equivalence
  characterization for the published singleton-permitting blocked superclass, together with a
  canonical PDAG lift, shortest legal reversal paths, exact-once enumeration, and fixed-p statistical
  consequences. The official cold D0.5.G referee nevertheless assigned subfield because the rendered
  note did not expose the precise Corollary 5.6 citation beside a load-bearing lemma; that citation and
  an independent attestation are present in core.json, so the remaining issue is citation visibility
  rather than a mathematical defect.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 43471583
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-07"
---

# eid_blocked_colour_reversal_complete / v1 — Downgraded

**Topic.** For every finite labelled causally sufficient linear Gaussian DAG with unrestricted positive noise variances and one coefficient per block of each target's parent partition, allowing singleton blocks, characterize equality of the full positive-definite covariance models. Prove that two blocked-colour states are equivalent exactly when they are connected by covered reversals whose reversed edge is a singleton block and whose endpoint partitions agree on their common parents, with the prescribed partition transport. Equivalently, prove the static criterion: common skeleton and unshielded colliders, identical nonsingleton parent-block families at every vertex, and fixed orientation for every edge joining vertices with unequal block families. Derive complete component enumeration, a shortest reversal path whose length is the number of disagreeing arrows, fixed-p generic Gaussian likelihood/BIC component recovery, and simultaneous inference for the component's finite causal-effect set. Do not broaden to unrestricted cross-target edge colourings or equate a compelled arrow with an identified coefficient. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Tangent supports at diagonal covariances recover each nonsingleton parent block; an exact sparse covariance separator forces every reversed edge to join equal endpoint block families; Chickering's monotone reversal theorem then supplies the proposed path. Exhaustive p=5 enumeration matched all 348631 states and 153462 static classes to move components, with exact separators and mixed-partition stress witnesses. UNRESOLVED BOTTLENECK: Independently audit tangent-support recovery and the arbitrary-reversed-edge sparse separator, especially extra target parents and simultaneous arrow changes, and verify the imported generic-faithfulness and monotone-transformation results. EARLY KILL TEST: Reproduce the exact separator on legal five-node pairs and audit the monotone induction; any full-model-equivalent pair with different nonsingleton blocks or a reversal across unequal endpoint families falsifies the theorem. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_blocked_colour_reversal_complete.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REVISE

**Banking reason.** D0.5.G cold referee: delivered tier=subfield below novelty_target=field; the load-bearing edge-coloured-model-equivalence lemma's precise Corollary 5.6 citation was not visible in the rendered note, despite being persisted and independently attested.

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

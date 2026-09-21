---
qid: pid_oracle_dtr_tree_diagonal_set
spec: v1
topic: "Sharp tree-diagonal capacity set for the full distribution of an oracle dynamic-treatment outcome. In a finite full-history SMART with known positive randomization and Y in {0,...,K-1}, target every pmf/CDF of M=max_d Y(d) compatible with the observed law under Shahn's FFRCISTG model. Prove the local maximum-coupling characterization q attainable iff F_q is below every action-marginal CDF and q(k)<=sum_a p_a(k); recurse it over the explicit treatment tree and prove both projection and an observed-law-preserving FFRCISTG lift including dormant branches and single-world independences. After intervention-reach rescaling, derive an O(K times tree-size) polyhedral formulation linear in observed multinomial probabilities, exact membership/support dual certificates, attaining samplers, strict cross-threshold nonrectangularity, and finite-sample whole-set confidence inversion by LP for the SMART-BD oracle-remission consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: monotone residual transport proves the local iff; reach-probability rescaling linearizes observed cells; local and two-stage reduced formulations matched 880 full response-type LP support checks to 8.9e-16, including a positive two-stage obstruction. Static copula and maximum-transport results are occupied, but no recursive causal-set collision was found. UNRESOLVED BOTTLENECK: prove every recursively feasible array embeds into the complete FFRCISTG counterfactual system while preserving dormant-branch consistency and single-world independences. EARLY KILL TEST: explicitly project the full two-stage binary-action, binary-response, three-outcome FFRCISTG model and compare it with the reduced formulation on heterogeneous positive kernels; any reduced feasible point without a valid lift should pivot or stop. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_oracle_dtr_tree_diagonal_set.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "standard FFRCISTG single-world conditional laws do not imply an a.s. shared cross-regime prefix, so Theta(P) subset proj_q R(P) is unproved"
  - "The cross-world-prefix objection is load-bearing and cannot be repaired under ordinary FFRCISTG without adding a crux-encoding prefix-consistency assumption."
  - "The strongest faithful same-assumption salvage is the constructive-inner/Shahn-outer sandwich, which the cold referee grades subfield with paper_score_ceiling 6.9 below the field threshold 7.4 and explicitly marks salvageable=false."
reusable_artifacts:
  - discovery/core.json  # local maximum-law theorem, constructive inner polytope, and cited-source attestation
  - discovery/solve_thm_compact_formulation.tex  # compact LP certificate and sampler derivation
  - discovery/gaps.json  # literature map and comparator positioning
  - discovery/writeup.tex  # full attempted projection/lift argument and honest residual obstruction
seeds_burned:
  - index: 0
    one_liner: "Tree-diagonal capacity theorem for the full oracle law"
    reason: "The sole angle cannot reach field tier without adding a crux-encoding cross-regime prefix-consistency assumption."
proof_attempt_summary: |
  The run proved the local discrete maximum-law characterization and built a tree-linear
  constructive inner polytope with exact LP certificates and samplers. The advertised equality
  with the full FFRCISTG identified set collapsed because its reverse inclusion requires shared
  cross-regime prefixes that ordinary single-world FFRCISTG assumptions do not supply; adding
  them would encode the crux. What remains sound is the subfield sandwich between the constructive
  inner polytope, the causal identified set, and Shahn's outer envelope, plus the K=3 inner-versus-
  outer strictness witness; no formalization stage ran under the temporary freeze.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 25036580
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 25036580
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# pid_oracle_dtr_tree_diagonal_set / v1 — Downgraded

**Topic.** Sharp tree-diagonal capacity set for the full distribution of an oracle dynamic-treatment outcome. In a finite full-history SMART with known positive randomization and Y in {0,...,K-1}, target every pmf/CDF of M=max_d Y(d) compatible with the observed law under Shahn's FFRCISTG model. Prove the local maximum-coupling characterization q attainable iff F_q is below every action-marginal CDF and q(k)<=sum_a p_a(k); recurse it over the explicit treatment tree and prove both projection and an observed-law-preserving FFRCISTG lift including dormant branches and single-world independences. After intervention-reach rescaling, derive an O(K times tree-size) polyhedral formulation linear in observed multinomial probabilities, exact membership/support dual certificates, attaining samplers, strict cross-threshold nonrectangularity, and finite-sample whole-set confidence inversion by LP for the SMART-BD oracle-remission consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: monotone residual transport proves the local iff; reach-probability rescaling linearizes observed cells; local and two-stage reduced formulations matched 880 full response-type LP support checks to 8.9e-16, including a positive two-stage obstruction. Static copula and maximum-transport results are occupied, but no recursive causal-set collision was found. UNRESOLVED BOTTLENECK: prove every recursively feasible array embeds into the complete FFRCISTG counterfactual system while preserving dormant-branch consistency and single-world independences. EARLY KILL TEST: explicitly project the full two-stage binary-action, binary-response, three-outcome FFRCISTG model and compare it with the reduced formulation on heterogeneous positive kernels; any reduced feasible point without a valid lift should pivot or stop. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_oracle_dtr_tree_diagonal_set.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** D0.5 field-floor failure: standard FFRCISTG does not imply the shared cross-regime prefixes required for the claimed sharp projection; the strongest honest same-assumption result is a subfield inner/outer sandwich (paper-score ceiling 6.9 below 7.4).

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

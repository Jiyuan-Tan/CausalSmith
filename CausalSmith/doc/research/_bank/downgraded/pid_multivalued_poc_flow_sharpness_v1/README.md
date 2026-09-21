---
qid: pid_multivalued_poc_flow_sharpness
spec: v1
topic: "Constructive all-alphabet sharpness of multivalued conjunction probabilities of causation. For finite X with m treatment levels and finite potential outcomes with r labels, consistency, and compatible common-population observational and one-treatment intervention margins, prove the published Shu–Wang–Li scalar conjunction bounds are attained for every real input. Derive an exact indicator coarsening and categorical lifting; construct the upper endpoint by intersection packing and the lower endpoint by a complete bipartite max-flow with diagonal edges removed and a proved residual-failure filling invariant; show mixtures fill the entire identified interval. For rational input give O(mr+k log k) endpoint evaluation, polynomial-time polynomial-support exact primal SCM laws, active-affine/min-cut dual certificates, and audited bit complexity. Add polynomial-size block-multinomial confidence-region inversion with uniform finite-sample coverage, while crediting Cheng–Mao–Pearl–Li for directional inference. Position against Shu–Wang–Li, binary-only Xie–Li, generic response-signature LPs, and Harinen et al. as a common-population hypothetical customer-journey consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Two score-blind presolves independently derived the categorical lifting, intersection packing, diagonal-deleted cut formula, and the unused-capacity residual invariant. Fresh exact arithmetic reproduced every full categorical margin and endpoint in 954 laws, including zero rows, deterministic p_i=1 boundaries, the five-way tie, and m=40,r=3,k=30; 97,625 subset/positive-part configurations and 80 confidence-program comparisons found no failure. Unequal alphabets, repeated queried labels, k<m, proper/full subset cuts, and global/singleton lower cuts were explicitly exercised. Searches found no collision with the disclosed binary, partial-diagram, generic-LP, or inference follow-ups. UNRESOLVED BOTTLENECK: Independently formalize the finite-cell TAKE refinement lemma and audit polynomial support, denominator, and bit-complexity accounting across all zero-mass domains; no central theorem step is being assumed. EARLY KILL TEST: Reconstruct the singleton-lower, proper-subset-upper, five-way-tie, and p_i=1 endpoint laws with exact arithmetic and verify every observational/interventional cell, objective, and residual-failure invariant; any failure stops this framing. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_multivalued_poc_flow_sharpness.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "The delivered result remains one scalar query with conservative outer inference and no developed application; field recovery requires simultaneous multi-query or policy-utility sharpness plus stronger inference/application scope."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The contribution remains confined to one scalar conjunction under common-population consistency-only margins and does not establish simultaneous sharpness for multiple response patterns or policy utilities."
  - "The support result determines only the order between mr and 2mr-m, while the confidence procedure is conservative and has no efficiency or width guarantee."
  - "These limitations and the absence of a developed application keep the package below flagship significance despite clearing the field-level floor."
reusable_artifacts:
  - discovery/core.json
  - discovery/solve_oeq_optimal_support_frontier.tex
  - discovery/solve_thm_algorithmic_certificates.tex
  - discovery/solve_thm_optimal_support_frontier_order.tex
  - discovery/writeup.tex
seeds_burned: []
proof_attempt_summary: |
  Discovery proved the complete sharp scalar interval, constructive endpoint laws,
  exact evaluation and certificates, and a certificate-preserving O(mr) support
  bound; the citation and mathematics panels passed. The field claim collapsed on
  scope rather than correctness: reaching the floor would require a new simultaneous
  multi-query or policy-utility result, stronger inference, and a developed application.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 17292147
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 17292147
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# pid_multivalued_poc_flow_sharpness / v1 — Downgraded

**Topic.** Constructive all-alphabet sharpness of multivalued conjunction probabilities of causation. For finite X with m treatment levels and finite potential outcomes with r labels, consistency, and compatible common-population observational and one-treatment intervention margins, prove the published Shu–Wang–Li scalar conjunction bounds are attained for every real input. Derive an exact indicator coarsening and categorical lifting; construct the upper endpoint by intersection packing and the lower endpoint by a complete bipartite max-flow with diagonal edges removed and a proved residual-failure filling invariant; show mixtures fill the entire identified interval. For rational input give O(mr+k log k) endpoint evaluation, polynomial-time polynomial-support exact primal SCM laws, active-affine/min-cut dual certificates, and audited bit complexity. Add polynomial-size block-multinomial confidence-region inversion with uniform finite-sample coverage, while crediting Cheng–Mao–Pearl–Li for directional inference. Position against Shu–Wang–Li, binary-only Xie–Li, generic response-signature LPs, and Harinen et al. as a common-population hypothetical customer-journey consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Two score-blind presolves independently derived the categorical lifting, intersection packing, diagonal-deleted cut formula, and the unused-capacity residual invariant. Fresh exact arithmetic reproduced every full categorical margin and endpoint in 954 laws, including zero rows, deterministic p_i=1 boundaries, the five-way tie, and m=40,r=3,k=30; 97,625 subset/positive-part configurations and 80 confidence-program comparisons found no failure. Unequal alphabets, repeated queried labels, k<m, proper/full subset cuts, and global/singleton lower cuts were explicitly exercised. Searches found no collision with the disclosed binary, partial-diagram, generic-LP, or inference follow-ups. UNRESOLVED BOTTLENECK: Independently formalize the finite-cell TAKE refinement lemma and audit polynomial support, denominator, and bit-complexity accounting across all zero-mass domains; no central theorem step is being assumed. EARLY KILL TEST: Reconstruct the singleton-lower, proper-subset-upper, five-way-tie, and p_i=1 endpoint laws with exact arithmetic and verify every observational/interventional cell, objective, and residual-failure invariant; any failure stops this framing. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_multivalued_poc_flow_sharpness.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5: sound sharp scalar conjunction interval, but paper_score_ceiling 7.0 is below the 7.4 field floor and no bounded same-scope repair can clear it.

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

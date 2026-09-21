---
qid: scm_relational_unseenrow_bounds
spec: v1
topic: "Exact algebraic certification of one unseen shared row in a relational intervention. Work with finite fully observed Markovian relational SCMs, independent ground noises, type-shared finite conditional mechanisms, compatible positive rational source laws, acyclic target groundings, and one target-relevant unsupported binary context row q in [0,1]. Given the explicit dense rational target polynomial F(q) and source tables, prove the sharp set F([0,1]), compute exact algebraic endpoints by derivative-root isolation and sign comparison, and serialize common finite-noise endpoint RSCMs with polynomial-size checkable certificates. For sampled supported rows, use simultaneous rational confidence boxes and a labeled conservative occurrence-coupling inflation; do not claim exact multivariate projection. Consumer: Ejaz--Bareinboim RelationalCausalModels Experiment 6.1 N3 traffic query, whose fitted point must be accompanied by the certified sharp [0,1] range. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Repeated shared-row factorization gives F(q); exact arithmetic checked F(q)=1/4+q/2-q^3/3 with range [1/4,1/4+sqrt(2)/6], rejected the extraneous conjugate, reproduced all source assignments, and enumerated common endpoint models. A finite breakpoint construction uses at most two irrational noise masses for the unsupported row, and a maximal-coupling telescoping argument gives delta=min(1,sum_r m_r epsilon_r) for conservative whole-set coverage. Tests covered boundary/repeated roots, ties, incompatible sources, untied occurrences, output-size accounting, nuisance-vertex failure, and generic single-parameter model-checking collisions. UNRESOLVED BOTTLENECK: Prove soundness, completeness, polynomial size, and checking cost for one fixed serialized certificate grammar linking derivative roots to selected endpoint values through ties, boundary coincidences, and algebraic threshold comparisons. EARLY KILL TEST: Implement an independent producer/checker for the cubic forest; it must accept both source-reproducing endpoint models and [1/4,1/4+sqrt(2)/6] while rejecting the conjugate endpoint and any certificate omitting a positive critical point. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_relational_unseenrow_bounds.md"
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "The proposed operational checker, serialized cubic tests, and N3 certificate remain undelivered, and even their completion would repair rigor without creating a field-tier theorem."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "tier=incremental < floor=field (target=field) and NOT salvageable in scope"
  - "The TL;DR and project justification advertise a sound, complete, polynomial-size skeptical certificate, but Check is defined by saying that it verifies semantic conclusions such as incidence exhaustiveness, candidate exhaustiveness, exact algebraic links, and model validity; the soundness proof then infers those same conclusions from acceptance."
  - "The cubic proposition does not deliver the promised independent producer/checker or a serialized certificate: it invokes the abstract completeness theorem and argues informally that malformed records would be rejected."
  - "What remains proved is a narrow fully Markovian product-simplex image and endpoint-attainment result, routine univariate extremization, and a conservative coupling enclosure, with no delivered N3 certificate or application evidence."
reusable_artifacts:
  - "discovery/core.json — maximized structural theorem graph, including finite-many-row sharpness and the exhaustive-Ictx obstruction"
  - "discovery/solve_thm_sharp_one_row.tex — one-row polynomial-image and endpoint proof"
  - "discovery/solve_thm_assignment_incidence_obstructs_width_compiler.tex — width-zero exponential-output witness for the frozen grammar"
  - "discovery/solve_thm_confidence_enclosure.tex — multiplicative occurrence-coupling enclosure"
  - "discovery/proto_core.json — proposal literature map, seed comparisons, and re-anchor candidates"
seeds_burned:
  - index: 0
    one_liner: "A fixed skeptical certificate grammar for exact one-unseen-row relational causal bounds"
    reason: "The selected fixed-scope certificate package remained incremental at D0.5; field tier requires a materially new circuit-level compiler or tied-versus-untied structural frontier."
proof_attempt_summary: |
  The run derived an exact product-simplex image with finite-noise endpoint witnesses, specialized it to one-row univariate algebraic bounds, and added a multiplicative occurrence-coupling enclosure. The field-tier certificate headline collapsed because the checker remained a semantic specification rather than an executable verified grammar, while the cubic transaction and N3 artifact were not delivered; completing those items would still be artifact completion at subfield scale. A future field attempt must re-anchor around a compact circuit-level compiler/checker theorem or a structural frontier for tied relational mechanisms versus untied canonical relaxations.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 32381578
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 32381578
  total_tokens_consumed: null
banked_on: "2026-09-15"
---

# scm_relational_unseenrow_bounds / v1 — Downgraded

**Topic.** Exact algebraic certification of one unseen shared row in a relational intervention. Work with finite fully observed Markovian relational SCMs, independent ground noises, type-shared finite conditional mechanisms, compatible positive rational source laws, acyclic target groundings, and one target-relevant unsupported binary context row q in [0,1]. Given the explicit dense rational target polynomial F(q) and source tables, prove the sharp set F([0,1]), compute exact algebraic endpoints by derivative-root isolation and sign comparison, and serialize common finite-noise endpoint RSCMs with polynomial-size checkable certificates. For sampled supported rows, use simultaneous rational confidence boxes and a labeled conservative occurrence-coupling inflation; do not claim exact multivariate projection. Consumer: Ejaz--Bareinboim RelationalCausalModels Experiment 6.1 N3 traffic query, whose fitted point must be accompanied by the certified sharp [0,1] range. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Repeated shared-row factorization gives F(q); exact arithmetic checked F(q)=1/4+q/2-q^3/3 with range [1/4,1/4+sqrt(2)/6], rejected the extraneous conjugate, reproduced all source assignments, and enumerated common endpoint models. A finite breakpoint construction uses at most two irrational noise masses for the unsupported row, and a maximal-coupling telescoping argument gives delta=min(1,sum_r m_r epsilon_r) for conservative whole-set coverage. Tests covered boundary/repeated roots, ties, incompatible sources, untied occurrences, output-size accounting, nuisance-vertex failure, and generic single-parameter model-checking collisions. UNRESOLVED BOTTLENECK: Prove soundness, completeness, polynomial size, and checking cost for one fixed serialized certificate grammar linking derivative roots to selected endpoint values through ties, boundary coincidences, and algebraic threshold comparisons. EARLY KILL TEST: Implement an independent producer/checker for the cubic forest; it must accept both source-reproducing endpoint models and [1/4,1/4+sqrt(2)/6] while rejecting the conjugate endpoint and any certificate omitting a positive critical point. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_relational_unseenrow_bounds.md

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5: tier=incremental < floor=field and NOT salvageable in scope; paper_score_ceiling 5.5 < 7.4.

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

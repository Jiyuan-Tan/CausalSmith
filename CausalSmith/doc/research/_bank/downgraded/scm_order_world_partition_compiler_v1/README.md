---
qid: scm_order_world_partition_compiler
spec: v1
topic: "For finite ordered SCMs with explicitly listed finite alphabets, unrestricted complete-predecessor functions, and arbitrary shared exogenous variation, prove that the equality partition of h factual/intervention-world complete prefixes is an exact continuation state. Derive representative transitions deciding one explicit unnested conjunction in Bell(h) * 3^((h-1)/3) * poly(input) time and an explicit rational combination of r conjunctions in Bell(h) * 2^r * (r+1)^(h-1) * poly(input) time, with alphabet size absent from the exponential. Reconstruct sparse response rows plus defaults, attain sharp observational cell-sum endpoints with one exogenous atom per positive-mass cell, and preserve joint term dependence. Prove a scoped separation on binary S<T<X1<...<Xn<Y: factual zero, A=do(S=1), B=do(S=1,T=1), and query T_A=0, all X_i,A=0, Y_B=1 leave 2^n accepting numeric B histories after every pin but one partition state per layer. Charge dense input reading and explicit unnesting; exclude sparse prescribed graphs, independence restrictions, cycles, and claims about all reduced MDDs. Credit Halpern's certificate/hardness and Rossetto--Antonucci's cell-sum construction. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Informal proofs establish exact partition continuation, complete representative transitions, both transition bounds, joint truth flags, sparse traceback, false-bit handling, and cellwise attainment. Existing checks passed 119,100 local transitions, 18,486 joint cell problems, 1,200 mixed-alphabet cases, and 192 NDE cases. A fresh independent pass added 1,414 same-partition suffix-support and 1,369 partition-plus-flags truth-support comparisons, including all 32,768 binary four-variable response systems. Actual pinned copid query classes and builds produced three normalized contexts and 2^n accepting pre-Y prefixes for n=1 through 4. Contradictory/repeated terms, empty conjunctions, singleton and exhausted alphabets, cross-block constants, false-bit asymmetry, sparse/dense inputs, structural versus sample zeros, and the prescribed-sparse-graph counterexample were checked. UNRESOLVED BOTTLENECK: No core theorem implication remains unresolved; the principal risk is an unlocated equality-abstraction specialization with the same causal h-context theorem, followed by production implementation and formal verification. EARLY KILL TEST: Compare complete numeric suffix supports for histories sharing a partition and terminal truth supports for histories sharing partition plus flags across mixed alphabets and query constants; any mismatch kills the quotient, and a literal prior theorem with these bounds forces a novelty pivot. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_order_world_partition_compiler.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "Field-tier lift requires a sparse-graph or multi-regime extension, or materially new competitive implementation and benchmark evidence; current in-scope hygiene repairs do not move the tier."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The Bell(h) theorem is confined to unrestricted complete-predecessor mechanisms and does not extend to prescribed sparse graphs, factorized exogeneity, cycles, or succinct nested queries."
  - "The only demonstrated computational separation is against a deliberately path-retaining numeric-history baseline, while no implementation or benchmark establishes gains over competitive reduced representations on substantive counterfactual-bound problems."
  - "D0.5.G projected paper-score gate: paper_score_ceiling 6.5 < 7.4, so the graded tier 'field' is capped at 'subfield'."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_joint_score_compiler.json
  - discovery/solve_thm_residual_partition_minimality.json
  - discovery/solve_oeq_residual_minimality.json
seeds_burned: []
proof_attempt_summary: |
  Discovery derived and independently math-checked exact equality-partition continuation,
  alphabet-independent single and joint compiler bounds, sparse attaining witnesses, sharp
  cellwise endpoints, and Bell(h) residual-state minimality. Several false Bell(h-1) and
  concrete-common-table residual formulations were rejected and repaired before the final math
  review passed. The package nevertheless missed the field novelty floor because its model scope
  and baseline-only separation lacked a sparse/multi-regime extension or competitive implementation evidence.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 26070329
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 26070329
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# scm_order_world_partition_compiler / v1 — Downgraded

**Topic.** For finite ordered SCMs with explicitly listed finite alphabets, unrestricted complete-predecessor functions, and arbitrary shared exogenous variation, prove that the equality partition of h factual/intervention-world complete prefixes is an exact continuation state. Derive representative transitions deciding one explicit unnested conjunction in Bell(h) * 3^((h-1)/3) * poly(input) time and an explicit rational combination of r conjunctions in Bell(h) * 2^r * (r+1)^(h-1) * poly(input) time, with alphabet size absent from the exponential. Reconstruct sparse response rows plus defaults, attain sharp observational cell-sum endpoints with one exogenous atom per positive-mass cell, and preserve joint term dependence. Prove a scoped separation on binary S<T<X1<...<Xn<Y: factual zero, A=do(S=1), B=do(S=1,T=1), and query T_A=0, all X_i,A=0, Y_B=1 leave 2^n accepting numeric B histories after every pin but one partition state per layer. Charge dense input reading and explicit unnesting; exclude sparse prescribed graphs, independence restrictions, cycles, and claims about all reduced MDDs. Credit Halpern's certificate/hardness and Rossetto--Antonucci's cell-sum construction. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Informal proofs establish exact partition continuation, complete representative transitions, both transition bounds, joint truth flags, sparse traceback, false-bit handling, and cellwise attainment. Existing checks passed 119,100 local transitions, 18,486 joint cell problems, 1,200 mixed-alphabet cases, and 192 NDE cases. A fresh independent pass added 1,414 same-partition suffix-support and 1,369 partition-plus-flags truth-support comparisons, including all 32,768 binary four-variable response systems. Actual pinned copid query classes and builds produced three normalized contexts and 2^n accepting pre-Y prefixes for n=1 through 4. Contradictory/repeated terms, empty conjunctions, singleton and exhausted alphabets, cross-block constants, false-bit asymmetry, sparse/dense inputs, structural versus sample zeros, and the prescribed-sparse-graph counterexample were checked. UNRESOLVED BOTTLENECK: No core theorem implication remains unresolved; the principal risk is an unlocated equality-abstraction specialization with the same causal h-context theorem, followed by production implementation and formal verification. EARLY KILL TEST: Compare complete numeric suffix supports for histories sharing a partition and terminal truth supports for histories sharing partition plus flags across mixed alphabets and query constants; any mismatch kills the quotient, and a literal prior theorem with these bounds forces a novelty pivot. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_order_world_partition_compiler.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G cold referee: delivered tier=subfield below novelty_target=field; paper_score_ceiling 6.5 < 7.4 and not salvageable within scope. Dedicated math review passed with no findings.

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

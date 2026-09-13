---
qid: eid_fanin_numedge_frontier
spec: v1
topic: "Sharp directed-fan-in frontier for numerical edge identification in confounded linear SEMs. Input: an acyclic mixed graph, rational feasible positive-definite covariance, and a queried directed coefficient; the fiber consists of all supported structural matrices whose induced noise covariance respects the bidirected graph. Prove a deterministic polynomial-bit algorithm at maximum directed indegree one using Möbius components plus singular 2-SAT clauses, returning a unique rational value, two unequal feasible witnesses, or a componentwise quadratic nonconstant-curve certificate. Prove promise universal-real completeness at indegree two via a fiber-bijective private-parent and occurrence-hub compiler with rational strictly diagonally dominant covariance. Preserve MIIVsem as the numerical-identification consumer and treat covariance-confidence-set inversion as secondary. PRESOLVE EVIDENCE REQUIRING VERIFICATION: indegree-one bi-affine equations were reduced to invertible Möbius components with quadratic-or-cofinite domains and singular equality disjunctions; indegree-two addition, multiplication, copying, repeated inputs, covariance-slot separation, and positive-definite witnesses passed bounded exact checks over 48 Möbius relations, 2,286 singular assignments, and two complete compilers. A global primitive element can have exponential degree, so certificates must remain componentwise quadratic. UNRESOLVED BOTTLENECK: independently audit the arbitrary-input component normalization and 2-SAT equivalence, including poles and every singular degeneration, then verify a complete selector-circuit compiler. EARLY KILL TEST: compare the full component algorithm against real-algebraic elimination on bounded degenerate rational systems and eliminate every copy equation in a circuit using all primitives; any extra fiber branch kills the frontier. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_fanin_numedge_frontier.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "tier_genuinely_below"
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - >-
    The proved contribution is an exact rational-covariance frontier: deterministic
    polynomial-time numerical edge identification at maximum indegree one and
    promise universal-real completeness at indegree two on bounded directed
    components.
  - >-
    Its hard-side novelty is specifically the bounded-fan-in replacement of
    Dörfler et al.'s storage star; general universal-real hardness and fiber
    bijectivity are inherited, while the K_G results are padding consequences
    rather than an additional identification frontier.
  - >-
    The result supplies no stability analysis for approximate covariances,
    finite-sample inference, implementation, or substantive MIIVsem
    demonstration, so the named practical consumer is not supported by delivered
    evidence.
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_fanin_one_algorithm.json
  - discovery/solve_thm_fanin_two_completeness.json
  - discovery/solve_thm_few_two_parent_fixed_parameter_hardness.json
  - discovery/solve_thm_zero_two_parent_hardness.json
  - reviews/review_math.json
  - reviews/review_general.json
seeds_burned: []
proof_attempt_summary: |
  The run completed and independently reviewed an exact all-covariance fan-in-one
  classification with constructive certificates, a fiber-bijective fan-in-two
  hardness compiler on bounded depth-one components, and exact-fiber padding
  consequences for fixed K_G. The mathematical and rubric reviewers passed the
  package, but the cold significance referee capped it at subfield because the
  hard-side delta is narrow and the package does not deliver approximate-covariance
  stability, finite-sample inference, implementation, or applied validation.
  Those additions remain possible follow-on work, but require new research beyond
  an in-scope derivation repair.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 13624663
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 13624663
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# eid_fanin_numedge_frontier / v1 — Downgraded

**Topic.** Sharp directed-fan-in frontier for numerical edge identification in confounded linear SEMs. Input: an acyclic mixed graph, rational feasible positive-definite covariance, and a queried directed coefficient; the fiber consists of all supported structural matrices whose induced noise covariance respects the bidirected graph. Prove a deterministic polynomial-bit algorithm at maximum directed indegree one using Möbius components plus singular 2-SAT clauses, returning a unique rational value, two unequal feasible witnesses, or a componentwise quadratic nonconstant-curve certificate. Prove promise universal-real completeness at indegree two via a fiber-bijective private-parent and occurrence-hub compiler with rational strictly diagonally dominant covariance. Preserve MIIVsem as the numerical-identification consumer and treat covariance-confidence-set inversion as secondary. PRESOLVE EVIDENCE REQUIRING VERIFICATION: indegree-one bi-affine equations were reduced to invertible Möbius components with quadratic-or-cofinite domains and singular equality disjunctions; indegree-two addition, multiplication, copying, repeated inputs, covariance-slot separation, and positive-definite witnesses passed bounded exact checks over 48 Möbius relations, 2,286 singular assignments, and two complete compilers. A global primitive element can have exponential degree, so certificates must remain componentwise quadratic. UNRESOLVED BOTTLENECK: independently audit the arbitrary-input component normalization and 2-SAT equivalence, including poles and every singular degeneration, then verify a complete selector-circuit compiler. EARLY KILL TEST: compare the full component algorithm against real-algebraic elimination on bounded degenerate rational systems and eliminate every copy equation in a circuit using all primitives; any extra fiber branch kills the frontier. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_fanin_numedge_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** The proved exact rational-covariance frontier is sound, but the hard-side novelty is the bounded-fan-in replacement of Dörfler et al.'s storage star; without stability, finite-sample inference, implementation, or substantive MIIVsem evidence, the cold referee capped it at subfield (7.0), below the field floor (7.4).

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

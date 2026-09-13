---
qid: scm_structsimp_exogenous_frontier
spec: v1
topic: "Exogenous-structure tractability frontier for Beckers structural-simplification actual causation. Fix a finite acyclic total nondeterministic SCM with explicit local tables, a specified actual solution, singleton X=x and Y=y events, and nonnegative rational edge-deletion costs. Under the full-graph reachability-closed and actualized-refinement legality rules, prove that full causal polyforests admit an exact minimum-cost value-path certificate: retained parents hit every bad-row difference support, safe relations compose along the unique path, and an O(L)-arithmetic dynamic program with polynomial bit complexity returns a positive witness, optimum certificate, or separating cut. Prove NP-completeness even for deterministic binary SCMs whose endogenous graph is one directed chain, actual world is zero, and total indegree is at most four, using shared exogenous selector roots and clause gates. Do not claim general treewidth FPT or unrestricted parsimonious certificate counting. Consumer: an explicit-support Beckers backend for the `actualcauses` Python package. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Independent derivations proved the local hitting equivalence, safe minimal-support transitions, forest completion and exact optimum, rational bit bounds, NP membership, and every selector/clause implication of the chain hardness reduction. Checks covered 52,488 local instances, 3,420 forest queries (2,467 ternary), 196 SAT instances, full state/edge cases, and the exogenous triangle counterexample to endogenous-only propagation. Classical HP tree and complexity results do not supply the Beckers-specific full-versus-endogenous separation. Normalized certificates, not unrestricted witnesses, carry the bijection. UNRESOLVED BOTTLENECK: Prove the complete arbitrary-domain compiler and certificate verifier extensionally equal to canonical Beckers causation and minimum deletion cost, including actual-row freezing and topological completion, within the stated explicit-input bound. EARLY KILL TEST: Compare compiler verdicts, optima, and all certificate types with exhaustive legal-edge and alternate-state enumeration on every three-vertex full forest with domains at most three, a fixed five-vertex mixed-domain rational-cost batch, and the exogenous triangle; any mismatch stops extension. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_structsimp_exogenous_frontier.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: null
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - >-
    The repeated description as a "frontier" is stronger than proved: the
    hardness construction is not shown to have relevant full-graph cycle rank
    two, or any fixed rank above one, so the note does not establish a
    cycle-rank dichotomy or maximal tractability boundary.
  - >-
    The positive and negative results are therefore separate tractability and
    hardness regimes rather than matching sides of the advertised parameterized
    frontier.
  - >-
    D0.5.G projected paper-score gate: paper_score_ceiling 7.2 < 7.4, so the
    graded tier 'field' is capped at 'subfield'.
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_chain_np_completeness.json
  - discovery/solve_oeq_full_unicycle_frontier.json
  - discovery/solve_thm_full_unicycle_polynomial_frontier.json
seeds_burned: []
proof_attempt_summary: |
  D0 proved exact minimum-cost optimization and replayable certificates when the
  relevant full-graph component has cycle rank at most one, together with
  NP-completeness for deterministic binary endogenous chains coupled by shared
  exogenous roots. Citation re-audit verified the bounded-clause SAT source, and
  the final math receipt passed; the package nevertheless missed the field floor
  because it did not connect the two regimes with a matching cycle-rank-two (or
  other fixed-rank-above-one) hardness construction. A future re-raise should
  reuse the proved rank-≤1 and chain gadgets and target that missing boundary.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 21968235
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 21968235
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# scm_structsimp_exogenous_frontier / v1 — Downgraded

**Topic.** Exogenous-structure tractability frontier for Beckers structural-simplification actual causation. Fix a finite acyclic total nondeterministic SCM with explicit local tables, a specified actual solution, singleton X=x and Y=y events, and nonnegative rational edge-deletion costs. Under the full-graph reachability-closed and actualized-refinement legality rules, prove that full causal polyforests admit an exact minimum-cost value-path certificate: retained parents hit every bad-row difference support, safe relations compose along the unique path, and an O(L)-arithmetic dynamic program with polynomial bit complexity returns a positive witness, optimum certificate, or separating cut. Prove NP-completeness even for deterministic binary SCMs whose endogenous graph is one directed chain, actual world is zero, and total indegree is at most four, using shared exogenous selector roots and clause gates. Do not claim general treewidth FPT or unrestricted parsimonious certificate counting. Consumer: an explicit-support Beckers backend for the `actualcauses` Python package. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Independent derivations proved the local hitting equivalence, safe minimal-support transitions, forest completion and exact optimum, rational bit bounds, NP membership, and every selector/clause implication of the chain hardness reduction. Checks covered 52,488 local instances, 3,420 forest queries (2,467 ternary), 196 SAT instances, full state/edge cases, and the exogenous triangle counterexample to endogenous-only propagation. Classical HP tree and complexity results do not supply the Beckers-specific full-versus-endogenous separation. Normalized certificates, not unrestricted witnesses, carry the bijection. UNRESOLVED BOTTLENECK: Prove the complete arbitrary-domain compiler and certificate verifier extensionally equal to canonical Beckers causation and minimum deletion cost, including actual-row freezing and topological completion, within the stated explicit-input bound. EARLY KILL TEST: Compare compiler verdicts, optima, and all certificate types with exhaustive legal-edge and alternate-state enumeration on every three-vertex full forest with domains at most three, a fixed five-vertex mixed-domain rational-cost batch, and the exogenous triangle; any mismatch stops extension. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_structsimp_exogenous_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** Cold-tier verdict: tier=subfield; target/floor=field; paper_score_ceiling=7.2 < ceiling_for_field=7.4; salvageable=false; improvement_directive=null; ceiling_directive=null.

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

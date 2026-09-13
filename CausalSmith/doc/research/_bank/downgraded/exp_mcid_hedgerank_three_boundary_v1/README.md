---
qid: exp_mcid_hedgerank_three_boundary
spec: v1
topic: "First-nonzero residual-hedge-rank frontier for minimum-cost causal experiment design. In finite simple bow-free semi-Markovian ADMGs with singleton target s and positive rational intervention costs, classify four-vertex hedges as complementary directed and bidirected spanning paths and prove r<=2 is hedge-free. For every ordered simple source graph H, use vertices x_u and one private guard z_e per edge e={u,v}, edges x_u->x_v->z_e->s, z_e<->x_u, and global s<->x_u spokes to prove the minimal residual-hedge clutter is exactly {{x_u,x_v,z_e}:e in E(H)}. Transfer unit-cost vertex cover to obtain NP/APX hardness at r=3 on bidirected trees of radius two. Prove a polynomial weighted factor-two LP rounding theorem, matching integrality-gap supremum two, and UGC-conditional (2-epsilon) hardness. Add promised-rank enumeration, scoped bounded-cardinality search, and an optimizer-or-rank-violation interface; do not claim unrestricted rank recognition or unconstrained weighted 3^k optimization. Consumer: Elahi et al.'s RC2/Gurobi workflow and Akbari et al.'s min_cost_intervention software. PRESOLVE EVIDENCE REQUIRING VERIFICATION: For every ordered H, every hedge contains a suffix x_v->z_e->s and bidirected connectivity forces its designated x_u; every intended triple is a four-vertex hedge. Guard replacement preserves vertex-cover optimum with unit costs. Edge counting classifies the first bow-free singleton hedge rank, parent/spouse rounding gives factor two, and complete-graph expansions match the LP gap. Exhaustive checks covered all 1,099 source graphs through five vertices and 1,900,363 residual subsets, plus K3,3 and the triangular prism; no unintended minimal hedge appeared. Rank-four and weighted-cardinality counterexamples removed two overclaims. UNRESOLVED BOTTLENECK: Independently or formally verify the universal reverse-inclusion theorem and rank-three parent/spouse rounding argument; the draft has complete informal proofs but is not Lean-checked. EARLY KILL TEST: Reimplement ancestry/connectivity enumeration independently through five source vertices and the named cubic cases; any hedge containing no intended triple kills the reduction. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_mcid_hedgerank_three_boundary.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "tier_genuinely_below"
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The proved algorithmic frontier is promise-based: the factor-two algorithm and exact LP-gap result require r(G,s) <= 3, while recognizing that promise on an arbitrary input remains open."
  - "The unconditional lower results are NP/APX hardness; the matching (2-epsilon) approximation threshold is conditional on UGC and established through the narrower unit-cost private-guard subclass."
  - "The causal-identification interpretation relies on the imported hedge-hitting equivalence, and the package provides no solver benchmarks demonstrating the asserted benefit to the named RC2/Gurobi workflows."
  - "D0.5.G projected paper-score gate: paper_score_ceiling 6.8 < 7.2, so the graded tier 'field' is capped at 'subfield'."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - formalization/plan.json
seeds_burned: []
proof_attempt_summary: |
  Discovery proved the rank-three hedge classification, private-guard realization,
  objective-preserving hardness, weighted factor-two rounding, and exact LP-gap
  frontier, and both mathematical and decision reviews passed. Formalization exposed
  and repaired the missing vertex-order, complexity-model, and positive-cost dependency
  edges; the final normalized novelty review nevertheless capped the sound package at
  subfield because promise recognition remains open, tightness is UGC-conditional on a
  narrower subclass, the identification bridge is imported, and no solver benchmarks
  were delivered.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 61171912
  pipeline_claude_tokens: 61614785
  pipeline_tokens_consumed: 122786697
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# exp_mcid_hedgerank_three_boundary / v1 — Downgraded

**Topic.** First-nonzero residual-hedge-rank frontier for minimum-cost causal experiment design. In finite simple bow-free semi-Markovian ADMGs with singleton target s and positive rational intervention costs, classify four-vertex hedges as complementary directed and bidirected spanning paths and prove r<=2 is hedge-free. For every ordered simple source graph H, use vertices x_u and one private guard z_e per edge e={u,v}, edges x_u->x_v->z_e->s, z_e<->x_u, and global s<->x_u spokes to prove the minimal residual-hedge clutter is exactly {{x_u,x_v,z_e}:e in E(H)}. Transfer unit-cost vertex cover to obtain NP/APX hardness at r=3 on bidirected trees of radius two. Prove a polynomial weighted factor-two LP rounding theorem, matching integrality-gap supremum two, and UGC-conditional (2-epsilon) hardness. Add promised-rank enumeration, scoped bounded-cardinality search, and an optimizer-or-rank-violation interface; do not claim unrestricted rank recognition or unconstrained weighted 3^k optimization. Consumer: Elahi et al.'s RC2/Gurobi workflow and Akbari et al.'s min_cost_intervention software. PRESOLVE EVIDENCE REQUIRING VERIFICATION: For every ordered H, every hedge contains a suffix x_v->z_e->s and bidirected connectivity forces its designated x_u; every intended triple is a four-vertex hedge. Guard replacement preserves vertex-cover optimum with unit costs. Edge counting classifies the first bow-free singleton hedge rank, parent/spouse rounding gives factor two, and complete-graph expansions match the LP gap. Exhaustive checks covered all 1,099 source graphs through five vertices and 1,900,363 residual subsets, plus K3,3 and the triangular prism; no unintended minimal hedge appeared. Rank-four and weighted-cardinality counterexamples removed two overclaims. UNRESOLVED BOTTLENECK: Independently or formally verify the universal reverse-inclusion theorem and rank-three parent/spouse rounding argument; the draft has complete informal proofs but is not Lean-checked. EARLY KILL TEST: Reimplement ancestry/connectivity enumeration independently through five source vertices and the named cubic cases; any hedge containing no intended triple kills the reduction. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_mcid_hedgerank_three_boundary.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** Latest normalized D0.5.G: paper_score_ceiling 6.8 < 7.2 field bar; math and decision panels pass, but no faithful same-scope material repair exists.

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

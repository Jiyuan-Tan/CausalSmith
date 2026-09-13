---
qid: scm_minhedge_reliability_hypergraph
spec: v1
topic: "Minimal edge-support obstruction hypergraphs for exact reliability of uncertain causal identification. Given a topologically ordered ADMG envelope with deterministic backbone edges, independently uncertain directed/bidirected edges, and a fixed query P_x(y), define O_XY as all inclusion-minimal uncertain-edge supports on which ordinary ID fails. Let b be the largest bidirected district of the full envelope and tau the incidence-treewidth of O_XY. Prove a canonical sparse-hedge-core algorithm enumerates O_XY with 2^{O(b log b)} polynomial preprocessing and delay, with coverage, global minimality, duplicate suppression, and exhaustion; include a complete polynomial-delay construction for all b<=2 envelopes by deterministic-path projection and induced-path branching. Prove R_XY(p)=product_e(1-p_e) I_O((p_e/(1-p_e))_e), compute R and every partial derivative in 2^{O(tau)} polynomial exact-arithmetic time from an incidence decomposition, and prove exact successful-realization counting at p_e=1/2 is #P-complete already at b=2. Consumer: Akbari et al.'s uncertain-ADMG sampler and edgeID workflow, which would report total identifiability probability, minimal failure combinations, and graph-refinement sensitivities instead of only one selected identifiable realization. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Informal derivations show that reachable-district width b equals the largest bidirected district of the envelope; every hedge has a selected core with at most 2b-2 edges and at most |V|*2^{O(b log b)} core templates. The entire b<=2 class reduces to labeled DAG reachability, where deterministic-path projection and chord-deleting induced-path branching enumerate minimal uncertain-edge supports with polynomial delay. Exact checks covered 32,000 four-vertex queries, 1,024 source-star realizations, 729 ternary DAG envelopes, 400 random seven-vertex envelopes, and 4,096 transversal encodings. The normalized independence-polynomial identity, incidence-treewidth reliability/derivative dynamic program, and #P hardness already at b=2 were also derived. UNRESOLVED BOTTLENECK: Prove a canonical partial-support recursion for globally minimal multiple-root ancestry supports across competing sparse hedge cores with 2^{O(b log b)} preprocessing and worst-case delay, including deterministic projection, cross-core domination, duplicate suppression, and exhaustion. EARLY KILL TEST: Exhaustively compare the proposed root-ordered state and child partition against every minimal support on envelopes with at most six vertices, b<=3, and at most eight uncertain edges; any omission, duplicate, false live branch, or lost global minimality stops the compiler. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_minhedge_reliability_hypergraph.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The promised canonical partial-support recursion with worst-case accepted-output delay was not proved; it remained an open question while a weaker candidate-sensitive compiler was substituted."
reusable: unknown
reraise_status: unknown
gap_reasons:
  - "The proposal headlined a general-b 2^{O(b log b)}-preprocessing, accepted-output-delay compiler, but this theorem delivers only raw-Steiner-candidate-sensitive total time and leaves that delay object open; retitle/reposition the result around the weaker compiler (or prove the promised recursion)."
  - "The framing accurately distinguishes these proved results from the unresolved general-b delay claim, so there is no stale overclaim."
reusable_artifacts:
  - discovery/solve_tex/solve_thm_width_two_enumeration.tex
  - discovery/solve_thm_width_two_enumeration.json
  - discovery/solve_tex/solve_thm_canonical_enumeration.tex
  - discovery/core.json
seeds_burned: []
proof_attempt_summary: |
  The run proved the sparse-core reduction, an exact candidate-sensitive general-width compiler, the complete district-width-two polynomial-delay construction, the width-two counting reduction, and post-compilation reliability/derivative evaluation. The promised general-width accepted-output-delay result collapsed at the cross-core domination problem: avoiding previously found obstructions couples a hypergraph-transversal constraint to multiple-root reachability, and bounded district width supplies no extension oracle. The canonical finite partial-support state, child partition, and nonempty-completion test therefore remain open and cannot be replaced by the proved raw-candidate-sensitive bound.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 21612149
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 21612149
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# scm_minhedge_reliability_hypergraph / v1 — Failed

**Topic.** Minimal edge-support obstruction hypergraphs for exact reliability of uncertain causal identification. Given a topologically ordered ADMG envelope with deterministic backbone edges, independently uncertain directed/bidirected edges, and a fixed query P_x(y), define O_XY as all inclusion-minimal uncertain-edge supports on which ordinary ID fails. Let b be the largest bidirected district of the full envelope and tau the incidence-treewidth of O_XY. Prove a canonical sparse-hedge-core algorithm enumerates O_XY with 2^{O(b log b)} polynomial preprocessing and delay, with coverage, global minimality, duplicate suppression, and exhaustion; include a complete polynomial-delay construction for all b<=2 envelopes by deterministic-path projection and induced-path branching. Prove R_XY(p)=product_e(1-p_e) I_O((p_e/(1-p_e))_e), compute R and every partial derivative in 2^{O(tau)} polynomial exact-arithmetic time from an incidence decomposition, and prove exact successful-realization counting at p_e=1/2 is #P-complete already at b=2. Consumer: Akbari et al.'s uncertain-ADMG sampler and edgeID workflow, which would report total identifiability probability, minimal failure combinations, and graph-refinement sensitivities instead of only one selected identifiable realization. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Informal derivations show that reachable-district width b equals the largest bidirected district of the envelope; every hedge has a selected core with at most 2b-2 edges and at most |V|*2^{O(b log b)} core templates. The entire b<=2 class reduces to labeled DAG reachability, where deterministic-path projection and chord-deleting induced-path branching enumerate minimal uncertain-edge supports with polynomial delay. Exact checks covered 32,000 four-vertex queries, 1,024 source-star realizations, 729 ternary DAG envelopes, 400 random seven-vertex envelopes, and 4,096 transversal encodings. The normalized independence-polynomial identity, incidence-treewidth reliability/derivative dynamic program, and #P hardness already at b=2 were also derived. UNRESOLVED BOTTLENECK: Prove a canonical partial-support recursion for globally minimal multiple-root ancestry supports across competing sparse hedge cores with 2^{O(b log b)} preprocessing and worst-case delay, including deterministic projection, cross-core domination, duplicate suppression, and exhaustion. EARLY KILL TEST: Exhaustively compare the proposed root-ordered state and child partition against every minimal support on envelopes with at most six vertices, b<=3, and at most eight uncertain edges; any omission, duplicate, false live branch, or lost global minimality stops the compiler. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_minhedge_reliability_hypergraph.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The proposal headlined a general-b accepted-output-delay compiler, but the proved theorem delivers only raw-Steiner-candidate-sensitive total time and leaves that delay object open.

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

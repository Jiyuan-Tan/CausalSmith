---
qid: scm_scg_cde_refinement_bounds
spec: v1
topic: "Sharp lag-refinement bounds for micro controlled direct effects: for finite binary processes with directed effects restricted to positive lags 1,…,L, a bounded observed window, and a directed/bidirected summary causal graph, fix one common controlled direct-effect query over the positive-lag possible-parent set and define its envelope over all compatible full-time ADMG refinements and semi-Markovian SCMs reproducing an algebraically encoded positive observed law; compile the fiber into canonical response-function polynomial programs and prove terminating exact real-algebraic certification with derived bit complexity, endpoint attainment and SCM reconstruction, collapse to Ferreira–Assaad adjustment under their conditions, strict tightening over graph-free order-only bounds on a graphically characterized relative-open family, and simultaneous-multinomial whole-set inference with tie-aware EasyRCA comparisons. PRESOLVE EVIDENCE REQUIRING VERIFICATION: For N=|V|(H+1), bounded positive lags give finitely many full-time refinements; fixed-graph canonical response tables turn each refinement into a compact polynomial program, and real-algebraic quantifier elimination isolates attained endpoints and reconstructs algebraic-weight SCMs. In the binary temporal-IV witness, matching primal/dual calculations give graph-aware endpoints 0.285 and 0.685 versus order-only endpoints -0.1975 and 0.8025; every response-coupling cell is at least 0.005, so continuity plausibly extends strict tightening to a relative-open family. A rational box-simplex multinomial confidence polytope supplies simultaneous finite-sample coverage, with joint pairwise endpoint optimization reporting ties when effect differences include zero. Checks covered H=L, γ=L, cyclic summaries with acyclic positive-lag unrollings, bow graphs, non-clique bidirected districts, simplex boundaries, zero-cell confidence regions, and the closest fixed-graph, order-only, and summary-graph papers; no collision or counterexample was found. UNRESOLVED BOTTLENECK: Prove that merging observationally and query-equivalent response signatures preserves exactly the attainable (P,q) image and semi-Markovian factorization with overlapping independent latent parents, and derive the quotient-size bound. EARLY KILL TEST: On binary A↔B↔C with independent edge latents and one lagged arrow into C, exhaust raw and quotiented canonical signatures and compare their projected (P,q) semialgebraic sets by exact elimination; any separating witness forces an unquotiented pivot and kills the quotient-complexity claim."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REVISE
proposal_promise_gap: "Field-tier delivery would require a separate raw-refinement compiler, proof-producing exact-QE backend, stable trace verifier, endpoint decoder, and executable certificate artifacts."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The finite raw-program envelope, the contrast-specific MC iff UA frontier, and the rational strict-tightening example are proved, but the advertised total exact certification framework is not fully discharged."
  - "The absence of an implementation, replay artifact, or application beyond constructed witnesses further limits the projected leading-journal score."
  - "What remains is a non-obvious but specialized graphical frontier and finite semialgebraic characterization, not yet the validated reusable compiler advertised by the headline."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_robust_order_tightening.json
  - discovery/solve_thm_factorization_safe_quotient_obstruction.json
  - discovery/solve_thm_positive_lag_fa_extension_collapse.json
  - formalization/plan.json
seeds_burned: []
proof_attempt_summary: |
  Discovery proved a finite sharp refinement envelope, the exact bounded-window
  frontier for uniform validity of the unadjusted Ferreira–Assaad contrast, a
  relative-open strict-tightening witness, simultaneous whole-set inference, and
  a full-support obstruction to unsafe response-signature quotienting.  A
  cross-boundary audit repaired the BPR provenance by separating its direct
  arithmetic/height/sample-point bounds from a paper-owned arithmetic-to-bit
  lift, and both typed technical panels then passed.  Field-tier delivery still
  requires an implemented proof-producing exact-QE compiler, trace verifier,
  endpoint decoder, and executable certificate artifacts; that is a separate
  project, so the sound theorem package is banked at subfield.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 68245217
  pipeline_claude_tokens: 24554966
  pipeline_tokens_consumed: 92800183
  total_tokens_consumed: null
banked_on: "2026-09-09"
---

# scm_scg_cde_refinement_bounds / v1 — Downgraded

**Topic.** Sharp lag-refinement bounds for micro controlled direct effects: for finite binary processes with directed effects restricted to positive lags 1,…,L, a bounded observed window, and a directed/bidirected summary causal graph, fix one common controlled direct-effect query over the positive-lag possible-parent set and define its envelope over all compatible full-time ADMG refinements and semi-Markovian SCMs reproducing an algebraically encoded positive observed law; compile the fiber into canonical response-function polynomial programs and prove terminating exact real-algebraic certification with derived bit complexity, endpoint attainment and SCM reconstruction, collapse to Ferreira–Assaad adjustment under their conditions, strict tightening over graph-free order-only bounds on a graphically characterized relative-open family, and simultaneous-multinomial whole-set inference with tie-aware EasyRCA comparisons. PRESOLVE EVIDENCE REQUIRING VERIFICATION: For N=|V|(H+1), bounded positive lags give finitely many full-time refinements; fixed-graph canonical response tables turn each refinement into a compact polynomial program, and real-algebraic quantifier elimination isolates attained endpoints and reconstructs algebraic-weight SCMs. In the binary temporal-IV witness, matching primal/dual calculations give graph-aware endpoints 0.285 and 0.685 versus order-only endpoints -0.1975 and 0.8025; every response-coupling cell is at least 0.005, so continuity plausibly extends strict tightening to a relative-open family. A rational box-simplex multinomial confidence polytope supplies simultaneous finite-sample coverage, with joint pairwise endpoint optimization reporting ties when effect differences include zero. Checks covered H=L, γ=L, cyclic summaries with acyclic positive-lag unrollings, bow graphs, non-clique bidirected districts, simplex boundaries, zero-cell confidence regions, and the closest fixed-graph, order-only, and summary-graph papers; no collision or counterexample was found. UNRESOLVED BOTTLENECK: Prove that merging observationally and query-equivalent response signatures preserves exactly the attainable (P,q) image and semi-Markovian factorization with overlapping independent latent parents, and derive the quotient-size bound. EARLY KILL TEST: On binary A↔B↔C with independent edge latents and one lagged arrow into C, exhaust raw and quotiented canonical signatures and compare their projected (P,q) semialgebraic sets by exact elimination; any separating witness forces an unquotiented pivot and kills the quotient-complexity claim.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REVISE

**Banking reason.** The finite semialgebraic envelope and exact unadjusted-contrast frontier are sound, but the advertised generic replayable exact-certification framework lacks an implemented proof-producing QE backend and is assessed subfield.

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

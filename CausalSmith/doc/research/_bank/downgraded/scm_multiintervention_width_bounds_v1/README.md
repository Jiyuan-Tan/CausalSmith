---
qid: scm_multiintervention_width_bounds
spec: v1
topic: "Certified exact optimization at bounded canonical-response width for multi-intervention quasi-Markovian SCMs. Fix a finite acyclic quasi-Markovian SCM with observed alphabets at most q, a compatible positive rational observational table, and a treatment touching at least three C-components. The input fully expands every canonical response-mass coordinate, raw observational equality, nonnegativity constraint, and interventional-query monomial, together with a nice decomposition of the scalar response-factor primal graph of width k; B is this full binary input length. Prove that a fixed external-parent context partitions each response block into at most q^2 equality-support cliques, so it has at most q^2(k+1) coordinates. Split disconnected equality systems, prove the resulting compact rational product and block-affinity, and compute exact sharp endpoints by complete support enumeration and standard max-sum/min-sum elimination in 2^{O(q^2(k+1)^2)} poly(B) bit operations. Return finite rational compatible SCMs attaining both endpoints and independently checkable support, separator-table, and backpointer certificates. For binary at-most-two-child components and ell explicitly relevant original response blocks, also prove the B^{O(ell(1+log B)^2)} exact algorithm without a width assumption. Credit Shridharan–Iyengar for the canonical multilinear reduction, Dechter for bucket elimination, Duarte et al. and Zaffalon et al. for general causal/credal bounds, and causaloptim-lean for existing linear certificate formalization. The CRAN causaloptim graph-to-bound workflow is the prospective same-question consumer: this theorem supplies a certified fallback for small higher-degree queries, not a claimed implementation. Exclude hardness, implicit response columns, statistical projection, new elimination machinery, and benchmark gains. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A fresh presolve independently derived the raw equality-clique bound, compact equality-component factorization, width-preserving contraction, exhaustive rational support criterion, denominator bit bound, and binary logarithmic-square rank bound. Exact rational checks reproduced 8,192 canonical tuples, 4,096 cubic monomials, 64 positive observed cells, and sharp endpoints 11/64 and 53/64 in a legal three-component chain; they additionally enumerated 80 and 32 vertices in the later disconnected factors and 243 projected tuples. An interleaved-parent example showed why the component kernel is 1/4 where the ordinary conditional is 3/8. Destructive checks covered omitted normalization, singular supports, zero endpoint masses, running intersection, irrelevant blocks, degree versus relevant-block count, and live collisions; generic elimination and existing canonical-validity results are explicitly credited. UNRESOLVED BOTTLENECK: Prove executable refinement: acceptance by the serialized certificate verifier must imply universal compatible-SCM interval validity and rational endpoint realization for every well-formed canonical input, with generator completeness and the stated bit bound. EARLY KILL TEST: Run the verifier on the cubic, interleaved-parent, disconnected-equality, singular-support, and zero-mass cases, then delete a necessary vertex and corrupt a separator entry; stop if an incorrect endpoint or source-kernel mismatch is accepted, and pivot if repair changes the representation contract. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_multiintervention_width_bounds.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The proposed certified causal endpoints optimize an unconstrained serialized g unless a deterministic canonical query compiler and coefficientwise equality contract are added; even that repair does not lift the representation-sensitive package to field tier."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The input class requires only syntactic completeness of the declared polynomial, not that g is the canonical expansion of Q: e.g. g=0 is admissible while E_Y=Val(V) gives Q=1, so (5) and the asserted value-set equality are false."
  - "Its elimination correctly optimizes the serialized g, but without a semantic g=Q contract it need not compute the compatible-SCM causal endpoints claimed in the theorem."
  - "Replay can certify extrema of an arbitrary complete serialized g; the missing g=Q premise leaves universal compatible-SCM interval validity and endpoint realization for Q unproved."
  - "The vertex/LP route optimizes g only; its sharp causal endpoint conclusion inherits the absent semantic link between the serialized polynomial and Q."
  - "The note proves exact rational endpoint computation for a fully expanded, positive-rational, at-most-two-child quasi-Markovian class under supplied scalar width, together with a separate binary few-relevant-block algorithm; these are genuine but representation-sensitive computational results."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_binary_relevant_block.json
  - discovery/solve_thm_binary_relevant_block.tex
  - reviews/review_math.json
  - orchestrator/decision_log.jsonl
seeds_burned: []
proof_attempt_summary: |
  Discovery derived the raw equality-clique width bound, equality-factor splitting,
  exact bucket-elimination certificate scheme, and the strengthened
  B^{O((ell-1)(1+log B)^2)} few-relevant-block algorithm with a polynomial ell=1
  elbow. D0.5 then found that the input only required a syntactically complete
  serialized polynomial g, not coefficientwise equality with the canonical causal
  query expansion, so all causal-endpoint conclusions could instead optimize an
  arbitrary g. A faithful revival must add a deterministic canonical query compiler,
  enforce coefficientwise equality, reprove downstream semantics, narrow the Duarte
  and Khachiyan cited leaves, and add the missing related-work positioning; the
  independent score still remained 6.3 below the 7.4 field floor.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 16477581
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 16477581
  total_tokens_consumed: null
banked_on: "2026-09-15"
---

# scm_multiintervention_width_bounds / v1 — Downgraded

**Topic.** Certified exact optimization at bounded canonical-response width for multi-intervention quasi-Markovian SCMs. Fix a finite acyclic quasi-Markovian SCM with observed alphabets at most q, a compatible positive rational observational table, and a treatment touching at least three C-components. The input fully expands every canonical response-mass coordinate, raw observational equality, nonnegativity constraint, and interventional-query monomial, together with a nice decomposition of the scalar response-factor primal graph of width k; B is this full binary input length. Prove that a fixed external-parent context partitions each response block into at most q^2 equality-support cliques, so it has at most q^2(k+1) coordinates. Split disconnected equality systems, prove the resulting compact rational product and block-affinity, and compute exact sharp endpoints by complete support enumeration and standard max-sum/min-sum elimination in 2^{O(q^2(k+1)^2)} poly(B) bit operations. Return finite rational compatible SCMs attaining both endpoints and independently checkable support, separator-table, and backpointer certificates. For binary at-most-two-child components and ell explicitly relevant original response blocks, also prove the B^{O(ell(1+log B)^2)} exact algorithm without a width assumption. Credit Shridharan–Iyengar for the canonical multilinear reduction, Dechter for bucket elimination, Duarte et al. and Zaffalon et al. for general causal/credal bounds, and causaloptim-lean for existing linear certificate formalization. The CRAN causaloptim graph-to-bound workflow is the prospective same-question consumer: this theorem supplies a certified fallback for small higher-degree queries, not a claimed implementation. Exclude hardness, implicit response columns, statistical projection, new elimination machinery, and benchmark gains. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A fresh presolve independently derived the raw equality-clique bound, compact equality-component factorization, width-preserving contraction, exhaustive rational support criterion, denominator bit bound, and binary logarithmic-square rank bound. Exact rational checks reproduced 8,192 canonical tuples, 4,096 cubic monomials, 64 positive observed cells, and sharp endpoints 11/64 and 53/64 in a legal three-component chain; they additionally enumerated 80 and 32 vertices in the later disconnected factors and 243 projected tuples. An interleaved-parent example showed why the component kernel is 1/4 where the ordinary conditional is 3/8. Destructive checks covered omitted normalization, singular supports, zero endpoint masses, running intersection, irrelevant blocks, degree versus relevant-block count, and live collisions; generic elimination and existing canonical-validity results are explicitly credited. UNRESOLVED BOTTLENECK: Prove executable refinement: acceptance by the serialized certificate verifier must imply universal compatible-SCM interval validity and rational endpoint realization for every well-formed canonical input, with generator completeness and the stated bit bound. EARLY KILL TEST: Run the verifier on the cubic, interleaved-parent, disconnected-equality, singular-support, and zero-mass cases, then delete a necessary vertex and corrupt a separator entry; stop if an incorrect endpoint or source-kernel mismatch is accepted, and pivot if repair changes the representation contract. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_multiintervention_width_bounds.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** D0.5 found that syntactic completeness does not require serialized g to equal the canonical causal query expansion; the package scored 6.3 below the 7.4 field floor, salvageable=false, with no bounded improvement directive.

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

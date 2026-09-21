---
qid: scm_sparsestfamily_simid_complete
spec: v1
topic: "Rational common-law certificates for simultaneous effects across sparsest causal graphs. Input finite variables, an exact CI bit-vector, background orientations, and the explicitly enumerated minimum-edge SA-MPDAG/CPDAG I-maps with certificates. For a fixed query P_x(Y), expand each represented DAG's truncated factorization into rational observed-table polynomials. Saturate the common CI ideal by all positive cells and denominators and use fixed-order real-radical normal forms for sound equality certificates. Prove SparseSIM-ID complete on this tied sparsest family: it returns either one common observable arithmetic circuit with checkable real-Nullstellensatz certificates, or two represented DAGs and a strictly positive rational table satisfying every oracle/graph restriction but giving different intervention laws. The hard theorem is effect-specific rational-positive separation for the common-law model; generic radical decision is supporting machinery. Give explicit termination/certificate bounds and plug-in inference after common identification. Consumer: Tetrad SP and causaldag/GSP all-ties output should report a common effect or a concrete ambiguity table instead of selecting one tied graph. PRESOLVE EVIDENCE REQUIRING VERIFICATION: An explicit separator lemma was derived for oppositely oriented oracle-inseparable binary edges. Exact enumeration of all 543 four-variable DAGs for the rational law (4,4,1,1,4,1,4,1,1,4,1,4,1,1,4,4)/40 found exactly four elementary CIs, 50 I-maps, and exactly two four-edge minimum DAGs in distinct MECs; their do(1=+1) effect on variable 3 is 13/20 versus 1/2. Checks exposed that graph-Markov constraints are redundant given the exact I-map oracle and that saturation alone does not encode strict positivity; no counterexample or prior-art completion of the general causal completeness theorem was found. UNRESOLVED BOTTLENECK: Prove that every intervention cross-product outside the rational real radical of the declared saturated oracle ideal has a strictly positive rational common-law point separating the effect for the tied minimum-edge family. EARLY KILL TEST: On positive rational binary four-variable multi-MEC oracles, enumerate all I-map DAGs and singleton-effect queries, then compare nonzero saturated-real-radical remainders with exact positive feasibility of F!=0; one nonzero remainder with no positive separator kills K1--K2. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_sparsestfamily_simid_complete.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "The proposed rational-positive separator with effective height is the known unresolved crux; the delivered exact algebraic decision framework has no degree, height, certificate-length, or usable runtime bound and no positive cross-MEC common-effect example missed by existing graphical criteria."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The main completeness theorem establishes decidability through exhaustive DAG enumeration and generic real-closed-field quantifier elimination, but supplies no degree, height, certificate-length, or usable runtime bound."
  - "The sole worked cross-MEC example produces an ambiguity certificate rather than a common effect missed by existing graphical criteria."
  - "General separating tables are only real algebraic, while rational replacement and effective height control remain explicitly open."
reusable_artifacts:
  - "discovery/core.json — maximized theorem graph with exhaustive tied-DAG enumeration, positive-chamber decision, maximal effect quotient, certificates, and fixed-class inference"
  - "discovery/writeup.tex — deterministic derivation note and explicit four-node rational ambiguity witness"
  - "discovery/solve_thm_rational_positive_separation.{json,tex} — semialgebraic positive-chamber decision construction"
  - "discovery/solve_thm_sparse_simid_completeness.{json,tex} — completeness and maximal-quotient proof material"
  - "reviews/review_math.json — clean mathematical audit and citation verification receipts"
seeds_burned:
  - index: 0
    one_liner: "seed:rational-positive-dichotomy"
    reason: "The sole developed angle was maximized through seven D0 solve rounds, but D0.5 found no bounded field-tier repair in scope."
proof_attempt_summary: |
  The run proved an exact finite procedure that enumerates tied sparsest DAGs, decides pairwise
  effect equality over the positive exact-oracle chamber by real-closed-field methods, computes the
  maximal effect quotient, and returns exact algebraic separators; it also verified the explicit
  four-node rational ambiguity witness and fixed-class Wald inference. The advertised bounded
  rational-positive separator theorem collapsed because saturated-ideal nonmembership need not select
  the relevant positive sign chamber or a rational point. A field-tier successor must prove effective
  rational replacement with height bounds and/or construct a substantive positive cross-MEC common-effect
  example beyond existing graphical criteria.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 45128665
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 45128665
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# scm_sparsestfamily_simid_complete / v1 — Downgraded

**Topic.** Rational common-law certificates for simultaneous effects across sparsest causal graphs. Input finite variables, an exact CI bit-vector, background orientations, and the explicitly enumerated minimum-edge SA-MPDAG/CPDAG I-maps with certificates. For a fixed query P_x(Y), expand each represented DAG's truncated factorization into rational observed-table polynomials. Saturate the common CI ideal by all positive cells and denominators and use fixed-order real-radical normal forms for sound equality certificates. Prove SparseSIM-ID complete on this tied sparsest family: it returns either one common observable arithmetic circuit with checkable real-Nullstellensatz certificates, or two represented DAGs and a strictly positive rational table satisfying every oracle/graph restriction but giving different intervention laws. The hard theorem is effect-specific rational-positive separation for the common-law model; generic radical decision is supporting machinery. Give explicit termination/certificate bounds and plug-in inference after common identification. Consumer: Tetrad SP and causaldag/GSP all-ties output should report a common effect or a concrete ambiguity table instead of selecting one tied graph. PRESOLVE EVIDENCE REQUIRING VERIFICATION: An explicit separator lemma was derived for oppositely oriented oracle-inseparable binary edges. Exact enumeration of all 543 four-variable DAGs for the rational law (4,4,1,1,4,1,4,1,1,4,1,4,1,1,4,4)/40 found exactly four elementary CIs, 50 I-maps, and exactly two four-edge minimum DAGs in distinct MECs; their do(1=+1) effect on variable 3 is 13/20 versus 1/2. Checks exposed that graph-Markov constraints are redundant given the exact I-map oracle and that saturation alone does not encode strict positivity; no counterexample or prior-art completion of the general causal completeness theorem was found. UNRESOLVED BOTTLENECK: Prove that every intervention cross-product outside the rational real radical of the declared saturated oracle ideal has a strictly positive rational common-law point separating the effect for the tied minimum-edge family. EARLY KILL TEST: On positive rational binary four-variable multi-MEC oracles, enumerate all I-map DAGs and singleton-effect queries, then compare nonzero saturated-real-radical remainders with exact positive feasibility of F!=0; one nonzero remainder with no positive separator kills K1--K2. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_sparsestfamily_simid_complete.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** Math review passes, but the contribution remains a generic finite enumeration plus real-closed-field feasibility composition; the negative strictness witness does not prove a stronger identification region.

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

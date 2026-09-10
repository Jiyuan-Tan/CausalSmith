---
qid: scm_threeitem_mnar_hybrid_complete
spec: v1
topic: "Complete binary three-item target-law classification under MNAR conditional missingness DAGs. For every labelled DAG G on binary X=(X1,X2,X3) and R=(R1,R2,R3), allow arbitrary Xj-to-Ri arrows, an acyclic R subgraph, no R-to-X arrows or latent variables, and every strictly positive 64-cell law factorizing as p(X) times the response kernels. Construct a total deterministic Complete3 classifier for uniform graph-model identification of the eight-cell target p_X from the full coarsened observed law. Its ID output must give eight rational expressions in observed cell probabilities, with divisions only by observed marginals positive throughout the model and a graph-factorization derivation. Its NONID output must give two explicit strictly positive rational 64-cell Markov laws with identical probabilities for all 27 coarsened observed cells but different p_X at a named cell. Prove that Complete3 terminates under an explicit graph-uniform operation bound B and returns ID iff p_X is uniformly identified, otherwise NONID, for all 12,800 labelled graphs. The construction may combine intervention-tree fixing, conditional independence, Chen odds-ratio factorization, grouped partial-order fixing, exact enumeration, and a finite obstruction catalogue, but may not use generic real quantifier elimination as the completeness proof. On every fixed epsilon-interior subclass, derive the plug-in rational estimator's multinomial influence function, covariance estimator, and simultaneous confidence region for all target cells. The public flexMissing intervention-tree workflow is the consumer: accepted graphs gain estimable formulas and rejected graphs gain checkable positive certificates. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact rational calculations verify the odds-rescue model (27 observed cells, minimum full mass 1/180, odds ratios 2 and 9/4, all eight target cells recovered as 1/8), the supplied self-censoring twins, and a new positive criss-cross twin fiber. Exhaustive graph reductions give positive rational twins for 11,854 labelled graphs and known/direct formulas for 742, leaving 204 graphs in 34 relabeling classes; an independently coded but unaudited fixing-state search leaves 48 graphs in eight classes. Checks distinguished uniform from law-specific identification, interior from boundary witnesses, and graph-specific certificates from generic algebraic decidability. The resolved March 2026 talk abstract reports partial solutions and remaining failures, and no public K=3 theorem was found through 2026-09-05. UNRESOLVED BOTTLENECK: Prove for every residual representative either a uniform rational observed-marginal functional or strictly positive rational observational twins, then compile certificates into a sound terminating classifier with an explicit operation bound. EARLY KILL TEST: Audit the fixing-state search and solve residual case 6, including positive rank-degenerate strata; stop if it forces a non-rational inverse, a forbidden divisor, or only irrational nonidentifying fibers. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_threeitem_mnar_hybrid_complete.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "No executable L3 AST/checker, no 496-mask or 246-mask trace compiler, and no completed 34-row residual-stratum ledger."
reusable: solver_blocked
reraise_status: true-negative
gap_reasons:
  - "after retry there are still no mask-indexed NBS weights, lower-level traces, checker transcripts, per-trace operation counts, or lexicographically first failed mask"
  - "Compile the Nabi--Bhattacharya--Shpitser unnormalized odds-ratio weights for each of the 496 no-self-censoring/no-colluder masks into accepted L3 traces"
  - "Classify the determinant-zero positive stratum of residual case 6 and construct accepted certificates for all strata of all 34 canonical residual graphs."
reusable_artifacts:
  - "discovery/proto_core.json — field-tier Complete3 statement, certificate grammar, and dependency graph"
  - "discovery/d0_escalation_log.jsonl — exact compiler directives, rejected language widening, and universal normalizer-cancellation retry"
  - "proof_archive/ — content-addressed derivations, including the universal target-level NBS normalizer cancellation"
  - "orchestrator/decision_log.jsonl — proposal adjudications, bounded-attempt receipts, and terminal validity rationale"
seeds_burned: []
proof_attempt_summary: |
  D-0.5 accepted the corrected Complete3 angle at field tier. Two exact-target D0 attempts attacked the 496-mask denominator-safe reduction compiler: the first widened the certificate language unfaithfully and was discarded; the second derived a universal NBS normalizer cancellation but emitted no mask-indexed weights, executable checker traces, operation ledger, or concrete failed-mask obstruction. A neutral validity gate classified the run as construction-intractable rather than theorem-false because implementing the AST/checker and 742 exhaustive traces would still leave the research-level 34-row exceptional-stratum ledger unresolved.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 30692825
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-06"
---

# scm_threeitem_mnar_hybrid_complete / v1 — Failed

**Topic.** Complete binary three-item target-law classification under MNAR conditional missingness DAGs. For every labelled DAG G on binary X=(X1,X2,X3) and R=(R1,R2,R3), allow arbitrary Xj-to-Ri arrows, an acyclic R subgraph, no R-to-X arrows or latent variables, and every strictly positive 64-cell law factorizing as p(X) times the response kernels. Construct a total deterministic Complete3 classifier for uniform graph-model identification of the eight-cell target p_X from the full coarsened observed law. Its ID output must give eight rational expressions in observed cell probabilities, with divisions only by observed marginals positive throughout the model and a graph-factorization derivation. Its NONID output must give two explicit strictly positive rational 64-cell Markov laws with identical probabilities for all 27 coarsened observed cells but different p_X at a named cell. Prove that Complete3 terminates under an explicit graph-uniform operation bound B and returns ID iff p_X is uniformly identified, otherwise NONID, for all 12,800 labelled graphs. The construction may combine intervention-tree fixing, conditional independence, Chen odds-ratio factorization, grouped partial-order fixing, exact enumeration, and a finite obstruction catalogue, but may not use generic real quantifier elimination as the completeness proof. On every fixed epsilon-interior subclass, derive the plug-in rational estimator's multinomial influence function, covariance estimator, and simultaneous confidence region for all target cells. The public flexMissing intervention-tree workflow is the consumer: accepted graphs gain estimable formulas and rejected graphs gain checkable positive certificates. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact rational calculations verify the odds-rescue model (27 observed cells, minimum full mass 1/180, odds ratios 2 and 9/4, all eight target cells recovered as 1/8), the supplied self-censoring twins, and a new positive criss-cross twin fiber. Exhaustive graph reductions give positive rational twins for 11,854 labelled graphs and known/direct formulas for 742, leaving 204 graphs in 34 relabeling classes; an independently coded but unaudited fixing-state search leaves 48 graphs in eight classes. Checks distinguished uniform from law-specific identification, interior from boundary witnesses, and graph-specific certificates from generic algebraic decidability. The resolved March 2026 talk abstract reports partial solutions and remaining failures, and no public K=3 theorem was found through 2026-09-05. UNRESOLVED BOTTLENECK: Prove for every residual representative either a uniform rational observed-marginal functional or strictly positive rational observational twins, then compile certificates into a sound terminating classifier with an explicit operation bound. EARLY KILL TEST: Audit the fixing-state search and solve residual case 6, including positive rank-degenerate strata; stop if it forces a non-rational inverse, a forbidden divisor, or only irrational nonidentifying fibers. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_threeitem_mnar_hybrid_complete.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** TERMINAL_FOR_THIS_RUN: construction-intractable, not theorem-false; no concrete bounded route exists to the required exact compiler.

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

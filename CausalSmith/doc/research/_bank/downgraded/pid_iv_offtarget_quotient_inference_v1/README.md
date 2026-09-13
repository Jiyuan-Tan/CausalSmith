---
qid: pid_iv_offtarget_quotient_inference
spec: v1
topic: "Exact quotient and nuisance-minimax inference for off-target exposure levels in discrete IV models. Let finite randomized Z have m arms, binary Y, and X=T union C. Require well-defined Z-excluded Y_t only for t in T; allow unrestricted X(z), and fully saturated arm-specific responses R_{c,z} for c in C. Prove that the sharp identified set for law(Y_T) depends only on skeleton cells p(X=t,Y=y|Z=z), equals the image of the reduced type simplex (T union {star})^Z times {0,1}^T, and is independent of |C| by an explicit right inverse. Conditional on arm counts, factor the full experiment into skeleton counts and a variation-independent nuisance allocation; for every convex loss prove the precise nuisance-minimax reduction R_q(delta0)<=sup_eta R_(q,eta)(delta), not pointwise domination. Adapt Song et al.'s method-of-types KL region for simultaneous finite-sample coverage of the entire reduced identified set, including endpoint kinks; state calibration and computation as independent of |C| but exponential in m and |T|, and prove feasible-law Hoffman/dual excess-width bounds plus a regular-face n^-1/2 lower bound. Verify by exact enumeration the Z={0,1},T={a,b},C={c} witness with z0 masses (a,0)=1/2,(c,1)=1/2 and z1 masses (a,0)=1/2,(c,0)=1/2: saturated responses give E[Y_b-Y_a] bounds [-1/2,1], while a common excluded Y_c gives [0,1]. PRESOLVE EVIDENCE REQUIRING VERIFICATION: represent reduced atoms r by x_z in T union {star} and y_T; the incidence map A records target cells and star mass and B records law(Y_T). Refine each star coordinate independently using eta_z(c,y)=p(c,y|z)/s(z,star), with a boundary convention at zero star mass, to obtain a full-law right inverse. Conditional multinomial likelihood then splits into a (2|T|+1)-cell skeleton factor and an eta_z allocation factor. For d=2|T|+1 use rho_z=[log(m/alpha)+(d-1)log(n_z+1)]/n_z in D(hat s_z||s_z), followed by reduced-polytope projection. Credit Gabriel et al. for finite coarsening cases, Song et al. for categorical-IV KL projection, Boushehrian et al. for exponential target-dimension limits, Sachs et al. for response LPs, and Levis et al. for active-facet inference. UNRESOLVED BOTTLENECK: prove the simplex/equality-system Hoffman statement for scalar support functions and keep every novelty claim confined to target-specific exclusion quotienting, nuisance-minimax equivalence, arbitrary finite cardinalities, and |C|-free inference. EARLY KILL TEST: enumerate the 36 reduced columns and corresponding 144 saturated full types for m=2,|T|=2, compare random support functions across multiple |C|, and require the displayed bounds exactly."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "No matched kink minimax/adaptive inference frontier, matching nonregular rate, polynomial computation in m and |T|, or substantive implementation/applied evidence; remaining Gabriel/Song comparison is deliberately narrowed to attested scope."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "the exact local minimax law and adaptive inference frontier at endpoint kinks remain open"
  - "the note does not establish a matched inference frontier"
  - "Computation remains exponential in the substantive arm and target cardinalities"
  - "supporting evidence is limited to one analytically certified low-cardinality witness without an implementation or applied demonstration"
reusable_artifacts:
  - "discovery/core.json — audited theorem graph, assumptions, and cited-source scopes"
  - "discovery/writeup.tex — sound incremental derivation after citation and empty-C boundary repairs"
  - "discovery/solve_thm_quotient_sharpness.json — exact quotient/right-inverse proof attempt"
  - "discovery/solve_thm_experiment_factorization.json — conditional experiment factorization proof attempt"
  - "discovery/solve_thm_binary_reduction.json — exact low-cardinality witness reduction"
  - "reviews/stage_0.5.G_attempt1.json — terminal field-tier assessment and missing-headline diagnosis"
seeds_burned: []
proof_attempt_summary: |
  The run derived and audited an exact target-only quotient, a boundary-safe right inverse,
  finite conditional-experiment factorization for nonempty off-target sets, nuisance-minimax
  reduction, KL whole-set coverage, and the stated binary witness. It repaired two comparator
  overclaims and the empty-off-target boundary, after which the same-note math and citation
  audits passed. The paper still lacked a matched kink minimax/adaptive inference frontier,
  a matching nonregular rate, scalable computation, and substantive implementation evidence,
  so D0.5 fixed the contribution at incremental rather than field tier.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 24624907
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 24624907
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# pid_iv_offtarget_quotient_inference / v1 — Downgraded

**Topic.** Exact quotient and nuisance-minimax inference for off-target exposure levels in discrete IV models. Let finite randomized Z have m arms, binary Y, and X=T union C. Require well-defined Z-excluded Y_t only for t in T; allow unrestricted X(z), and fully saturated arm-specific responses R_{c,z} for c in C. Prove that the sharp identified set for law(Y_T) depends only on skeleton cells p(X=t,Y=y|Z=z), equals the image of the reduced type simplex (T union {star})^Z times {0,1}^T, and is independent of |C| by an explicit right inverse. Conditional on arm counts, factor the full experiment into skeleton counts and a variation-independent nuisance allocation; for every convex loss prove the precise nuisance-minimax reduction R_q(delta0)<=sup_eta R_(q,eta)(delta), not pointwise domination. Adapt Song et al.'s method-of-types KL region for simultaneous finite-sample coverage of the entire reduced identified set, including endpoint kinks; state calibration and computation as independent of |C| but exponential in m and |T|, and prove feasible-law Hoffman/dual excess-width bounds plus a regular-face n^-1/2 lower bound. Verify by exact enumeration the Z={0,1},T={a,b},C={c} witness with z0 masses (a,0)=1/2,(c,1)=1/2 and z1 masses (a,0)=1/2,(c,0)=1/2: saturated responses give E[Y_b-Y_a] bounds [-1/2,1], while a common excluded Y_c gives [0,1]. PRESOLVE EVIDENCE REQUIRING VERIFICATION: represent reduced atoms r by x_z in T union {star} and y_T; the incidence map A records target cells and star mass and B records law(Y_T). Refine each star coordinate independently using eta_z(c,y)=p(c,y|z)/s(z,star), with a boundary convention at zero star mass, to obtain a full-law right inverse. Conditional multinomial likelihood then splits into a (2|T|+1)-cell skeleton factor and an eta_z allocation factor. For d=2|T|+1 use rho_z=[log(m/alpha)+(d-1)log(n_z+1)]/n_z in D(hat s_z||s_z), followed by reduced-polytope projection. Credit Gabriel et al. for finite coarsening cases, Song et al. for categorical-IV KL projection, Boushehrian et al. for exponential target-dimension limits, Sachs et al. for response LPs, and Levis et al. for active-facet inference. UNRESOLVED BOTTLENECK: prove the simplex/equality-system Hoffman statement for scalar support functions and keep every novelty claim confined to target-specific exclusion quotienting, nuisance-minimax equivalence, arbitrary finite cardinalities, and |C|-free inference. EARLY KILL TEST: enumerate the 36 reduced columns and corresponding 144 saturated full types for m=2,|T|=2, compare random support functions across multiple |C|, and require the displayed bounds exactly.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G tier=incremental < floor=field (target=field) and NOT salvageable in scope; paper_score_ceiling=6.2 below the 7.2 field threshold.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

The quotient and exact witness are reusable starting points. Any future field-tier topic should
re-anchor on a genuinely new kink-rate or adaptive-inference theorem rather than restating the
identification quotient, and should retain the repaired nonempty-`C` scope for the experiment-level
factorization claims.

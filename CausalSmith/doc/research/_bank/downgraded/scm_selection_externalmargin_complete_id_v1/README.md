---
qid: scm_selection_externalmargin_complete_id
spec: v1
topic: "Constructive completeness for causal recovery from selected data plus one unbiased external margin. For every finite-state semi-Markovian selection ADMG G on V union {S}, disjoint X,Y, and T0 subset V, with epsilon-positive selected P(V|S=1) and unbiased P(T0), construct a terminating EXT-ID procedure returning either an explicit finite arithmetic functional for P_x(Y) valid in every compatible SCM or two epsilon-interior finite SCMs agreeing on both input laws but disagreeing on P_x(Y); prove soundness, completeness, termination, and for every differentiable returned functional give the saturated two-source plug-in estimator, source-specific influence functions, and simultaneous confidence regions uniformly on fixed positive compact subclasses. The ACTG 320 generalization to women using WIHS/CNICS margins is the applied audit consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A derived recovery step shows that whenever Z is conditionally independent of selection S given the unbiased-margin variables T0, the population joint law P(T0,Z) equals P(Z|T0,S=1)P(T0) and can feed recursive district fixing. On a positive binary graph with W affecting treatment, mediator, outcome, and selection, plus treatment–outcome confounding and T0={W}, this produces a front-door-type external-margin functional; exact rational evaluation at one intervention/outcome cell matched the directly computed value 19/36. A destructive check also produced two strictly positive binary SCMs for A→Y→S with T0={A} that agree on uniform P(A,Y|S=1) and P(A=1)=1/2 but yield population P(Y=1|a) equal to 1/3 versus 2/3 by offsetting positive selection probabilities. Boundary cases T0=V, selection independent of V, empty T0, adjustment, gID, do-search, and the 2024 systematic-selection framework were checked without finding a collision. UNRESOLVED BOTTLENECK: Prove the margin-anchored hedge lemma: every terminal failure of the proposed mixed-source fixing recursion admits two epsilon-interior finite SCMs agreeing exactly on both P(V|S=1) and P(T0) while disagreeing on P_x(Y). EARLY KILL TEST: Enumerate every binary selection ADMG with at most three substantive nodes and every T0; compare the recursion with exact response-function quantifier elimination, and pivot or stop on any unsound returned formula or any failure lacking an interior same-input/different-query witness."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - >-
    The delivered note does not prove the constructive completeness advertised by the research objective: EXT-ID is sound and terminating, but its FAIL output is not connected to a nonidentification witness except in one hand-constructed graph.
  - >-
    The canonical response-fiber theorem only characterizes nonidentification when its separate feasibility problem is solved; it does not establish that EXT-ID failure makes that problem feasible.
  - >-
    Moreover, the claimed exactness of the response-fiber characterization relies on the uncited finite-disturbance full-law reduction, which is stated without an author, year, theorem identifier, or cardinality guarantee.
reusable_artifacts:
  - discovery/writeup.tex
  - discovery/core.json
  - discovery/d0_working.json
  - discovery/proof_archive/index.jsonl
  - reviews/review_general.json
  - orchestrator/decision_log.jsonl
seeds_burned: []
proof_attempt_summary: |
  The run built a finite terminating EXT-ID transition system, proved success soundness, a conditional projective nullspace certificate, an exact three-node rational witness, fixed-fiber semialgebraic characterization, and boundary obstruction results. The field-level step collapsed because neither the projective argument nor the available quantifier-elimination substrate derives a feasible same-input separating pair from every terminal EXT-ID failure. A future revival must prove the margin-anchored hedge or add a genuinely complete recovery rule, while also supplying a sourced finite-disturbance full-law reduction.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 96040834
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-04"
---

# scm_selection_externalmargin_complete_id / v1 — Downgraded

**Topic.** Constructive completeness for causal recovery from selected data plus one unbiased external margin. For every finite-state semi-Markovian selection ADMG G on V union {S}, disjoint X,Y, and T0 subset V, with epsilon-positive selected P(V|S=1) and unbiased P(T0), construct a terminating EXT-ID procedure returning either an explicit finite arithmetic functional for P_x(Y) valid in every compatible SCM or two epsilon-interior finite SCMs agreeing on both input laws but disagreeing on P_x(Y); prove soundness, completeness, termination, and for every differentiable returned functional give the saturated two-source plug-in estimator, source-specific influence functions, and simultaneous confidence regions uniformly on fixed positive compact subclasses. The ACTG 320 generalization to women using WIHS/CNICS margins is the applied audit consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A derived recovery step shows that whenever Z is conditionally independent of selection S given the unbiased-margin variables T0, the population joint law P(T0,Z) equals P(Z|T0,S=1)P(T0) and can feed recursive district fixing. On a positive binary graph with W affecting treatment, mediator, outcome, and selection, plus treatment–outcome confounding and T0={W}, this produces a front-door-type external-margin functional; exact rational evaluation at one intervention/outcome cell matched the directly computed value 19/36. A destructive check also produced two strictly positive binary SCMs for A→Y→S with T0={A} that agree on uniform P(A,Y|S=1) and P(A=1)=1/2 but yield population P(Y=1|a) equal to 1/3 versus 2/3 by offsetting positive selection probabilities. Boundary cases T0=V, selection independent of V, empty T0, adjustment, gID, do-search, and the 2024 systematic-selection framework were checked without finding a collision. UNRESOLVED BOTTLENECK: Prove the margin-anchored hedge lemma: every terminal failure of the proposed mixed-source fixing recursion admits two epsilon-interior finite SCMs agreeing exactly on both P(V|S=1) and P(T0) while disagreeing on P_x(Y). EARLY KILL TEST: Enumerate every binary selection ADMG with at most three substantive nodes and every T0; compare the recursion with exact response-function quantifier elimination, and pivot or stop on any unsound returned formula or any failure lacking an interior same-input/different-query witness.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** Sound scoped results, but no theorem turns every terminal EXT-ID failure into a same-input separating pair; achieved subfield ceiling 6.8 below the field floor.

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

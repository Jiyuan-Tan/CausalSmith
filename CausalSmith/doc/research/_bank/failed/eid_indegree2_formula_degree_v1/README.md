---
qid: eid_indegree2_formula_degree
spec: v1
topic: "Sharp identifying-degree frontier for rationally identifiable acyclic linear Gaussian mixed graphs with directed indegree at most two. Let ID_G be the source-defined minimum, over recursive identifying orders, of the largest total polynomial degree in any certificate, and let D2(n) maximize ID_G over identifiable n-vertex graphs. Prove matching asymptotic upper and lower bounds for D2(n), including an explicit graph family whose degree cannot be reduced by recursive substitutions through structural or error parameters; compile the upper bound into a total stopping schedule for DegBoundedIdentifiability; and give plug-in influence-function and simultaneous Wald inference for the returned rational formulas on fixed denominator, covariance-eigenvalue, and nondegeneracy charts. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact rank-intersection closure over all original parameters was derived and used to enumerate all 64 topologically labelled three-vertex mixed graphs, yielding D2(3)=3: eight degree-one, twenty-one degree-two, two degree-three, and thirty-three generically rank-deficient graphs. A positive-definite six-vertex directed chain outside HTC was constructed; two quadratic cycle equations with distinct second roots cancel to give a rational certificate of degree at most nine. Checks covered bow nonidentification, cycle ambiguity, error-parameter shortcuts, generic-elimination collapse, and current tree-identification work; no exact frontier collision was found. UNRESOLVED BOTTLENECK: Determine the sharp graph-uniform closure degree for every rationally identifiable indegree-two graph and construct a matching family whose degree-d closure remains proper below that threshold. EARLY KILL TEST: Compute exact degree-four closure for the six-vertex two-triangle graph, including error parameters; if it is complete, abandon cycle length as growth evidence and test constant-degree completeness before enlarging the family. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_indegree2_formula_degree.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The proposal promised matching asymptotic upper and lower bounds for D2(n), but discovery established only graph-sensitive and graph-uniform effective elimination upper bounds; exact ID_K6, any intrinsic rate, and a substitution-robust lower family remain unresolved."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The proposal's sharp full-class indegree-two frontier (matching upper and lower bounds) is still explicitly unresolved; the delivered effective Dubé cutoff is a materially weaker object and must be repositioned as such rather than presented as fulfillment of that frontier promise."
  - "The advertised sharp identifying-degree frontier is not determined: the note proves only the very loose bracket 3 <= D2(n) <= U2(n), where U2 is a generic double-exponential Gröbner bound rather than an intrinsic rate."
  - "After the windmill family failed, no admissible lower family remains."
reusable_artifacts:
  - "discovery/solve_thm_effective_elimination_upper_bound.json — graph-sensitive cubic-elimination bound and certificate proof"
  - "discovery/solve_thm_total_stopping_schedule.json — total stopping-schedule construction from the effective cutoff"
  - "discovery/solve_oeq_degree_four_kill_test.json — audited K6 rational inverse and degree-at-most-seven route; no matching lower bound"
  - "discovery/solve_thm_closure_characterization.json — closure characterization and three-vertex base-case material"
  - "discovery/solve_thm_rational_chart_inference.json — inference result for fixed rational charts"
seeds_burned: []
proof_attempt_summary: |
  Discovery tested the proposed windmill lower family, rejected it by a parameter-dimension obstruction, and derived a valid graph-sensitive Dubé elimination bound, an unconditional stopping schedule, and a rational K6 inverse of degree at most seven. The sharp-frontier kernel nevertheless collapsed because neither the exact K6 lower certificate nor a dimension-feasible substitution-robust asymptotic lower family was established. Determining whether D2(n) is bounded, and matching that answer with an intrinsic upper bound, remains open.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 37455234
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 37455234
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# eid_indegree2_formula_degree / v1 — Failed

**Topic.** Sharp identifying-degree frontier for rationally identifiable acyclic linear Gaussian mixed graphs with directed indegree at most two. Let ID_G be the source-defined minimum, over recursive identifying orders, of the largest total polynomial degree in any certificate, and let D2(n) maximize ID_G over identifiable n-vertex graphs. Prove matching asymptotic upper and lower bounds for D2(n), including an explicit graph family whose degree cannot be reduced by recursive substitutions through structural or error parameters; compile the upper bound into a total stopping schedule for DegBoundedIdentifiability; and give plug-in influence-function and simultaneous Wald inference for the returned rational formulas on fixed denominator, covariance-eigenvalue, and nondegeneracy charts. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact rank-intersection closure over all original parameters was derived and used to enumerate all 64 topologically labelled three-vertex mixed graphs, yielding D2(3)=3: eight degree-one, twenty-one degree-two, two degree-three, and thirty-three generically rank-deficient graphs. A positive-definite six-vertex directed chain outside HTC was constructed; two quadratic cycle equations with distinct second roots cancel to give a rational certificate of degree at most nine. Checks covered bow nonidentification, cycle ambiguity, error-parameter shortcuts, generic-elimination collapse, and current tree-identification work; no exact frontier collision was found. UNRESOLVED BOTTLENECK: Determine the sharp graph-uniform closure degree for every rationally identifiable indegree-two graph and construct a matching family whose degree-d closure remains proper below that threshold. EARLY KILL TEST: Compute exact degree-four closure for the six-vertex two-triangle graph, including error parameters; if it is complete, abandon cycle length as growth evidence and test constant-degree completeness before enlarging the family. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_indegree2_formula_degree.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The advertised sharp identifying-degree frontier is not determined: only a loose effective Gröbner cutoff was proved, while the matching lower family and bounded-versus-unbounded elbow remain open.

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

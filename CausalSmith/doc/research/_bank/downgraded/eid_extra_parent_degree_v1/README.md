---
qid: eid_extra_parent_degree
spec: v1
topic: "Sharp generic single-edge identification degree beyond trees, with fasttreeid as the software consumer (exactid; field target). Let G=(V,D,B) be a known acyclic mixed graph on n>=2 vertices, bows allowed, containing a supplied rooted spanning arborescence T and at most k additional directed edges, where 0<=k<=(n-1)(n-2)/2. The Gaussian linear SCM has arbitrary real directed coefficients and positive-definite noise covariance Omega with zeros at missing bidirected pairs; its exact observed covariance is Sigma=(I-Lambda)^(-T)Omega(I-Lambda)^(-1). In the complexified source function field L=C(lambda_D,omega_B,omega_diag), let K_G=C(sigma_ij) be the covariance subfield. Define d_e(G)=[K_G(lambda_e):K_G] when algebraic, infinity otherwise, and D_k(n)=max finite d_e(G) over this entire graph class and directed-edge queries. This is SINGLE-COORDINATE complex generic degree, not whole-fiber degree, real root count, or local Jacobian rank.\n\nKERNEL: determine D_k(n) sharply for EVERY admissible (n,k), by an explicit formula or structural recurrence solely in n,k, a universal upper bound and constructive attaining graph families. Give a complete randomized algorithm on (G,T,e,delta) returning d_e and, when finite, its monic minimal polynomial over K_G with coefficients represented by rational arithmetic circuits in covariance entries. Supply an explicit proper algebraic exceptional set outside which the polynomial's roots are exactly the complex queried-coordinate projection. Require construction time and certificate length n^{C(k+1)} poly(log(1/delta)) for universal C in a specified exact-arithmetic/PIT model, with symbolic error probability at most delta. The exact frontier, recurrence and mechanics remain answer-open; the sharpness, full size scope and certificate guarantees are commitments. Generic exposure plus black-box elimination alone is not the hard theorem. For regular positive-definite specializations separately retain real roots iff they extend to real directed coefficients satisfying the missing-bidirected equations; positive definiteness of recovered Omega follows by congruence. Do not assert real uniqueness from complex degree or local rank.\n\nESTIMATION RUNG: at fixed G,n and compact smooth covariance-model subsets with certificate denominators bounded away from zero, simple uniformly separated retained roots, and locally constant real-extension status, construct a sample-covariance/model-projection finite-set estimator with root-m sample-size Hausdorff rate and simultaneous asymptotic branch confidence neighborhoods. On singleton real fibers derive consistency and asymptotic normality. No discriminant-uniform inference or unjustified branch selection is claimed.\n\nGrounding: Gupta-Blaser AAAI2024 arXiv2311.14058 Theorem27 and Lemmas4/12/25 give scalar Mobius tree identification; Briefs-Blaser NeurIPS2025 accelerates the same 1/2/infinite tree predicate. Hollering-Misra-Sturma arXiv2604.20516 Theorems4.4/5.1 concern bounded-degree RATIONAL FORMULAS, not algebraic fiber degree. Foygel-Draisma-Drton arXiv1107.5552 already has higher-degree small SEMs, so one cubic/quartic example is not novel. The named consumer https://cran.r-universe.dev/fasttreeid/doc/manual.html currently accepts one parent per node and returns 0/1/2 with path/fraction/cycle certificates; this theorem extends that same workflow to added parents and higher finite ambiguity. INTERNAL ANTI-CONSTRAINT: active/eid_fanin_numedge_frontier's numerical bounded-two-parent supplied-covariance predicate and residual handle are occupied. Do not relabel that numerical algorithm, omit the sharp generic frontier, or claim its all-singular-covariance scope. A six-node tree-plus-one-arrow legal SPD witness has four distinct real pole-free values of one coefficient, recovered from two conics; exact verification files accompany the draft.\n\nPRESOLVE EVIDENCE REQUIRING VERIFICATION: The draft derives a proposed 2^(k+1) single-coordinate upper bound by freezing a coordinate transcendence basis, selecting residual Jacobian equations, and counting prescribed-indegree orientations in multihomogeneous Bezout. A one-sink family on 2k+4 vertices makes one original coefficient separate every branch. Exact rational checks verify degree-eight and degree-sixteen examples with positive-definite covariances and real simple branches; 715 bounded orientation graphs passed. Source-integral rank-one anchoring and Mobius propagation yield a proposed quadratic core in at most 2k coefficients. Positive-dimensional localization, zero/zero interactions, poles, real-extension limitations, and joint-versus-coordinate degree were checked. Old cubic/quartic examples and the active numerical handle are not novelty claims.\nUNRESOLVED BOTTLENECK: Prove the size-sensitive orientation-realization theorem, correcting forced covariance relations or infinity roots, to determine D_k(n) and attain it for every smaller n. The full symbolic complexity, exceptional-set certificate and regular real-set inference still require the draft's listed proofs; do not substitute the established-looking large-n result for the original all-n kernel.\nEARLY KILL TEST: Resolve rooted five-node k<=2 orientation predictions by exact saturated coordinate elimination, first lifting the modular quartic to characteristic zero. A strict gap stops the uncorrected realization conjecture; absent a tractable correction, pivot the all-n scope.\nSTRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_extra_parent_degree.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "kernel_substituted"
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  - "The promised sharp all-(n,k) coordinate-degree frontier is not delivered: this node leaves the entire positive-excess below-threshold strip open and replaces the requested recurrence/attaining families with an envelope and threshold result."
  - "The promised graph-input algorithm returning exact d_e and its minimal polynomial with certificates is still open; the current operational output is only an algebraicity tag and ceiling, while exact polynomial output requires a supplied source-prime chart."
reusable_artifacts:
  - path: discovery/core.json
    kind: other
    one_line: "Sound dependency graph for the orientation bound, large-size equality, threshold theorem, small-size results, and conditional exact-output machinery."
  - path: discovery/writeup.tex
    kind: other
    one_line: "Synchronized derivation note containing the repaired positive-dimensional counting argument and all explicitly marked open boundaries."
  - path: discovery/solve_thm_orientation_upper_bound.json
    kind: other
    one_line: "Reusable proof attempt for the universal single-coordinate orientation upper bound."
  - path: discovery/solve_thm_large_size_frontier.json
    kind: witness
    one_line: "Reusable construction and proof attempt attaining the upper envelope in the large-size regime."
  - path: reviews/review_math.json
    kind: other
    one_line: "Final independent soundness and citation-scope audit; PASS with all ten cited claims verified and attested."
  - path: reviews/review_rubric.json
    kind: other
    one_line: "Exact record of the two remaining promise gaps that force the downgrade."
seeds_burned:
  - index: 0
    one_liner: "seed:sharp-size-frontier"
    reason: "The sharp all-size frontier and unconditional chart-free minimal-polynomial construction remained open after exhaustive D0 work."
  - index: 2
    one_liner: "seed:fpt-minimal-polynomial"
    reason: "The sharp all-size frontier and unconditional chart-free minimal-polynomial construction remained open after exhaustive D0 work."
proof_attempt_summary: |
  The run developed and repaired a sound universal orientation upper bound, matching large-size constructions, the exact equality threshold n >= 2k+4, small-size results, and conditional geometric-resolution machinery; the final math review passed with all cited claims verified at their narrowed scope. The field-tier promise collapsed because the exact positive-excess frontier below that threshold, beginning with D_2(6), remained open, and the exact degree/minimal-polynomial algorithm still required a supplied source-prime chart. A future retry should reuse the orientation and construction infrastructure while supplying a genuinely size-sensitive realization theorem and a chart-free exact-output construction.
token_usage:
  complete: false
  orchestrator_tokens: 1152697
  pipeline_codex_tokens: 84244434
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 84244434
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# eid_extra_parent_degree / v1 — Downgraded

**Topic.** Sharp generic single-edge identification degree beyond trees, with fasttreeid as the software consumer (exactid; field target). Let G=(V,D,B) be a known acyclic mixed graph on n>=2 vertices, bows allowed, containing a supplied rooted spanning arborescence T and at most k additional directed edges, where 0<=k<=(n-1)(n-2)/2. The Gaussian linear SCM has arbitrary real directed coefficients and positive-definite noise covariance Omega with zeros at missing bidirected pairs; its exact observed covariance is Sigma=(I-Lambda)^(-T)Omega(I-Lambda)^(-1). In the complexified source function field L=C(lambda_D,omega_B,omega_diag), let K_G=C(sigma_ij) be the covariance subfield. Define d_e(G)=[K_G(lambda_e):K_G] when algebraic, infinity otherwise, and D_k(n)=max finite d_e(G) over this entire graph class and directed-edge queries. This is SINGLE-COORDINATE complex generic degree, not whole-fiber degree, real root count, or local Jacobian rank.

KERNEL: determine D_k(n) sharply for EVERY admissible (n,k), by an explicit formula or structural recurrence solely in n,k, a universal upper bound and constructive attaining graph families. Give a complete randomized algorithm on (G,T,e,delta) returning d_e and, when finite, its monic minimal polynomial over K_G with coefficients represented by rational arithmetic circuits in covariance entries. Supply an explicit proper algebraic exceptional set outside which the polynomial's roots are exactly the complex queried-coordinate projection. Require construction time and certificate length n^{C(k+1)} poly(log(1/delta)) for universal C in a specified exact-arithmetic/PIT model, with symbolic error probability at most delta. The exact frontier, recurrence and mechanics remain answer-open; the sharpness, full size scope and certificate guarantees are commitments. Generic exposure plus black-box elimination alone is not the hard theorem. For regular positive-definite specializations separately retain real roots iff they extend to real directed coefficients satisfying the missing-bidirected equations; positive definiteness of recovered Omega follows by congruence. Do not assert real uniqueness from complex degree or local rank.

ESTIMATION RUNG: at fixed G,n and compact smooth covariance-model subsets with certificate denominators bounded away from zero, simple uniformly separated retained roots, and locally constant real-extension status, construct a sample-covariance/model-projection finite-set estimator with root-m sample-size Hausdorff rate and simultaneous asymptotic branch confidence neighborhoods. On singleton real fibers derive consistency and asymptotic normality. No discriminant-uniform inference or unjustified branch selection is claimed.

Grounding: Gupta-Blaser AAAI2024 arXiv2311.14058 Theorem27 and Lemmas4/12/25 give scalar Mobius tree identification; Briefs-Blaser NeurIPS2025 accelerates the same 1/2/infinite tree predicate. Hollering-Misra-Sturma arXiv2604.20516 Theorems4.4/5.1 concern bounded-degree RATIONAL FORMULAS, not algebraic fiber degree. Foygel-Draisma-Drton arXiv1107.5552 already has higher-degree small SEMs, so one cubic/quartic example is not novel. The named consumer https://cran.r-universe.dev/fasttreeid/doc/manual.html currently accepts one parent per node and returns 0/1/2 with path/fraction/cycle certificates; this theorem extends that same workflow to added parents and higher finite ambiguity. INTERNAL ANTI-CONSTRAINT: active/eid_fanin_numedge_frontier's numerical bounded-two-parent supplied-covariance predicate and residual handle are occupied. Do not relabel that numerical algorithm, omit the sharp generic frontier, or claim its all-singular-covariance scope. A six-node tree-plus-one-arrow legal SPD witness has four distinct real pole-free values of one coefficient, recovered from two conics; exact verification files accompany the draft.

PRESOLVE EVIDENCE REQUIRING VERIFICATION: The draft derives a proposed 2^(k+1) single-coordinate upper bound by freezing a coordinate transcendence basis, selecting residual Jacobian equations, and counting prescribed-indegree orientations in multihomogeneous Bezout. A one-sink family on 2k+4 vertices makes one original coefficient separate every branch. Exact rational checks verify degree-eight and degree-sixteen examples with positive-definite covariances and real simple branches; 715 bounded orientation graphs passed. Source-integral rank-one anchoring and Mobius propagation yield a proposed quadratic core in at most 2k coefficients. Positive-dimensional localization, zero/zero interactions, poles, real-extension limitations, and joint-versus-coordinate degree were checked. Old cubic/quartic examples and the active numerical handle are not novelty claims.
UNRESOLVED BOTTLENECK: Prove the size-sensitive orientation-realization theorem, correcting forced covariance relations or infinity roots, to determine D_k(n) and attain it for every smaller n. The full symbolic complexity, exceptional-set certificate and regular real-set inference still require the draft's listed proofs; do not substitute the established-looking large-n result for the original all-n kernel.
EARLY KILL TEST: Resolve rooted five-node k<=2 orientation predictions by exact saturated coordinate elimination, first lifting the modular quartic to characteristic zero. A strict gap stops the uncorrected realization conjecture; absent a tractable correction, pivot the all-n scope.
STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_extra_parent_degree.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The all-(n,k) positive-excess frontier and unconditional chart-free exact finite output remain open; the sound residual is incremental.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/core.json` — final proof/dependency graph.
- `discovery/writeup.tex` — synchronized derivation note.
- `reviews/review_math.json` — final soundness and citation audit.
- `reviews/review_rubric.json` and `reviews/review_general.json` — surviving promise gaps and achieved-tier assessment.
- `orchestrator/decision_log.jsonl` — derivation, repair, maximality, and terminal-decision receipts.

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->

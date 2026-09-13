---
qid: exp_multiarm_sharp_secondorder_limit
spec: v1
topic: "Sharp second-order minimax limit and optimal joint procedures for binary-outcome multiarm trials. For every fixed K>=3 and fixed real contrast c with sum c=0, sum |c|=2 and at least three nonzero entries, nature fixes an arbitrary binary n-by-K potential-outcome schedule; the design is any outcome-independent assignment law, including dependence across units, and the estimator sees all assignment labels and observed outcomes. Target the finite-population contrast tau_c and squared-error minimax risk R_n(c) over all designs and arbitrary possibly biased estimators. The banked parent proves only the first-order value 1/n, the Theta(n^(-4/3)) improvement order and finite response-type certificates. Prove that L(c)=lim n^(4/3)(1/n-R_n(c)) exists in (0,infinity), derive an independently defined evaluable limiting decision object, construct total finite-data attaining procedures and matching all-procedure lower bounds, and prove an effective finite-to-limit certificate theorem. Give a terminating certified evaluator for rational c and an explicit real-contrast approximation route; do not assume arbitrary reals computable. Determine whether independent q*_a=|c_a|/2 attains the same second-order value, with equality or strict loss answer-open. No growing-K or uniform vanishing-weight claim. The finite K=3,n=3 full-label witness has risk 511653/4000000 below the scalar Bayes lower bound 18213/136000; do not assume that gap persists asymptotically. Consumer: prospective ACTG175-style complete fixed-horizon binary-endpoint regimen contrasts, not a reanalysis of its censored outcomes. The hard full limit, evaluable object and unrestricted converse are the kernel; another order bound or numerical extrapolation does not discharge it. Independently verify the presolve formula and all gaps.\n\nPRESOLVE EVIDENCE REQUIRING VERIFICATION: A finite response-alphabet LP defines kappa(c), and its dual gives an observable full-label shrinkage score. Presolve derives an Airy-corrected risk upper bound and solves an independent directional variational problem with value C_A kappa(c)^(2/3). For one-versus-many contrasts c=(1,-w), kappa equals the sum of squared averaging weights. Eleven rational primal-dual certificates passed independent exact checks, including repeated weights, inactive arms and near cancellations. These checks certify finite LP values, not the asymptotic risk theorem. The Taylor argument remains informal. A scalar-path-only prior fails because a pair-focused design can exploit it; a finite-sample label gap does not establish an asymptotic gap.\nUNRESOLVED BOTTLENECK: Prove the design-independent, full-dimensional Bayes-prior bridge uniformly over all allocation counts, dependent designs and labeled estimators, with effective finite-to-limit errors and a valid finite-population target identity. Sharp equality, convergence and second-order optimality of q* remain conditional on this step.\nEARLY KILL TEST: At c=(1,-1/4,-3/4), derive the eight-type tube-prior information expansion including n^(-1/6) allocation perturbations and boundary allocations. A persistent design-optimized deficit above the proposed value or failure of the uniform score identity kills this LP/Airy spine and requires a fresh answer-open derivation.\nSTRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_multiarm_sharp_secondorder_limit.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "kernel_substituted"
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  - "The proposal's fixed-K, every-permitted-contrast sharp-limit/evaluator kernel is replaced by a result only for cdagger=(1,-1/4,-3/4); the stated general qstar equality-or-strict-loss question and rational-c/general-real evaluation route are therefore not discharged."
  - "classification: status failed; proposal reusable=solver_blocked, not false-claim; proved cdagger artifacts remain mathematically reusable"
reusable_artifacts:
  - "discovery/core.json — proved fixed-independent-design sharp coefficient for general c, plus the cdagger unrestricted theorem, face-robust tangent construction, endpoint reduction, and binary-submodel comparison"
  - "discovery/writeup.tex — complete derivation and scope boundary for the cdagger unrestricted result"
  - "discovery/solve_thm_unequal_three_arm_allocation_tube.json — all-count Bayes bridge attempt and face/boundary analysis"
  - "discovery/solve_thm_qstar_second_order.json — attaining fixed-design Airy procedure and coefficient argument"
  - "reviews/review_math.json — clean mathematical review and source-match receipts after primary-source attestation"
seeds_burned: []
proof_attempt_summary: |
  The run built a response-alphabet/Airy program, repaired a false widening-tube prior with a face-robust construction, and derived a sharp unrestricted second-order theorem for cdagger=(1,-1/4,-3/4), together with general-c results under the fixed independent qstar design. The original promise required the unrestricted limit, evaluator, converse, and qstar design comparison for every permitted fixed K and c; that all-sign-partition bridge was never proved, so substituting the cdagger kill-test theorem for the promised kernel failed the fidelity gate. A future retry should reuse the proved artifacts but must supply genuinely general 2^K-response-alphabet tube, face, evaluator, and unrestricted-converse mathematics.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 139610840
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 139610840
  total_tokens_consumed: null
banked_on: "2026-09-10"
---

# exp_multiarm_sharp_secondorder_limit / v1 — Failed

**Topic.** Sharp second-order minimax limit and optimal joint procedures for binary-outcome multiarm trials. For every fixed K>=3 and fixed real contrast c with sum c=0, sum |c|=2 and at least three nonzero entries, nature fixes an arbitrary binary n-by-K potential-outcome schedule; the design is any outcome-independent assignment law, including dependence across units, and the estimator sees all assignment labels and observed outcomes. Target the finite-population contrast tau_c and squared-error minimax risk R_n(c) over all designs and arbitrary possibly biased estimators. The banked parent proves only the first-order value 1/n, the Theta(n^(-4/3)) improvement order and finite response-type certificates. Prove that L(c)=lim n^(4/3)(1/n-R_n(c)) exists in (0,infinity), derive an independently defined evaluable limiting decision object, construct total finite-data attaining procedures and matching all-procedure lower bounds, and prove an effective finite-to-limit certificate theorem. Give a terminating certified evaluator for rational c and an explicit real-contrast approximation route; do not assume arbitrary reals computable. Determine whether independent q*_a=|c_a|/2 attains the same second-order value, with equality or strict loss answer-open. No growing-K or uniform vanishing-weight claim. The finite K=3,n=3 full-label witness has risk 511653/4000000 below the scalar Bayes lower bound 18213/136000; do not assume that gap persists asymptotically. Consumer: prospective ACTG175-style complete fixed-horizon binary-endpoint regimen contrasts, not a reanalysis of its censored outcomes. The hard full limit, evaluable object and unrestricted converse are the kernel; another order bound or numerical extrapolation does not discharge it. Independently verify the presolve formula and all gaps.

PRESOLVE EVIDENCE REQUIRING VERIFICATION: A finite response-alphabet LP defines kappa(c), and its dual gives an observable full-label shrinkage score. Presolve derives an Airy-corrected risk upper bound and solves an independent directional variational problem with value C_A kappa(c)^(2/3). For one-versus-many contrasts c=(1,-w), kappa equals the sum of squared averaging weights. Eleven rational primal-dual certificates passed independent exact checks, including repeated weights, inactive arms and near cancellations. These checks certify finite LP values, not the asymptotic risk theorem. The Taylor argument remains informal. A scalar-path-only prior fails because a pair-focused design can exploit it; a finite-sample label gap does not establish an asymptotic gap.
UNRESOLVED BOTTLENECK: Prove the design-independent, full-dimensional Bayes-prior bridge uniformly over all allocation counts, dependent designs and labeled estimators, with effective finite-to-limit errors and a valid finite-population target identity. Sharp equality, convergence and second-order optimality of q* remain conditional on this step.
EARLY KILL TEST: At c=(1,-1/4,-3/4), derive the eight-type tube-prior information expansion including n^(-1/6) allocation perturbations and boundary allocations. A persistent design-optimized deficit above the proposed value or failure of the uniform score identity kills this LP/Airy spine and requires a fresh answer-open derivation.
STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_multiarm_sharp_secondorder_limit.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The proposal's fixed-K, every-permitted-contrast sharp-limit/evaluator kernel is replaced by a result only for cdagger=(1,-1/4,-3/4); the stated general qstar equality-or-strict-loss question and rational-c/general-real evaluation route are therefore not discharged.

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

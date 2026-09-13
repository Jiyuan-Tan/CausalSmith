---
qid: exp_multiarm_unrestricted_airy_universality
spec: v1
topic: "Universal response-alphabet Airy law for unrestricted multi-arm binary randomized experiments. For every fixed integer K>=3 and every fixed real contrast c in R^K with sum_a c_a=0, sum_a |c_a|=2, and at least three nonzero coordinates, nature chooses an arbitrary labelled n-by-K schedule of binary potential outcomes Y_i(a) in {0,1}. Before observing outcomes, the designer chooses any probability law on assignments Z in {1,...,K}^n, including dependent assignments; the estimator is any measurable function of the full assignment labels and observed outcomes. The target is tau_c=n^(-1) sum_i sum_a c_a Y_i(a), loss is squared error, and R_n(c) is the infimum over all such design-estimator pairs of the worst-schedule risk. With this normalization the accepted parent gives first-order value 1/n; define d_n(c)=1/n-R_n(c). Write S_c={a:c_a!=0}, s_c=(sign(c_a)) on S_c, v=s_c/2, T_c={0,1}^{S_c}, b_t=t-1/2 and theta_t=c^T t. For xi in R^{S_c}, define the finite response-alphabet gauge V_c(xi)=min{sum_{t in T_c} lambda_t theta_t^2: lambda_t>=0 and sum_t lambda_t b_t=xi}; define kappa(c)=V_c(v). Define C_A=inf over phi in H^1(R) with ||phi||_2=1 of integral_R {4|phi_prime(x)|^2+|x|phi(x)^2} dx, and Lambda_c=C_A kappa(c)^(2/3). Prove, for every fixed K and every c in the declared class, the unrestricted expansion R_n(c)=1/n-Lambda_c n^(-4/3)+o(n^(-4/3)), equivalently lim n^(4/3)d_n(c)=Lambda_c. The upper theorem must use the explicit independent allocation q*_a=|c_a|/2 on S_c and a total full-label nonlinear Airy estimator; the lower theorem must construct compatible finite-schedule priors proving the same coefficient uniformly against every dependent outcome-independent design and every randomized labelled-data estimator, including allocation faces with zero arm counts. Give, for every rational c and rational eta>0, a terminating certificate that returns N and exact rational/algebraic upper and lower risk witnesses whose normalized gap is <=eta for all n>=N; extend the mathematical coefficient and risk expansion to real c using explicit rational contrast bracketing and the accepted parent continuity modulus, without claiming a Turing evaluator for an unrepresented real. A theorem for one contrast, the already-proved fixed-q* expansion, another order bound, or numerical convergence alone does not satisfy the kernel. Consumer: Hammer et al. (1996), ACTG 175, compares four antiretroviral regimens. For a prospective ACTG-175-style fixed-horizon trial with a prespecified binary regimen-versus-average contrast, the theorem changes allocation and shrinkage away from procedures known to be only first-order minimax, and the certificate quantifies whether contrast-weighted independent assignment is genuinely second-order optimal. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A full-dimensional response tube with basis [v, basis of ker(cᵀ)] extends the prior exact-target Bayes argument to every fixed contrast. For positive active allocations, z_a=c_a/(q_a H(q)) is a convex combination of e_a/c_a, so nuisance coordinates remain bounded near every simplex face. The identity H(q)-4=4 sum_a (q_a-q*_a)^2/q_a+4(1-Q) controls exterior and inactive-arm allocations, while a missing active arm yields a target-changing direction with zero observed-likelihood information. Exact checks covered seven rational contrasts, 28 missing-arm directions and 49 positive-allocation cases, including mixed signs, repeated weights, zero subset sums and small coefficients. These checks validate finite geometry, not the asymptotic theorem; no external universal multi-arm closure was found. UNRESOLVED BOTTLENECK: Independently prove and make effective the general exact-target all-count Bayes inequality for the piecewise-polynomial tube, including weak integration by parts across sign cells and uniform local, exterior and zero-count remainder bounds. EARLY KILL TEST: For c=(1/3,2/3,-1/4,-3/4), verify the regression, variance decomposition and directional bounds on all 16 response types, then add an inactive arm; any failed target identity, uncovered allocation face, or unrestricted procedure beating C_A(11/36)^(2/3) kills the universal formula. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_multiarm_unrestricted_airy_universality.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "The accepted parent already establishes the unrestricted game first-order value, n^-4/3 rate, and certificate framework; the proposed sharp coefficient, convergence, and q-star second-order optimality were not positioned or verified strongly enough to clear field tier."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "D0.5.G tier=incremental < floor=field (target=field) and NOT salvageable in scope."
  - "D0.5.G projected paper-score gate: paper_score_ceiling 5.2 < 7.2, so the graded tier subfield is capped at incremental; no bounded fix in scope."
  - "Position the sharp multi-arm Airy law explicitly against accepted-bank exp_multiarm_secondorder_minimax_frontier_v1, which established this unrestricted game's first-order value, n^-4/3 rate, and certificate framework but left the sharp coefficient, convergence, and q-star second-order optimality open."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_prop_mixed_sign_kill_test.json
  - discovery/solve_thm_all_count_bayes_inequality.json
  - discovery/solve_thm_effective_certificate.json
  - discovery/solve_thm_universal_lower.json
seeds_burned:
  - index: 0
    one_liner: "seed:universal-response-alphabet-airy"
    reason: "Angle 0 exhausted three D-0.5 revisions; the cold typed gate remained below field."
proof_attempt_summary: |
  The run developed the response-alphabet gauge, a full-dimensional exact-target tube, an all-count
  Bayes lower-bound route, and an effective-certificate construction for the proposed universal Airy
  coefficient. The typed novelty gate nevertheless graded the result incremental: the accepted parent
  already owns the first-order value, n^-4/3 rate, and certificate framework, while the new coefficient,
  convergence, and q-star optimality were not positioned and verified strongly enough to clear field.
  The archived solve artifacts preserve the mixed-sign witness, all-count argument, lower bound, and
  certificate work for a future re-raised proposal.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 21602024
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 21602024
  total_tokens_consumed: null
banked_on: "2026-09-10"
---

# exp_multiarm_unrestricted_airy_universality / v1 — Downgraded

**Topic.** Universal response-alphabet Airy law for unrestricted multi-arm binary randomized experiments. For every fixed integer K>=3 and every fixed real contrast c in R^K with sum_a c_a=0, sum_a |c_a|=2, and at least three nonzero coordinates, nature chooses an arbitrary labelled n-by-K schedule of binary potential outcomes Y_i(a) in {0,1}. Before observing outcomes, the designer chooses any probability law on assignments Z in {1,...,K}^n, including dependent assignments; the estimator is any measurable function of the full assignment labels and observed outcomes. The target is tau_c=n^(-1) sum_i sum_a c_a Y_i(a), loss is squared error, and R_n(c) is the infimum over all such design-estimator pairs of the worst-schedule risk. With this normalization the accepted parent gives first-order value 1/n; define d_n(c)=1/n-R_n(c). Write S_c={a:c_a!=0}, s_c=(sign(c_a)) on S_c, v=s_c/2, T_c={0,1}^{S_c}, b_t=t-1/2 and theta_t=c^T t. For xi in R^{S_c}, define the finite response-alphabet gauge V_c(xi)=min{sum_{t in T_c} lambda_t theta_t^2: lambda_t>=0 and sum_t lambda_t b_t=xi}; define kappa(c)=V_c(v). Define C_A=inf over phi in H^1(R) with ||phi||_2=1 of integral_R {4|phi_prime(x)|^2+|x|phi(x)^2} dx, and Lambda_c=C_A kappa(c)^(2/3). Prove, for every fixed K and every c in the declared class, the unrestricted expansion R_n(c)=1/n-Lambda_c n^(-4/3)+o(n^(-4/3)), equivalently lim n^(4/3)d_n(c)=Lambda_c. The upper theorem must use the explicit independent allocation q*_a=|c_a|/2 on S_c and a total full-label nonlinear Airy estimator; the lower theorem must construct compatible finite-schedule priors proving the same coefficient uniformly against every dependent outcome-independent design and every randomized labelled-data estimator, including allocation faces with zero arm counts. Give, for every rational c and rational eta>0, a terminating certificate that returns N and exact rational/algebraic upper and lower risk witnesses whose normalized gap is <=eta for all n>=N; extend the mathematical coefficient and risk expansion to real c using explicit rational contrast bracketing and the accepted parent continuity modulus, without claiming a Turing evaluator for an unrepresented real. A theorem for one contrast, the already-proved fixed-q* expansion, another order bound, or numerical convergence alone does not satisfy the kernel. Consumer: Hammer et al. (1996), ACTG 175, compares four antiretroviral regimens. For a prospective ACTG-175-style fixed-horizon trial with a prespecified binary regimen-versus-average contrast, the theorem changes allocation and shrinkage away from procedures known to be only first-order minimax, and the certificate quantifies whether contrast-weighted independent assignment is genuinely second-order optimal. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A full-dimensional response tube with basis [v, basis of ker(cᵀ)] extends the prior exact-target Bayes argument to every fixed contrast. For positive active allocations, z_a=c_a/(q_a H(q)) is a convex combination of e_a/c_a, so nuisance coordinates remain bounded near every simplex face. The identity H(q)-4=4 sum_a (q_a-q*_a)^2/q_a+4(1-Q) controls exterior and inactive-arm allocations, while a missing active arm yields a target-changing direction with zero observed-likelihood information. Exact checks covered seven rational contrasts, 28 missing-arm directions and 49 positive-allocation cases, including mixed signs, repeated weights, zero subset sums and small coefficients. These checks validate finite geometry, not the asymptotic theorem; no external universal multi-arm closure was found. UNRESOLVED BOTTLENECK: Independently prove and make effective the general exact-target all-count Bayes inequality for the piecewise-polynomial tube, including weak integration by parts across sign cells and uniform local, exterior and zero-count remainder bounds. EARLY KILL TEST: For c=(1/3,2/3,-1/4,-3/4), verify the regression, variance decomposition and directional bounds on all 16 response types, then add an inactive arm; any failed target identity, uncovered allocation face, or unrestricted procedure beating C_A(11/36)^(2/3) kills the universal formula. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_multiarm_unrestricted_airy_universality.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** Stage 0.5 (typed) BELOW NOVELTY FLOOR: D0.5.G tier=incremental < floor=field and paper_score_ceiling 5.2 < 7.2; not salvageable in scope.

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

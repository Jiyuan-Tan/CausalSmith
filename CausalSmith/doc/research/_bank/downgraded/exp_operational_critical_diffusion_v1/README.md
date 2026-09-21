---
qid: exp_operational_critical_diffusion
spec: v1
topic: "Joint operational critical-diffusion inference and capacity design for service experiments. Consider two independent stationary finite-source arms of N participants. The control undesirable-count chain has birth rate lambda(N-k) and death rate tau*k; treatment has death rate tau*k+nu*min(k,M_N), with M_N=ceil(N*lambda/(lambda+tau+nu)+gamma*sqrt(N)). Over compact positive rate and gamma classes, for T_N tending to infinity with T_N=o(N^(1/8)), prove a uniform central limit law for the treatment-control occupation contrast at sqrt(N*T_N) scale. Derive the control OU and treatment piecewise-OU stationary limits, solve their Poisson equations, and estimate rates from marked transition counts and at-risk occupation times. Establish the fixed-staffing rate-score correction and uniformly valid fitted-center Wald intervals. Give certified quadrature for the variance and terminating interval branch-and-bound for J(gamma)=c_M*gamma+c_I*z*sqrt(V0+V_gamma) on a compact range. Credit Boutilier--Jonasson--Li--Yoeli arXiv:2407.21322 for separate fixed-N and fluid limits; Keheala tuberculosis-adherence staffing is the consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The score-blind presolve derived the exact finite-chain birth-death Poisson flux solution, uniform gradient bounds, a spectral-gap reduction, and the joint score identity Cov(S,R)=Gamma A. Holding implemented staffing fixed gives A=grad(a0)-D_H grad(a), so same-path fitted centering has residual variance V-A^T Gamma A rather than the naive V. At lambda=tau=nu=1 and gamma=0, quadrature gave V=0.4804862942 and residual variance 0.4076427604; exact finite-chain derivatives converge toward A. It also checked ceiling offsets, negative staffing offsets, OU limits, time scaling, rate-boundary clipping, pilots, event marks, initialization, arm dependence, and vanishing-rate boundaries, and found no same-theorem collision in bounded current-literature checks. UNRESOLVED BOTTLENECK: Prove uniformly over the compact rate and staffing window that the stationary expectation of the absolute generator residual is O(N^(-1/2)), including jumps crossing the piecewise-drift kink; this yields the O(N^(-1)) effect-centering error required by the fitted Wald limit. EARLY KILL TEST: Establish that generator-residual bound directly from the piecewise-Gaussian Poisson solution and stress-test its scaled constant against exact stationary products at asymmetric rate-box corners and ceiling phases; a genuine nonvanishing residual stops or pivots the route. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_operational_critical_diffusion.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "No substantive staffing exercise or application-level evidence shows that the recommendation changes operational decisions; the delivered theory remains constrained to stationary initialization, observed recovery-cause marks, independent equal-sized arms, homogeneous rates, and a known compact critical-staffing regime."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "Its econometric reach is constrained by stationary initialization, observed recovery-cause marks, independent equal-sized arms, homogeneous rates, and a known compact critical-staffing regime."
  - "The capacity result optimizes a model-specific staffing-versus-interval-width objective using supplied rate inputs and computable-real receipts, but provides neither an instantiated certificate nor a substantive staffing exercise showing that the recommendation changes operational decisions."
  - "These restrictions and the absence of reproducible application-level evidence keep the package below flagship significance despite the delivered field-level theory."
  - "Not salvageable within scope — bank downgraded, or re-anchor the proposal (rewind D-1.2)."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_oeq_kink_residual.json
  - discovery/solve_thm_fitted_center_wald.json
  - discovery/solve_thm_certified_capacity_design.json
  - discovery/solve_thm_finite_design_regret.json
  - reviews/review_general.json
  - reviews/review_math.json
  - reviews/review_rubric.json
seeds_burned:
  - index: 0
    one_liner: "uniform-critical-occupation-law"
    reason: "The selected critical-diffusion angle was fully solved and reviewed, but its equal-arm stationary homogeneous marked-history scope and lack of substantive application-level evidence cap the package below field."
proof_attempt_summary: |
  The run proved the compact-uniform critical occupation/score limit, the kink-inclusive
  generator-residual bound, exact fixed-capacity fitted-center Wald theory, and an
  oracle-relative capacity certificate and finite-system regret transfer. The mathematics
  survived D0 review and the Boutilier scope citation was verified directly, but D0.5 capped
  the package at subfield because the stationary equal-arm marked-history model and absence
  of an instantiated operational application do not clear the field-level significance bar.
  A future re-raise should re-anchor around a broader empirical or design contribution rather
  than repeat the completed critical-diffusion derivations.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 31582566
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 31582566
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# exp_operational_critical_diffusion / v1 — Downgraded

**Topic.** Joint operational critical-diffusion inference and capacity design for service experiments. Consider two independent stationary finite-source arms of N participants. The control undesirable-count chain has birth rate lambda(N-k) and death rate tau*k; treatment has death rate tau*k+nu*min(k,M_N), with M_N=ceil(N*lambda/(lambda+tau+nu)+gamma*sqrt(N)). Over compact positive rate and gamma classes, for T_N tending to infinity with T_N=o(N^(1/8)), prove a uniform central limit law for the treatment-control occupation contrast at sqrt(N*T_N) scale. Derive the control OU and treatment piecewise-OU stationary limits, solve their Poisson equations, and estimate rates from marked transition counts and at-risk occupation times. Establish the fixed-staffing rate-score correction and uniformly valid fitted-center Wald intervals. Give certified quadrature for the variance and terminating interval branch-and-bound for J(gamma)=c_M*gamma+c_I*z*sqrt(V0+V_gamma) on a compact range. Credit Boutilier--Jonasson--Li--Yoeli arXiv:2407.21322 for separate fixed-N and fluid limits; Keheala tuberculosis-adherence staffing is the consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The score-blind presolve derived the exact finite-chain birth-death Poisson flux solution, uniform gradient bounds, a spectral-gap reduction, and the joint score identity Cov(S,R)=Gamma A. Holding implemented staffing fixed gives A=grad(a0)-D_H grad(a), so same-path fitted centering has residual variance V-A^T Gamma A rather than the naive V. At lambda=tau=nu=1 and gamma=0, quadrature gave V=0.4804862942 and residual variance 0.4076427604; exact finite-chain derivatives converge toward A. It also checked ceiling offsets, negative staffing offsets, OU limits, time scaling, rate-boundary clipping, pilots, event marks, initialization, arm dependence, and vanishing-rate boundaries, and found no same-theorem collision in bounded current-literature checks. UNRESOLVED BOTTLENECK: Prove uniformly over the compact rate and staffing window that the stationary expectation of the absolute generator residual is O(N^(-1/2)), including jumps crossing the piecewise-drift kink; this yields the O(N^(-1)) effect-centering error required by the fitted Wald limit. EARLY KILL TEST: Establish that generator-residual bound directly from the piecewise-Gaussian Poisson solution and stress-test its scaled constant against exact stationary products at asymmetric rate-box corners and ceiling phases; a genuine nonvanishing residual stops or pivots the route. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_operational_critical_diffusion.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G tier=subfield < floor=field and NOT salvageable in scope.

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

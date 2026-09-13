---
qid: stat_napkin_continuous_global_efficiency
spec: v1
topic: "Primitive growing-sieve attainment of the full-arm continuous-Napkin efficiency bound. In the iid mean-scale Verma model with W in a fixed finite alphabet with cell masses bounded below, continuous Z on [0,1], J>=3 treatment arms, bounded noisy outcomes, uniform overlap, and cellwise one-dimensional Holder smoothness s>1, target tau=c'psi with zero entries allowed. Define the regular averaged-score operator directly, with Lq=c and C=M_D+T*T, never through a fixed-z influence function. Derive the uniformly coercive full-arm optimizer q*=C^(-1)L*(LC^(-1)L*)^(-1)c, its efficiency bound, and a necessary-and-sufficient projection condition for strict gains from zero-contrast arms, including the checked three-arm odd-h witness. For B-spline dimension K_n=n^kappa with 1/(4s)<kappa<1/4, construct a cellwise cross-fitted plug-in Galerkin estimator and prove dimension-free operator perturbation, the exact training-dependent weighted-Verma remainder, global-bound asymptotic linearity, ratio-consistent variance, and uniform Wald coverage. Report a held-out Galerkin residual and active-only versus full-arm gain diagnostic; do not claim continuous/high-dimensional-W adaptation. PRESOLVE EVIDENCE REQUIRING VERIFICATION: For fixed finite W, the plug-in multiplication-plus-finite-rank operator has a derived O_P(rho_n) operator-norm route without a K_n factor. An exact fold-conditional bias identity is second order in nuisance errors; the corrected witness yields strict gain 3 gamma^2 gamma_3^2/(sigma_3^2/3+2 gamma_3^2), and cubic-spline oracle solves converge with constraint error below 5e-16. Current checks found no collision beyond the occupied abstract geometry and fixed-basis optimization. UNRESOLVED BOTTLENECK: Prove the uniform finite-n cellwise local-polynomial concentration lemma, including endpoint bins, denominator/clipping/fallback events and measurability, while retaining rho_n without a sieve multiplier. EARLY KILL TEST: Reproduce the passed s=2, kappa=3/16 dimension-free operator and exact bias bounds; any unavoidable multiplier that closes the rate window should pivot or stop. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_napkin_continuous_global_efficiency.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: REVISE
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The asymptotic held-out certificate quantifies only over an integer M>K_n although K_n grows; it needs an explicit sequence M_n and growth conditions sufficient for covariance convergence on V_{M_n}^J."
  - "The model class contains only observed-data laws satisfying a mean-Verma equality, but the proposal repeatedly concludes a Napkin intervention-mean/causal interpretation without declaring the required Napkin SCM or potential-outcome identification assumptions."
reusable_artifacts:
  - "discovery/proto_core.json — final operator, Galerkin, inactive-arm frontier, and odd-h witness specification; reuse only after removing the population diagnostic sentence and repairing causal scope."
  - "reviews/angle0_v8.json — final field-tier review and exact causal-scope failure receipt."
seeds_burned: []
proof_attempt_summary: |
  Eight D-0.5 proposal revisions successively repaired witness feasibility, source attribution,
  observed-law target definitions, and the restricted odd-h comparison, while preserving the proposed
  full-arm efficiency and growing-sieve attainment kernel. The final authorized retry deleted the
  asymptotic diagnostic theorem but retained forbidden population-certificate language and still
  overclaimed causal interpretation from an observed-law mean-Verma model, so discovery never passed
  D-0.5 and no Lean proof stage began.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 26779145
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 26779145
  total_tokens_consumed: null
banked_on: "2026-09-12"
---

# stat_napkin_continuous_global_efficiency / v1 — Failed

**Topic.** Primitive growing-sieve attainment of the full-arm continuous-Napkin efficiency bound. In the iid mean-scale Verma model with W in a fixed finite alphabet with cell masses bounded below, continuous Z on [0,1], J>=3 treatment arms, bounded noisy outcomes, uniform overlap, and cellwise one-dimensional Holder smoothness s>1, target tau=c'psi with zero entries allowed. Define the regular averaged-score operator directly, with Lq=c and C=M_D+T*T, never through a fixed-z influence function. Derive the uniformly coercive full-arm optimizer q*=C^(-1)L*(LC^(-1)L*)^(-1)c, its efficiency bound, and a necessary-and-sufficient projection condition for strict gains from zero-contrast arms, including the checked three-arm odd-h witness. For B-spline dimension K_n=n^kappa with 1/(4s)<kappa<1/4, construct a cellwise cross-fitted plug-in Galerkin estimator and prove dimension-free operator perturbation, the exact training-dependent weighted-Verma remainder, global-bound asymptotic linearity, ratio-consistent variance, and uniform Wald coverage. Report a held-out Galerkin residual and active-only versus full-arm gain diagnostic; do not claim continuous/high-dimensional-W adaptation. PRESOLVE EVIDENCE REQUIRING VERIFICATION: For fixed finite W, the plug-in multiplication-plus-finite-rank operator has a derived O_P(rho_n) operator-norm route without a K_n factor. An exact fold-conditional bias identity is second order in nuisance errors; the corrected witness yields strict gain 3 gamma^2 gamma_3^2/(sigma_3^2/3+2 gamma_3^2), and cubic-spline oracle solves converge with constraint error below 5e-16. Current checks found no collision beyond the occupied abstract geometry and fixed-basis optimization. UNRESOLVED BOTTLENECK: Prove the uniform finite-n cellwise local-polynomial concentration lemma, including endpoint bins, denominator/clipping/fallback events and measurability, while retaining rho_n without a sieve multiplier. EARLY KILL TEST: Reproduce the passed s=2, kappa=3/16 dimension-free operator and exact bias bounds; any unavoidable multiplier that closes the rate window should pivot or stop. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_napkin_continuous_global_efficiency.md.

**Novelty target.** field

**Stage -0.5 verdict.** REVISE

**Stage 0.5 verdict.** NA

**Banking reason.** The final D-0.5 retry violated the approved finite-sample-only diagnostic scope and the reviewer found an unresolved causal/intervention-interpretation C-coherence defect.

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

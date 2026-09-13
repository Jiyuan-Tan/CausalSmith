---
qid: stat_spatial_slope_infill_phase
spec: v2
topic: "Adaptive root-N inference through a vanishing spatial-confounding cross-tail. For d in {1,2}, observe X(s_i) and Y(s_i)=beta X(s_i)+W(s_i) on deterministic quasi-uniform designs in a fixed bounded Lipschitz domain, with fill distance comparable to N^(-1/d), separation comparable to fill distance, and bounded local-stencil degree. Let (X,W) be a centered stationary bivariate Gaussian field with Matérn marginal smoothness one-half, compact positive scales and ranges, and cross-spectrum A(alpha_C^2+||omega||^2)^(-(p+d/2)), where p lies in a fixed compact subinterval of (1/2,1), A may have either sign or vanish, and the spectral determinant has a fixed positive margin. Construct three or more nested affine-annihilating local-stencil slope statistics and a finite-dimensional profile confidence set for beta over the observation-scale tail amplitude and p. Prove a uniform actual-design Gaussian experiment, feasible residual-scale studentization, asymptotic 1-alpha coverage through every sequence A_N->0, O(N^(-1/2)) worst-case expected diameter and squared-risk O(N^(-1)), plus a matching honest-length lower bound. Explicitly control boundary, aliasing, irregular-design, denominator and Matérn remainder terms; do not assume independent Fourier coordinates, known p, efficient constants, unknown marginal smoothness adaptation, or a broader covariance class. Use Burman-Ogburn-Datta's PM2.5/COVID county-centroid homogeneous slope as the conditional applied consumer when the Matérn and design diagnostics hold. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Three scales have the exact annihilator (tu,-t-u,1), orthogonal to both power-law nuisance directions v(t)=(1,t,t^2) and v(u), while its inner product with the slope direction is (t-1)(u-1); compact p-bounds therefore separate beta uniformly even when amplitude is zero. Reparameterizing the nuisance as the observation-scale amplitude B=A K(p)h^(2p-1) absorbs the apparent log(h) derivative. On the actual one-dimensional OU lattice this yields a conservative honest root-N profile interval, and an exact Gaussian KL calculation matches the rate. Exact-design affine stencil means and covariances plus numerical Bessel checks support the irregular d=2 route; affine annihilation removes its O(h) analytic bias and first-difference log-variance obstruction. Checks covered zero and sign-changing amplitudes, unidentifiable p, the two-scale failure, local and diverging amplitudes, exponent endpoints, boundary effects, unestimable ranges, and large variance constants; no complete current-literature collision was found. UNRESOLVED BOTTLENECK: Prove uniform Gaussian profile calibration and mathematical attainment of the least-favorable quantile on the actual quasi-uniform designs across all local-amplitude and exponent-boundary sequences. A terminating certified numerical approximation, with a proved error bound, is an explicit residual open question rather than a promised delivered object. EARLY KILL TEST: On adversarially perturbed d=2 quasi-uniform designs, certify a positive divided-difference separation constant for the exact affine-stencil moment curve, including coincident exponents, and verify the exact Bessel mean remainder is o(h); failure for every allowed fixed-radius construction forces a design/scope pivot. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_spatial_slope_infill_phase.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "tier_genuinely_below"
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The paper score is constrained by the narrow parametric model, the absence of a certified implementation or substantive application, and the compressed treatment of load-bearing arbitrary-design covariance-remainder and quadratic-form CLT bounds."
  - "The lower bound comes from the regular independent A=0 subexperiment and therefore matches the rates without establishing that vanishing cross-tail adaptation creates a distinct minimax difficulty."
reusable_artifacts:
  - "discovery/core.json — proved theorem graph, exact attainable calibration, superclass lower-bound transfer, and final literature map"
  - "discovery/solve_thm_profile_inference.json — multiscale profile-inference derivation"
  - "discovery/solve_thm_exact_attainable_calibration.json — exact finite-design Gaussian-reference calibration derivation"
  - "discovery/solve_thm_honest_confidence_set_lower_bound.json — arbitrary measurable confidence-set lower-bound derivation"
  - "discovery/writeup.tex — final sound derivation note"
seeds_burned:
  - index: 0
    one_liner: "seed:uniform-profile"
    reason: "The accepted proposal was fully developed and repaired, but its narrow exact Matérn-one-half class, residual certified computation, and lack of substantive application capped it below field."
proof_attempt_summary: |
  The run constructed the affine-stencil experiment, uniform profile inference through vanishing cross-tail amplitude, exact attained Gaussian-reference calibration, and matching root-N confidence-set diameter and N^-1 risk lower bounds; both final review panels passed with no findings. The result remained below field because its upper theorem is confined to a narrow no-nugget Matérn-one-half class, its lower bound uses the regular independent subexperiment rather than a new weak-tail minimax obstruction, and no certified implementation or substantive application was delivered. A terminating certified approximation to the continuum critical value remains an explicit open question.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 37284432
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 37284432
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# stat_spatial_slope_infill_phase / v2 — Downgraded

**Topic.** Adaptive root-N inference through a vanishing spatial-confounding cross-tail. For d in {1,2}, observe X(s_i) and Y(s_i)=beta X(s_i)+W(s_i) on deterministic quasi-uniform designs in a fixed bounded Lipschitz domain, with fill distance comparable to N^(-1/d), separation comparable to fill distance, and bounded local-stencil degree. Let (X,W) be a centered stationary bivariate Gaussian field with Matérn marginal smoothness one-half, compact positive scales and ranges, and cross-spectrum A(alpha_C^2+||omega||^2)^(-(p+d/2)), where p lies in a fixed compact subinterval of (1/2,1), A may have either sign or vanish, and the spectral determinant has a fixed positive margin. Construct three or more nested affine-annihilating local-stencil slope statistics and a finite-dimensional profile confidence set for beta over the observation-scale tail amplitude and p. Prove a uniform actual-design Gaussian experiment, feasible residual-scale studentization, asymptotic 1-alpha coverage through every sequence A_N->0, O(N^(-1/2)) worst-case expected diameter and squared-risk O(N^(-1)), plus a matching honest-length lower bound. Explicitly control boundary, aliasing, irregular-design, denominator and Matérn remainder terms; do not assume independent Fourier coordinates, known p, efficient constants, unknown marginal smoothness adaptation, or a broader covariance class. Use Burman-Ogburn-Datta's PM2.5/COVID county-centroid homogeneous slope as the conditional applied consumer when the Matérn and design diagnostics hold. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Three scales have the exact annihilator (tu,-t-u,1), orthogonal to both power-law nuisance directions v(t)=(1,t,t^2) and v(u), while its inner product with the slope direction is (t-1)(u-1); compact p-bounds therefore separate beta uniformly even when amplitude is zero. Reparameterizing the nuisance as the observation-scale amplitude B=A K(p)h^(2p-1) absorbs the apparent log(h) derivative. On the actual one-dimensional OU lattice this yields a conservative honest root-N profile interval, and an exact Gaussian KL calculation matches the rate. Exact-design affine stencil means and covariances plus numerical Bessel checks support the irregular d=2 route; affine annihilation removes its O(h) analytic bias and first-difference log-variance obstruction. Checks covered zero and sign-changing amplitudes, unidentifiable p, the two-scale failure, local and diverging amplitudes, exponent endpoints, boundary effects, unestimable ranges, and large variance constants; no complete current-literature collision was found. UNRESOLVED BOTTLENECK: Prove uniform Gaussian profile calibration and mathematical attainment of the least-favorable quantile on the actual quasi-uniform designs across all local-amplitude and exponent-boundary sequences. A terminating certified numerical approximation, with a proved error bound, is an explicit residual open question rather than a promised delivered object. EARLY KILL TEST: On adversarially perturbed d=2 quasi-uniform designs, certify a positive divided-difference separation constant for the exact affine-stencil moment curve, including coincident exponents, and verify the exact Bessel mean remainder is o(h); failure for every allowed fixed-radius construction forces a design/scope pivot. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_spatial_slope_infill_phase.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G tier=subfield < floor=field; clean math and decision panels passed with no findings, but paper_score_ceiling 7.1 < 7.4 and no bounded same-topic repair can lift it.

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

---
qid: panel_bivariate_cic_critical_transport_inference
spec: v1
topic: "Critical-plane inference for nested Brenier difference-in-differences. Under the published two-group/two-period cyclic-comonotonicity identification assumptions, take four independent samples from C^s, s>=8, uniformly positive densities on the two-dimensional flat torus with uniformly elliptic Brenier potentials. For p=OT(P_C0,P_C1), Pdagger_T1=p#P_T0, and Tdagger=OT(P_T1,Pdagger_T1), prove that a specified order-s positive-normalized periodized-KDE/Monge-Ampere plug-in has a joint fixed-grid Gaussian limit at sqrt(n/log(1/h)); derive the full four-cell nested critical Green covariance including generated-target cross terms; consistently estimate it by adjoint elliptic solves; give simultaneous multiplier ellipses for y-Tdagger(y); and match log(1/h)/n squared risk by a Hellinger-local minimax lower bound. Use the explicit smooth separable torus witness and target the Card-Krueger bivariate employment reanalysis. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Pulling both transports into treated-post coordinates gives exactly M=(f_T0/f_C0)C for the inner and generated-pushforward elliptic coefficients, reducing the nested derivative to one outer Green response to four weighted noises plus an order-minus-two remainder. This rules out independent-cell cancellation and predicts covariance blocks V_j=w_j sqrt(det DT(y_j))DT(y_j)/(4pi f_T1(y_j)); matrix identities, angular constants, bandwidth feasibility, clipping, and the separable witness were checked, and no collision was found including an August 2026 potential-CLT follow-up. UNRESOLVED BOTTLENECK: Prove uniformly that the full transformed-KDE variable-coefficient Green response has the stated log-normalized covariance while generated-target and estimated-coefficient/pole remainders are negligible. EARLY KILL TEST: On one nonseparable smooth torus example with nonconstant f_T0/f_C0, compute adjoint covariance increments at h,h/2,h/4,h/8 with resolved discretization error; stop or pivot if logarithmic slopes miss the formula or the remainder diverges logarithmically. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/panel_bivariate_cic_critical_transport_inference.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: null
reusable: unknown
reraise_status: unknown
gap_reasons:
  - >-
    The note advertises a proved Gaussian limit, feasible covariance, simultaneous ellipses, and
    matched risk, but every one of these results depends on the claimed uniform critical-control
    theorem.
  - >-
    That theorem obtains its central frozen-pole, moving-pole, coefficient-stability, and
    mixed-remainder conclusions by citing lem:uniform-critical-estimates, whose proof compresses the
    decisive transformed-kernel comparison into an unsupported dyadic-annulus assertion and invokes
    the unproved, uncited lem:one-map-mixed-linearization.
  - >-
    The missing analytic gate also invalidates the upper-risk half of the advertised matched rate and
    leaves no implemented Card–Krueger analysis or nonseparable numerical kill test to support
    practical significance.
  - >-
    cited-underspecified@lem:fixed-path-ma-linearization-source;
    positioning@thm:joint-critical-clt; positioning@thm:matched-critical-risk.
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_adjoint_covariance.json
  - discovery/solve_lem_mixed_bandwidth_feasibility.json
  - discovery/solve_oeq_uniform_critical_control.json
  - reviews/review_general.json
seeds_burned: []
proof_attempt_summary: |
  The run developed an intrinsic flat-torus changes-in-changes identification result, a
  translation-aware nested derivative with harmonic modes, bandwidth arithmetic, and separable or
  constant-coefficient checks. It repeatedly attempted to close the general variable-coefficient
  Green/KDE inference spine, but the final review found the annular comparison, moving-pole and
  coefficient stability, and generated-target mixed remainder asserted rather than proved. A future
  effort must supply those analytic estimates independently before claiming the CLT, covariance
  estimator, simultaneous ellipses, or matched upper risk.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 72137307
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 72137307
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# panel_bivariate_cic_critical_transport_inference / v1 — Downgraded

**Topic.** Critical-plane inference for nested Brenier difference-in-differences. Under the published two-group/two-period cyclic-comonotonicity identification assumptions, take four independent samples from C^s, s>=8, uniformly positive densities on the two-dimensional flat torus with uniformly elliptic Brenier potentials. For p=OT(P_C0,P_C1), Pdagger_T1=p#P_T0, and Tdagger=OT(P_T1,Pdagger_T1), prove that a specified order-s positive-normalized periodized-KDE/Monge-Ampere plug-in has a joint fixed-grid Gaussian limit at sqrt(n/log(1/h)); derive the full four-cell nested critical Green covariance including generated-target cross terms; consistently estimate it by adjoint elliptic solves; give simultaneous multiplier ellipses for y-Tdagger(y); and match log(1/h)/n squared risk by a Hellinger-local minimax lower bound. Use the explicit smooth separable torus witness and target the Card-Krueger bivariate employment reanalysis. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Pulling both transports into treated-post coordinates gives exactly M=(f_T0/f_C0)C for the inner and generated-pushforward elliptic coefficients, reducing the nested derivative to one outer Green response to four weighted noises plus an order-minus-two remainder. This rules out independent-cell cancellation and predicts covariance blocks V_j=w_j sqrt(det DT(y_j))DT(y_j)/(4pi f_T1(y_j)); matrix identities, angular constants, bandwidth feasibility, clipping, and the separable witness were checked, and no collision was found including an August 2026 potential-CLT follow-up. UNRESOLVED BOTTLENECK: Prove uniformly that the full transformed-KDE variable-coefficient Green response has the stated log-normalized covariance while generated-target and estimated-coefficient/pole remainders are negligible. EARLY KILL TEST: On one nonseparable smooth torus example with nonconstant f_T0/f_C0, compute adjoint covariance increments at h,h/2,h/4,h/8 with resolved discretization error; stop or pivot if logarithmic slopes miss the formula or the remainder diverges logarithmically. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/panel_bivariate_cic_critical_transport_inference.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G tier=incremental < floor=field and NOT salvageable in scope; the critical inference spine remains unsupported.

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

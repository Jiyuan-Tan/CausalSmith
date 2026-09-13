---
qid: panel_nested_donor_honest_width_frontier
spec: v1
topic: "Honest-width frontier for horizon-adaptive nested donor pools in staggered synthetic controls. Fix finite treated units and horizons, deterministic adoption dates, observed predictors x_i, and deduplicated unit-calendar-time untreated outcomes with conditional means m_it=x_i' beta_t+r_it, ||beta_t||<=L, |r_it|<=delta/2, and known Gaussian covariance Sigma_Q with eigenvalues in a fixed positive band. For each treated j and horizon h let D_jh={i:T_i>T_j+h}. Among deterministic linear-SC rectangular bands whose weights and half-widths depend only on fixed design/model inputs, define W_nested by horizon-specific support D_jh and W_deep by common support D_jK, under uniform joint 1-alpha coverage. Characterize W_nested up to universal constants using a fixed-Bonferroni bias-plus-standard-error SOCP, prove a matching lower bound and finite-sample coverage, prove W_nested<=W_deep, and give a necessary-and-sufficient primal-dual certificate for strict improvement valid on degenerate active faces. Treat correlated Gaussian-max calibration only as a post-solve refinement. Consumers are scpi and augsynth::multisynth. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The prediction error was derived as one observable worst-case bias radius plus a Gaussian contrast on the deduplicated unit–calendar-time vector. With a fixed Bonferroni multiplier, minimizing the maximum bias-plus-standard-error envelope under simplex and nested-support constraints is a genuine SOCP with finite-sample simultaneous coverage; correlated Gaussian-max calibration is only a post-solve refinement. Each contrast retains a unique treated coordinate, so its contrast Gram matrix is at least the identity and the covariance is uniformly bounded below by sigma_min. Together with coordinatewise attainable bias shifts and an Anderson Gaussian-cube bound, this yields a finite constant-factor comparison between the SOCP envelope and exact robust width, subject to formal verification. Nested feasible-set inclusion proves width cannot worsen. In the two-horizon witness, optimized early nested weights (50/51,1/102,1/102) give variance 101/5100 versus 51/100 for deepest-pool support, with common second-horizon variance 3/200; exact 95% simultaneous full widths were computed as 0.593131 versus 2.799389. No collision was found with CFPT, partially pooled staggered synthetic controls, scpi/multisynth, or Cao–Lu–Wu. UNRESOLVED BOTTLENECK: Prove a necessary-and-sufficient nested-primal/deep-dual strict-gap certificate that remains valid on degenerate active faces, using relative-interior strong duality and interval-certified positive gaps. EARLY KILL TEST: Formalize the covariance-domination/Anderson sandwich and the finite Gaussian-quantile ratio bound; pivot if any legal deduplicated design with fixed eigenvalue bounds violates either inequality or makes the ratio diverge."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REVISE
proposal_promise_gap: "kernel_substituted"
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The note proves an exact finite-dimensional Gaussian decision frontier and an honest Bonferroni SOCP approximation, but only for deterministic weights in a bespoke bounded-mean experiment with known covariance."
  - "The necessary-and-sufficient degeneracy-safe certificate concerns strict improvement of the Bonferroni surrogate Gamma, while strict improvement of the exact frontier W is established only under zero bias with Loewner or disjoint-diagonal structure and for one constructed witness."
  - "References to scpi and augsynth::multisynth as consumers therefore exceed what is operationally transferred, even though the prose correctly disclaims coverage for those procedures."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_constant_factor_frontier.json
  - discovery/solve_thm_degenerate_iff_gap_certificate.json
  - discovery/solve_thm_disjoint_diagonal_exact_frontier.json
  - discovery/solve_prop_strict_witness_gap.json
seeds_burned: []
proof_attempt_summary: |
  The run derived the attainable joint-bias exact Gaussian width frontier, a finite-sample
  Bonferroni SOCP with a constant-factor spectral guarantee, correlated and disjoint-diagonal
  strictness criteria, a rational witness, and a degeneracy-safe strict-gap certificate. The
  mathematical bundle survived citation and real-algebraic-witness repairs, but the field claim
  collapsed because the model retains deterministic weights and known covariance rather than
  transferring uniform inference to a published staggered-SC estimator class. A future re-raise
  should add pretreatment covariance estimation under primitive published error conditions and
  prove that the robustified nested-support program preserves honesty and the frontier comparison.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 50836291
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-07"
---

# panel_nested_donor_honest_width_frontier / v1 — Downgraded

**Topic.** Honest-width frontier for horizon-adaptive nested donor pools in staggered synthetic controls. Fix finite treated units and horizons, deterministic adoption dates, observed predictors x_i, and deduplicated unit-calendar-time untreated outcomes with conditional means m_it=x_i' beta_t+r_it, ||beta_t||<=L, |r_it|<=delta/2, and known Gaussian covariance Sigma_Q with eigenvalues in a fixed positive band. For each treated j and horizon h let D_jh={i:T_i>T_j+h}. Among deterministic linear-SC rectangular bands whose weights and half-widths depend only on fixed design/model inputs, define W_nested by horizon-specific support D_jh and W_deep by common support D_jK, under uniform joint 1-alpha coverage. Characterize W_nested up to universal constants using a fixed-Bonferroni bias-plus-standard-error SOCP, prove a matching lower bound and finite-sample coverage, prove W_nested<=W_deep, and give a necessary-and-sufficient primal-dual certificate for strict improvement valid on degenerate active faces. Treat correlated Gaussian-max calibration only as a post-solve refinement. Consumers are scpi and augsynth::multisynth. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The prediction error was derived as one observable worst-case bias radius plus a Gaussian contrast on the deduplicated unit–calendar-time vector. With a fixed Bonferroni multiplier, minimizing the maximum bias-plus-standard-error envelope under simplex and nested-support constraints is a genuine SOCP with finite-sample simultaneous coverage; correlated Gaussian-max calibration is only a post-solve refinement. Each contrast retains a unique treated coordinate, so its contrast Gram matrix is at least the identity and the covariance is uniformly bounded below by sigma_min. Together with coordinatewise attainable bias shifts and an Anderson Gaussian-cube bound, this yields a finite constant-factor comparison between the SOCP envelope and exact robust width, subject to formal verification. Nested feasible-set inclusion proves width cannot worsen. In the two-horizon witness, optimized early nested weights (50/51,1/102,1/102) give variance 101/5100 versus 51/100 for deepest-pool support, with common second-horizon variance 3/200; exact 95% simultaneous full widths were computed as 0.593131 versus 2.799389. No collision was found with CFPT, partially pooled staggered synthetic controls, scpi/multisynth, or Cao–Lu–Wu. UNRESOLVED BOTTLENECK: Prove a necessary-and-sufficient nested-primal/deep-dual strict-gap certificate that remains valid on degenerate active faces, using relative-interior strong duality and interval-certified positive gaps. EARLY KILL TEST: Formalize the covariance-domination/Anderson sandwich and the finite Gaussian-quantile ratio bound; pivot if any legal deduplicated design with fixed eigenvalue bounds violates either inequality or makes the ratio diverge.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REVISE

**Banking reason.** D0.5 exhausted three revision rounds at achieved tier subfield below the field floor; the sound constant-factor honest-width frontier remains novel but theorem-level comparison and related-work coverage do not clear field.

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

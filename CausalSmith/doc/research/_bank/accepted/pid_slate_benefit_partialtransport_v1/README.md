---
qid: pid_slate_benefit_partialtransport
spec: v1
topic: "Sharp survivor-complier benefit bounds by partial transport. For finite ordered outcomes under conditional IV independence, treatment and outcome consistency and exclusion, instrument overlap, no defiers, positive aggregate survivor-complier mass, and covariate-specific weak selection monotonicity, identify the selected-complier outcome capacities in each covariate cell; prove that the single branch-free exact-mass partial-transport polytope is the exact projection of compatible laws and that the sharp endpoints of P(Y1>Y0 | S1=S0=1,D1>D0) have closed threshold min-cut formulas in both selection directions and on the zero-gap tie face, an O(|X|K) sparse-flow algorithm with O(|X|K^2) dense materialization, and endpoint-attaining full latent IV/selection laws. Estimate the observable capacities with the total nonnegative-projection plug-in estimator; derive its fixed-law Hadamard directional limit under arbitrary simultaneous threshold-cut ties, including positive-survivor zero-gap cells and screened zero-survivor cells; and give the explicit deterministic-guard confidence set whose containment of the entire identified interval tends to one uniformly under overlap and a uniform aggregate survivor-mass bound. Do not claim calibrated face-aware directional-multiplier inference: the multiplier face envelope is diagnostic only, and first-order exact unguarded uniform multiplier calibration under changing survivor support remains an open inference frontier. Include the three-level witness with survivor share 1/2, higher-arm mixture (0.2,0.5,0.3), lower-arm marginal (0.3,0.4,0.3), and sharp benefit interval [0,0.7]. Give a variable-level reinterpretation of the Chen-Flores Job Corps wage application—Z as offer assignment, D as program receipt, S as employment, and Y as an ordered wage category—without claiming an empirical reanalysis or transfer of their published bounds. VERIFIED CORE: using unnormalized cell masses ell_i=P(Y0=i,S0=1,C|x), h_j=P(Y1=j,S1=1,C|x), q0=sum_i ell_i, q1=sum_j h_j, and m=min(q0,q1), the exact projected polytope is Gamma_x*={gamma>=0: row(gamma)<=ell, col(gamma)<=h, sum gamma=m}; the sharp lower benefit mass is max(0,max_t(ell_{<=t}-h_{<=t})+min(q1-q0,0)) and the sharp upper mass is min(m,min_t(ell_{<t}+h_{>t})). These specialize to the directional formulas and agree on the tie face. The supplied witness gives masses 0 and 0.175, hence conditional endpoints 0 and 0.7. Direct full-LP checks matched the formulas on 100 random four-level instances in each direction, and the symbolic proof covers zero-survivor cells, atoms, cut ties, latent-mixture completion, and endpoint-attaining compatible full laws. OPEN INFERENCE FRONTIER: calibrate an estimated-active-face directional multiplier uniformly under simultaneous cut ties and changing survivor support without disguising the deterministic guard as multiplier calibration. EARLY KILL TEST PASSED: the finite-grid latent-type LP comparisons found no projected endpoint differing from the threshold formula."
novelty_target: field
banked_novelty_tier: field
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: null
reusable: unknown
reraise_status: unknown
gap_reasons:
  []
reusable_artifacts:
  - Causalean/Stat/Inference/HadamardDeriv.lean
  - Causalean/PO/Conditioning/CondExpTooling.lean
  - CausalSmith/PartialID/PID_SlateBenefitPartialtransport_Research/Helpers/WeakConvergenceTools.lean
  - CausalSmith/PartialID/PID_SlateBenefitPartialtransport_Research/Helpers/FullLawPasting.lean
  - discovery/core.json
  - discovery/writeup.tex
seeds_burned: []
proof_attempt_summary: |
  The run proved the exact branch-free partial-transport polytope, sharp threshold endpoints,
  explicit endpoint-attaining full laws, a sparse-flow construction, a fixed-law directional
  limit, and a uniform deterministic guard. Formalization exposed and repaired finite-sample,
  domain-pinning, full-law-pasting, and documentation gaps; the intentionally open frontier is
  calibrated face-aware multiplier inference under simultaneous ties and changing survivor support.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 408867711
  pipeline_claude_tokens: 99427278
  total_tokens_consumed: null
banked_on: "2026-09-05"
---

# pid_slate_benefit_partialtransport / v1 — Accepted

**Topic.** Sharp survivor-complier benefit bounds by partial transport. For finite ordered outcomes under conditional IV independence, treatment and outcome consistency and exclusion, instrument overlap, no defiers, positive aggregate survivor-complier mass, and covariate-specific weak selection monotonicity, identify the selected-complier outcome capacities in each covariate cell; prove that the single branch-free exact-mass partial-transport polytope is the exact projection of compatible laws and that the sharp endpoints of P(Y1>Y0 | S1=S0=1,D1>D0) have closed threshold min-cut formulas in both selection directions and on the zero-gap tie face, an O(|X|K) sparse-flow algorithm with O(|X|K^2) dense materialization, and endpoint-attaining full latent IV/selection laws. Estimate the observable capacities with the total nonnegative-projection plug-in estimator; derive its fixed-law Hadamard directional limit under arbitrary simultaneous threshold-cut ties, including positive-survivor zero-gap cells and screened zero-survivor cells; and give the explicit deterministic-guard confidence set whose containment of the entire identified interval tends to one uniformly under overlap and a uniform aggregate survivor-mass bound. Do not claim calibrated face-aware directional-multiplier inference: the multiplier face envelope is diagnostic only, and first-order exact unguarded uniform multiplier calibration under changing survivor support remains an open inference frontier. Include the three-level witness with survivor share 1/2, higher-arm mixture (0.2,0.5,0.3), lower-arm marginal (0.3,0.4,0.3), and sharp benefit interval [0,0.7]. Give a variable-level reinterpretation of the Chen-Flores Job Corps wage application—Z as offer assignment, D as program receipt, S as employment, and Y as an ordered wage category—without claiming an empirical reanalysis or transfer of their published bounds. VERIFIED CORE: using unnormalized cell masses ell_i=P(Y0=i,S0=1,C|x), h_j=P(Y1=j,S1=1,C|x), q0=sum_i ell_i, q1=sum_j h_j, and m=min(q0,q1), the exact projected polytope is Gamma_x*={gamma>=0: row(gamma)<=ell, col(gamma)<=h, sum gamma=m}; the sharp lower benefit mass is max(0,max_t(ell_{<=t}-h_{<=t})+min(q1-q0,0)) and the sharp upper mass is min(m,min_t(ell_{<t}+h_{>t})). These specialize to the directional formulas and agree on the tie face. The supplied witness gives masses 0 and 0.175, hence conditional endpoints 0 and 0.7. Direct full-LP checks matched the formulas on 100 random four-level instances in each direction, and the symbolic proof covers zero-survivor cells, atoms, cut ties, latent-mixture completion, and endpoint-attaining compatible full laws. OPEN INFERENCE FRONTIER: calibrate an estimated-active-face directional multiplier uniformly under simultaneous cut ties and changing survivor support without disguising the deterministic guard as multiplier calibration. EARLY KILL TEST PASSED: the finite-grid latent-type LP comparisons found no projected endpoint differing from the threshold formula.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** CKPT 2 approved: field-tier sharp partial-identification result with attained endpoints; fresh dual F4, F5, full build, source, axiom, and gate audits all clean.

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

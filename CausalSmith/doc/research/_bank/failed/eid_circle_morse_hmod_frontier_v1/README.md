---
qid: eid_circle_morse_hmod_frontier
spec: v1
topic: "Sharp full-law recovery modulus at Morse-critical circular interventions. On bounded C^k causal models over T^n with grouped positive single-node perfect interventions, define complete-family Hellinger distance between observed environment laws and L2 encoder distance modulo node permutations and coordinatewise circle diffeomorphisms. Under a finite order-m derivative profile, prove the matching inverse modulus Omega_km(eps) asymptotic to eps^((k+1)/(k+m+1)), with the primary C2/Morse exponent 3/4, uniformly over both DAGs, mechanisms, and decoders. Treat CauCA plateau rotations and Varici et al. almost-everywhere exact recovery as occupied. Give a certified Fourier/spline recovery and confidence-set rung. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Multiplying every node-target baseline density and dividing by observational density^(n-1) exactly yields the decoder pushforward of an independent baseline product for any DAG. After coordinate probability-integral gauges this controls determinant error, while within-group ratios control factorization residuals, without losing the Hellinger exponent under two-sided nuisance variation. For bounded radial Hamiltonian twists, angular averaging plus interpolation through the critical hole proves the matching exponent; conditional variance of exp(i T_i) prevents quotient absorption. In the two-node C2/Morse family, exact expansions give representation error h^3 and full-law Hellinger error h^4. Ratio-only strip alternatives yield a worse exponent but incur determinant error and are excluded by the synthetic law. Checks covered anisotropic and oscillatory packets, winding, positivity, flat and coalescing critical regimes, quotient absorption, and current nonlinear/linear recovery literature; no full-modulus collision was found. UNRESOLVED BOTTLENECK: Prove the degenerate incompressible-rigidity inequality for arbitrary bounded C2 torus diffeomorphisms in the two-node Morse model, then extend it uniformly over both nuisance classes. EARLY KILL TEST: Prove or refute the normalized divergence-free C2 inequality using joint-critical and oscillatory-strip packets; any unbounded sequence or need for extra critical-spacing/decoder assumptions pivots the run. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_circle_morse_hmod_frontier.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The proposal promised a matching full-class exponent uniformly over mechanisms and decoders, but only a nonmatching full-class bracket and a sharp restricted radial result were established."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The proposal promised the matching full-class exponent, but the theorem proved only a nonmatching lower/upper bracket."
  - "Equation (8) is essentially the desired strip-to-corner inequality and is asserted after an informal ‘finite recurrence’."
  - "The required effective certified sieve, orbit objective, and explicit calibration were also not supplied."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_oeq_full_incompressible_rigidity.json
  - discovery/solve_tex/solve_oeq_full_incompressible_rigidity.tex
seeds_burned: []
proof_attempt_summary: |
  The run established an exact synthetic-product identity, exact zero-law identification,
  a sharp radial-subclass 3/4 modulus, and a conservative full-class bracket. Its final
  attempt at the promised sharp arbitrary-map result collapsed because the strip-to-corner
  coercivity estimate was restated rather than proved, with nonlinear normalization and
  critical-scale absorption still unjustified; the effective certified statistical sieve
  and orbit calibration also remain open.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 35036174
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 35036174
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# eid_circle_morse_hmod_frontier / v1 — Failed

**Topic.** Sharp full-law recovery modulus at Morse-critical circular interventions. On bounded C^k causal models over T^n with grouped positive single-node perfect interventions, define complete-family Hellinger distance between observed environment laws and L2 encoder distance modulo node permutations and coordinatewise circle diffeomorphisms. Under a finite order-m derivative profile, prove the matching inverse modulus Omega_km(eps) asymptotic to eps^((k+1)/(k+m+1)), with the primary C2/Morse exponent 3/4, uniformly over both DAGs, mechanisms, and decoders. Treat CauCA plateau rotations and Varici et al. almost-everywhere exact recovery as occupied. Give a certified Fourier/spline recovery and confidence-set rung. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Multiplying every node-target baseline density and dividing by observational density^(n-1) exactly yields the decoder pushforward of an independent baseline product for any DAG. After coordinate probability-integral gauges this controls determinant error, while within-group ratios control factorization residuals, without losing the Hellinger exponent under two-sided nuisance variation. For bounded radial Hamiltonian twists, angular averaging plus interpolation through the critical hole proves the matching exponent; conditional variance of exp(i T_i) prevents quotient absorption. In the two-node C2/Morse family, exact expansions give representation error h^3 and full-law Hellinger error h^4. Ratio-only strip alternatives yield a worse exponent but incur determinant error and are excluded by the synthetic law. Checks covered anisotropic and oscillatory packets, winding, positivity, flat and coalescing critical regimes, quotient absorption, and current nonlinear/linear recovery literature; no full-modulus collision was found. UNRESOLVED BOTTLENECK: Prove the degenerate incompressible-rigidity inequality for arbitrary bounded C2 torus diffeomorphisms in the two-node Morse model, then extend it uniformly over both nuisance classes. EARLY KILL TEST: Prove or refute the normalized divergence-free C2 inequality using joint-critical and oscillatory-strip packets; any unbounded sequence or need for extra critical-spacing/decoder assumptions pivots the run. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_circle_morse_hmod_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** terminal:laundering — the final scoped attempt asserted the load-bearing strip-to-corner inequality rather than proving it, leaving the promised sharp full-class modulus unproved.

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

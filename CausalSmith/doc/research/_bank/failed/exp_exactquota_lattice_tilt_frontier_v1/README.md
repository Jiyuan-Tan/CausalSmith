---
qid: exp_exactquota_lattice_tilt_frontier
spec: v1
topic: "Sharp exact-quota finite-population ranking exponents and a solved nonbalanced allocation frontier. Fix equal cluster size n, distinct interior exact quotas, positive fixed welfare gaps, deterministic binary stratified-interference outcomes, exact first-stage arm totals, and uniform within-cluster quota subsets. For empirical cluster-mean policy ranking, prove uniform polynomial-factor upper and matching deterministic-population lower bounds from the exact response-type/arm/outcome integer-table entropy, including zero-error infinite-rate branches. Prove the continuous fixed-allocation branch exponent and boundary-safe primal/dual certificates on explicit compatible rational replication lattices. For n=4, quotas (1,2,3), gaps (1/2,1/2,1), derive the complete three-piece exponent and prove the unique optimizer on A_epsilon is (epsilon,1-2epsilon,epsilon), not balance. Consumer: RCT2 and the Baird--Bohren--McIntosh--Ozler saturation-design calculator. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Two independent derivations obtained the exact factorial table law and its endogenous-population relative entropy, uniform minimax bounds, actual least-favorable populations, rational vertex replication, and feasible-face branch duals. Exact enumeration reproduced all 81,920 witness paths and the 9,299 reversal/8,771 adverse-tie/63,850 correct split. All 256 middle-arm patterns yield the nine-point endpoint envelope; coefficient bounds and explicit populations give transitions 12/25 and 4/5, rates 0.3182570841474064 at balance and 1.4334075753824445 at the optimum, and every-sequence rounding. The thirds-gap counterexample kills unrestricted all-C convergence, and strict convexity kills outer-KKT sufficiency; both are excluded. UNRESOLVED BOTTLENECK: No revised-core theorem step remains; downstream work must prove coverage for a concretely specified simultaneous order confidence set. EARLY KILL TEST: At C=8 and middle-arm count 6, enumerate all 526 feasible welfare-count vectors; the exact maximum endpoint-hit probability must be 37/1306368, attained by counts (1,0,0,0,6,0,0,0,1). STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_exactquota_lattice_tilt_frontier.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "No polynomial-factor ranking exponent bounds, continuous fixed-allocation characterization, explicit n=4 three-piece exponent, transition points, or nonbalanced optimizer were delivered."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The delivered results establish exact schedule inversion, a finite response-table quotient, and atomwise restrictions on deterministic weak-order confidence rules, but these are narrow finite-space inference results rather than the sharp ranking-exponent and allocation-frontier results advertised in the project brief."
  - "No polynomial-factor upper or lower exponent, continuous fixed-allocation characterization, three-piece n=4 exponent, or nonbalanced optimizer is proved in the note."
  - "No honest bounded same-topic repair: restoring fidelity requires the entire exponent/allocation theorem spine; solving oeq:consonant-order-closure only strengthens the substituted object."
reusable_artifacts:
  - discovery/core.json
  - discovery/solve_thm_exact_weak_order_coverage.tex
  - discovery/solve_thm_small_alpha_atom_obstruction.tex
  - discovery/solve_oeq_consonant_order_closure.tex
  - discovery/writeup.tex
seeds_burned: []
proof_attempt_summary: |
  D0 derived a sound finite response-table inversion, an exact deterministic coverage
  characterization, and a sharp low-alpha order-atom obstruction. These results changed
  the paper's kernel: they did not prove the promised ranking-error exponents, matching
  least-favorable constructions, continuous allocation frontier, or explicit n=4
  nonbalanced optimizer. Recovering the accepted topic would require rebuilding the full
  exponent/allocation theorem spine, while the remaining consonant-closure question only
  strengthens the substituted confidence-set problem.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 13202489
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 13202489
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# exp_exactquota_lattice_tilt_frontier / v1 — Failed

**Topic.** Sharp exact-quota finite-population ranking exponents and a solved nonbalanced allocation frontier. Fix equal cluster size n, distinct interior exact quotas, positive fixed welfare gaps, deterministic binary stratified-interference outcomes, exact first-stage arm totals, and uniform within-cluster quota subsets. For empirical cluster-mean policy ranking, prove uniform polynomial-factor upper and matching deterministic-population lower bounds from the exact response-type/arm/outcome integer-table entropy, including zero-error infinite-rate branches. Prove the continuous fixed-allocation branch exponent and boundary-safe primal/dual certificates on explicit compatible rational replication lattices. For n=4, quotas (1,2,3), gaps (1/2,1/2,1), derive the complete three-piece exponent and prove the unique optimizer on A_epsilon is (epsilon,1-2epsilon,epsilon), not balance. Consumer: RCT2 and the Baird--Bohren--McIntosh--Ozler saturation-design calculator. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Two independent derivations obtained the exact factorial table law and its endogenous-population relative entropy, uniform minimax bounds, actual least-favorable populations, rational vertex replication, and feasible-face branch duals. Exact enumeration reproduced all 81,920 witness paths and the 9,299 reversal/8,771 adverse-tie/63,850 correct split. All 256 middle-arm patterns yield the nine-point endpoint envelope; coefficient bounds and explicit populations give transitions 12/25 and 4/5, rates 0.3182570841474064 at balance and 1.4334075753824445 at the optimum, and every-sequence rounding. The thirds-gap counterexample kills unrestricted all-C convergence, and strict convexity kills outer-KKT sufficiency; both are excluded. UNRESOLVED BOTTLENECK: No revised-core theorem step remains; downstream work must prove coverage for a concretely specified simultaneous order confidence set. EARLY KILL TEST: At C=8 and middle-arm count 6, enumerate all 526 feasible welfare-count vectors; the exact maximum endpoint-hit probability must be 37/1306368, attained by counts (1,0,0,0,6,0,0,0,1). STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_exactquota_lattice_tilt_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** TERMINAL:LAUNDERING — the delivered confidence-set kernel substitutes for the promised ranking-exponent and nonbalanced-allocation frontier; no honest bounded D0 repair exists.

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
